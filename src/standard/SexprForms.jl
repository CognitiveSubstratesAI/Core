# SexprForms.jl — the LANE-NEUTRAL s-expression form parsers.
#
# ─── WHY THESE LIVE HERE AND NOT IN MM2Router ────────────────────────────────────────────────────
# `mm2_split_forms` / `mm2_head` / `mm2_expr_args` are the ONLY definitions of these functions in the
# tree, and they are pure string parsing — no MM2 semantics, no lowering, no MORK. They happened to be
# written inside `MM2Router.jl`, which made every consumer of them a consumer of the router:
#
#     MeTTaIL.jl   mm2_head x14 · mm2_expr_args x12 · mm2_split_forms x7
#     GSLT.jl      parses `(theory …)` with the same three
#     DualTrack.jl lane dispatch reads heads with them
#     PatternMiner.jl
#     -> ~56 call sites; `MeTTaCore.jl` includes MM2Router BEFORE all four.
#
# So "disconnect MM2Router" was not a sequencing problem, it was a contradiction: MeTTa-IL is a CLIENT
# of MM2Router, not an alternative to it (10-agent audit, 2026-08-07). Moving the parsers out is the
# FORCED first step — after it, what remains in MM2Router is the direct surface-`(=)`→MM2 lowering,
# which is the arrow Figure 2 does not have and the only part anyone wants gone.
#
# NAMES ARE UNCHANGED ON PURPOSE. These are spliced into `MeTTaCore` by `include`, exactly as they were
# from `MM2Router.jl`, so all ~56 call sites keep working untouched and this commit is provably
# behaviour-neutral. Renaming them to `sexpr_*` is a separate, later, mechanical change — doing both at
# once would make a regression impossible to attribute.
#
# ⚠️ NOT MM2-SPECIFIC despite the prefix: `GSLT.jl` parses `(theory …)` and `MeTTaIL.jl` parses
# `(~> LHS RHS)` with these. They are the tree's s-expression reader for TEXT forms — distinct from the
# grammar's `Atom` parser (`Eval.parse_from`), which reads into typed atoms rather than strings.

# ── top-level form splitter: paren-depth aware, `!`-prefix aware, `;`-comment aware ──
function mm2_split_forms(program::AbstractString)::Vector{Tuple{Bool, String}}
    forms = Tuple{Bool, String}[]
    s = collect(program)
    n = length(s)
    i = 1
    while i <= n
        while i <= n && (isspace(s[i]) || s[i] == ';')
            if s[i] == ';'
                while i <= n && s[i] != '\n'
                    i += 1
                end
            else
                i += 1
            end
        end
        i > n && break
        bang = false
        if s[i] == '!'
            bang = true
            i += 1
            while i <= n && isspace(s[i])
                i += 1
            end
        end
        i > n && break
        start = i
        if s[i] == '('
            depth = 0
            instr = false
            esc = false        # string-aware: (/)/whitespace inside "…" are literal
            while i <= n
                c = s[i]
                if instr
                    if esc
                        (esc = false)
                    elseif c == '\\'
                        (esc = true)
                    else
                        c == '"' && (instr = false)
                    end
                elseif c == '"'
                    instr = true
                elseif c == '('
                    depth += 1
                elseif c == ')'
                    depth -= 1
                end
                i += 1
                (depth == 0 && !instr) && break
            end
        else
            while i <= n && !isspace(s[i])
                i += 1
            end
        end
        push!(forms, (bang, String(s[start:(i - 1)])))
    end
    forms
end

"Head symbol of a top-level form (`\"exec\"` for an exec-rule)."
function mm2_head(form::AbstractString)::String
    t = lstrip(form)
    startswith(t, "(") || return strip(t)
    inner = SubString(t, nextind(t, firstindex(t)))
    j = findfirst(c -> isspace(c) || c == '(' || c == ')', inner)
    if j === nothing
        strip(inner)
    else
        strip(SubString(inner, firstindex(inner), prevind(inner, j)))
    end
end

"Top-level argument forms of a paren expr, e.g. `(match S P T)` → [\"match\",\"S\",\"P\",\"T\"]."
function mm2_expr_args(form::AbstractString)::Vector{String}
    t = strip(form)
    (startswith(t, "(") && endswith(t, ")")) || error("mm2_expr_args: not an expr: $form")
    inner = SubString(t, nextind(t, firstindex(t)), prevind(t, lastindex(t)))
    args = String[]
    depth = 0
    buf = IOBuffer()
    instr = false
    esc = false                            # string-aware: (/)/whitespace inside "…" are literal
    for c in inner
        if instr
            print(buf, c)
            if esc
                (esc = false)
            elseif c == '\\'
                (esc = true)
            else
                c == '"' && (instr = false)
            end
        elseif c == '"'
            instr = true
            print(buf, c)
        elseif c == '('
            depth += 1
            print(buf, c)
        elseif c == ')'
            depth -= 1
            print(buf, c)
        elseif isspace(c) && depth == 0
            s = String(take!(buf))
            isempty(s) || push!(args, s)
        else
            print(buf, c)
        end
    end
    s = String(take!(buf))
    isempty(s) || push!(args, s)
    args
end

# ── program regions: the sequential-effects partition (MeTTa Invariant 1) ────────────────────────
# `metta_language_spec.md` §7 Invariant 1: a `!`-prefixed form EVALUATES and returns; a BARE form is
# ADDED to the atomspace; and EFFECTS ARE SEQUENTIAL — form N observes form N−1's mutations. Every
# lane in this tree violates that by construction, because each lane entry takes the program as ONE
# string and processes it whole:
#
#   mc_run :direct    → mm2_route!(cs, program) · mm2_zam_answers(program, …) · _mc_fallback_eval(…, program, …)
#   mc_run :direct/sc → sc_execute!(cs, join(keep, "\n"))
#   mc_run :rewrite   → metta_il_lower(program)      — one lowering, one calculus generation
#   mc_run :pipeline  → metta_il_run_pipeline!(cs, data, program)
#
# MEASURED 2026-08-08 on the compiled lane:
#
#     (= (f) a)  !(f)  (= (f) b)  !(f)
#     oracle    →  ["a"]      then  ["a","b"]
#     compiled  →  ["a","b"]  and   ["a","b"]      ← the FIRST query answered with a LATER rule
#
# The `:rewrite` lane does not exhibit it only because `_il_assert_all_rewrites` REFUSES any program
# containing a bang (`MeTTaIL.jl:50`) — that is absent capability, not safety. It inherits the defect
# the day the compiler's emitter feeds it bang-bearing programs. Which is why this partition is
# LANE-NEUTRAL and lives HERE and not in `DualTrack.jl`, whose direct-lowering arrow is due for
# deletion: the doomed lane is where the defect is visible today, the surviving lane is where it
# lands tomorrow, and the invariant outlives both.
#
# ─── WHAT A REGION IS ────────────────────────────────────────────────────────────────────────────
# A maximal span over which the atomspace does not change under its queries' feet. `defs` are the
# definitional forms INTRODUCED by this region; `queries` are answered against the accumulated defs
# of this region AND every prior one. Regions are INCREMENTAL, not self-contained — a driver applies
# `defs`, answers `queries`, keeps the space, and moves on.
#
# PREFIX-EXACT means BOTH directions: on the program above, region 1 must answer `["a"]` and region 2
# must answer `["a","b"]`. Returning `["a"]` for the second is as wrong as `["a","b"]` for the first.
#
# DEGENERACY: a program whose definitions all precede its queries yields exactly ONE region, so the
# common case is byte-identical to the un-staged path and costs nothing.
#
# This file stays SEMANTICS-FREE (see the header): the may-mutate predicate is a PARAMETER, because
# only the caller knows the rule set and the grounded registry.
struct ProgramRegion
    defs::Vector{String}      # definitional (non-`!`) forms introduced in this region, in order
    queries::Vector{String}   # `!` bodies, bang stripped, answered against all defs up to and including this region
end

"""
    split_program_regions(program, may_mutate) -> Vector{ProgramRegion}

Partition `program` into churn-free regions so that each query is answered against the rule set which
TEXTUALLY PRECEDES it, per MeTTa Invariant 1.

`may_mutate(form::AbstractString)::Bool` is asked of every `!` body; `true` closes the region after
that query so its mutation is visible downstream. It must be FAIL-SAFE — an unclassifiable head has
to answer `true`. Over-reporting only costs regions; under-reporting silently restores the defect.

Regions are INCREMENTAL: apply `defs`, answer `queries`, keep the space, move on.
"""
function split_program_regions(
    program::AbstractString, may_mutate::F
)::Vector{ProgramRegion} where {F}
    regions = ProgramRegion[]
    defs = String[]
    queries = String[]
    for (bang, form) in mm2_split_forms(program)
        if !bang
            if !isempty(queries)      # a definition AFTER queries ⇒ that prefix is closed
                push!(regions, ProgramRegion(defs, queries))
                defs = String[]
                queries = String[]   # REBIND, never `empty!` — the pushed region aliases these
            end
            push!(defs, form)
        else
            push!(queries, form)
            if may_mutate(form)       # the query itself changes the space ⇒ nothing after it shares this prefix
                push!(regions, ProgramRegion(defs, queries))
                defs = String[]
                queries = String[]
            end
        end
    end
    (isempty(defs) && isempty(queries)) || push!(regions, ProgramRegion(defs, queries))
    regions
end

"Render a region back to program text — `defs` in order, then each query re-prefixed with `!`."
function region_program(r::ProgramRegion)::String
    io = IOBuffer()
    for d in r.defs
        println(io, d)
    end
    for q in r.queries
        println(io, "!", q)
    end
    String(take!(io))
end
