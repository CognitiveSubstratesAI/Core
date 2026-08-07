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
# grammar's `Atom` parser (`Interpreter.parse_from`), which reads into typed atoms rather than strings.

# ── top-level form splitter: paren-depth aware, `!`-prefix aware, `;`-comment aware ──
function mm2_split_forms(program::AbstractString)::Vector{Tuple{Bool, String}}
    forms = Tuple{Bool, String}[]
    s = collect(program); n = length(s); i = 1
    while i <= n
        while i <= n && (isspace(s[i]) || s[i] == ';')
            if s[i] == ';'
                while i <= n && s[i] != '\n'; i += 1; end
            else
                i += 1
            end
        end
        i > n && break
        bang = false
        if s[i] == '!'
            bang = true; i += 1
            while i <= n && isspace(s[i]); i += 1; end
        end
        i > n && break
        start = i
        if s[i] == '('
            depth = 0; instr = false; esc = false        # string-aware: (/)/whitespace inside "…" are literal
            while i <= n
                c = s[i]
                if instr
                    esc ? (esc = false) : c == '\\' ? (esc = true) : c == '"' && (instr = false)
                elseif c == '"'; instr = true
                elseif c == '('; depth += 1
                elseif c == ')'; depth -= 1
                end
                i += 1
                (depth == 0 && !instr) && break
            end
        else
            while i <= n && !isspace(s[i]); i += 1; end
        end
        push!(forms, (bang, String(s[start:i-1])))
    end
    forms
end

"Head symbol of a top-level form (`\"exec\"` for an exec-rule)."
function mm2_head(form::AbstractString)::String
    t = lstrip(form)
    startswith(t, "(") || return strip(t)
    inner = SubString(t, nextind(t, firstindex(t)))
    j = findfirst(c -> isspace(c) || c == '(' || c == ')', inner)
    j === nothing ? strip(inner) : strip(SubString(inner, firstindex(inner), prevind(inner, j)))
end

"Top-level argument forms of a paren expr, e.g. `(match S P T)` → [\"match\",\"S\",\"P\",\"T\"]."
function mm2_expr_args(form::AbstractString)::Vector{String}
    t = strip(form)
    (startswith(t, "(") && endswith(t, ")")) || error("mm2_expr_args: not an expr: $form")
    inner = SubString(t, nextind(t, firstindex(t)), prevind(t, lastindex(t)))
    args = String[]; depth = 0; buf = IOBuffer()
    instr = false; esc = false                            # string-aware: (/)/whitespace inside "…" are literal
    for c in inner
        if instr; print(buf, c)
            esc ? (esc = false) : c == '\\' ? (esc = true) : c == '"' && (instr = false)
        elseif c == '"'; instr = true; print(buf, c)
        elseif c == '('; depth += 1; print(buf, c)
        elseif c == ')'; depth -= 1; print(buf, c)
        elseif isspace(c) && depth == 0
            s = String(take!(buf)); isempty(s) || push!(args, s)
        else; print(buf, c); end
    end
    s = String(take!(buf)); isempty(s) || push!(args, s)
    args
end
