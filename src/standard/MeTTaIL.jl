# MeTTaIL.jl — MeTTa-IL rewrite-reduction → MM2 → MORK (F1R3FLY layered track).
#
# RE-GROUNDED 2026-06-19 in the ACTUAL upstream MeTTa-IL (F1R3FLY/MeTTaIL `GSLT/.module` +
# mettail-rust `language!`), NOT the scalable-infra paper §9.1 `def/match/emit` sketch (that was a
# mislabel — corrected). The real MeTTa-IL: a Theory has `Terms` (BNF grammar), `Equations`,
# `Rewrites`, `Replacements`, with theory composition. Its EXECUTABLE reduction relation is the
# **Rewrites** — `Name : LHS ~> RHS` (base) and congruence `let Src ~> Tgt in (Ctx Src) ~> (Ctx Tgt)`
# (same structure as mettail-rust's `Name . | M0~>M1 |- LHS ~> RHS`).
#
# This lane lowers the BASE rewrites `(~> LHS RHS)` → MM2 `(exec 0 (, LHS) (, RHS))`, run on the native
# MORK CoreSpace via the router's machinery (no surface→IR rewrite, no FFI), bisimulation-gated ≡ the
# interpreter-spec. RECURSIVE closure → `saturate=true` (KBSaturation to fixpoint). CONGRUENCE / calculus
# reduction → `metta_il_normalize` (subterm rewriting). NOT yet covered: equations-as-rewrite orientation.
# The GSLT theory algebra (Terms/Equations/Replacements/composition/parameterization) lives in GSLT.jl.
#
# Two distinct `~>` execution modes (pick by workload): metta_il_run! = additive forward-derivation
# (relational/forward-derivation — transitive closure, deductive queries); metta_il_normalize = term reduction with
# congruence (calculi — rho/lambda, equational reduction). Same surface, different semantics.

"Lower one MeTTa-IL base rewrite `(~> LHS RHS)` (GSLT `Name : LHS ~> RHS`) to an MM2 `(exec …)` rule.
LHS may be a single pattern or a conjunction `(, P1 P2 …)`."
function metta_il_lower_rewrite(rw::AbstractString)::String
    a = mm2_expr_args(rw)
    (length(a) == 3 && a[1] == "~>") ||
        error("metta_il_lower_rewrite: expected (~> LHS RHS), got: $rw")
    lhs, rhs = a[2], a[3]
    src = startswith(lstrip(lhs), "(,") ? lhs : "(, $lhs)"
    "(exec 0 $src (, $rhs))"
end

"""
    _il_assert_all_rewrites(program, who)

Raise unless EVERY form in `program` is a `(~> LHS RHS)` base rewrite.

This lane's contract is "program = rewrites, facts arrive via the `data` argument". Nothing enforced
it, and every lowering entry filtered with `if !bang && mm2_head(f) == "~>"`, so any other form was
DROPPED WITHOUT A WORD. That is reachable from `mc_run`, which selects this lane on the mere PRESENCE
of a `~>` head (DualTrack.jl:109) and will therefore hand it mixed programs that violate the contract.

Measured before this guard existed — `(~> (p \$x) (q \$x))` + `(= (q A) B)` + `(p A)` ran as lane
`:rewrite`, lowered ONLY the `~>` form, returned `String[]`, and left the space EMPTY: the rule and
the ground fact both vanished silently. A wrong answer with no diagnostic is the worst failure shape
we have ([[feedback_port_defect_taxonomy]] silent-narrowing), so the drop is now loud.

⚠️ This does NOT make the lane accept `(=)`. Whether MeTTa-IL SHOULD consume `(=)` — i.e. be the
§3.4 compilation bridge rather than a `~>`-only side lane — is an open architectural question. This
guard only guarantees we find out by an error instead of by a missing answer.
"""
function _il_assert_all_rewrites(program::AbstractString, who::AbstractString)
    bad = String[]
    bangs = String[]
    for (bang, f) in mm2_split_forms(program)
        if bang
            push!(bangs, strip(f))
        elseif mm2_head(f) != "~>"
            push!(bad, strip(f))
        end
    end
    (isempty(bad) && isempty(bangs)) && return nothing
    msg = "$who: this lane lowers ONLY `(~> LHS RHS)` base rewrites, but the program contains " *
          "forms it would silently discard.\n"
    isempty(bad) || (msg *= "  unsupported forms ($(length(bad))): " *
                            join(first(bad, 5), "  ") * (length(bad) > 5 ? "  …" : "") * "\n")
    isempty(bangs) || (msg *= "  `!` directives ($(length(bangs))): " *
                              join(first(bangs, 5), "  ") * (length(bangs) > 5 ? "  …" : "") * "\n")
    msg *= "  → ground FACTS belong in the `data` argument, not the program.\n" *
           "  → `(=)` rules are not lowered by this lane; run them on the :direct lane (mc_run " *
           "mode=:direct) or express them as `(~> LHS RHS)`."
    error(msg)
end

"Lower a MeTTa-IL program (its `(~> LHS RHS)` rewrites) to MM2 exec rules.
RAISES on any non-`~>` form rather than dropping it — see `_il_assert_all_rewrites`."
function metta_il_lower(program::AbstractString)::String
    _il_assert_all_rewrites(program, "metta_il_lower")
    join([metta_il_lower_rewrite(strip(f)) for (bang, f) in mm2_split_forms(program)
          if !bang && mm2_head(f) == "~>"], "\n")
end

"Lower a MeTTa-IL program's rewrites to KBSaturation forward rules `(==> LHS RHS)` (for recursive
closure). `(~> LHS RHS)` and `(==> BODY HEAD)` are the same forward-derivation; `==>` runs to fixpoint.
RAISES on any non-`~>` form rather than dropping it — see `_il_assert_all_rewrites`."
function metta_il_lower_saturation(program::AbstractString)::String
    _il_assert_all_rewrites(program, "metta_il_lower_saturation")
    join(["(==> $(mm2_expr_args(f)[2]) $(mm2_expr_args(f)[3]))"
          for (bang, f) in mm2_split_forms(program) if !bang && mm2_head(f) == "~>"], "\n")
end

"""
    metta_il_run!(cs::CoreSpace, data, program; steps=1_000_000, saturate=false) -> Vector{String}

Run a MeTTa-IL program's rewrites over `data` on the native MORK `cs`, returning the rewritten atoms
(by each RHS head). Two engines:
  * `saturate=false` (default): lower `(~> LHS RHS)` → MM2 `(exec …)`, step the calculus ONE generation.
  * `saturate=true`: lower → KBSaturation rules `(==> LHS RHS)`, run `sc_execute!` to FIXPOINT — needed
    for RECURSIVE rewrites (a rewrite whose RHS head also appears in a body), e.g. transitive closure.
"""
function metta_il_run!(cs::CoreSpace, data::AbstractString, program::AbstractString;
                       steps::Int = 1_000_000, saturate::Bool = false,
                       use_magic_sets::Bool = false, magic_query::AbstractString = "", magic_bound::Int = 0)
    # Guard FIRST — before `data` touches the space. The lowering entries below also check, but by
    # then we would have mutated `cs` and then thrown, leaving a half-loaded space behind.
    _il_assert_all_rewrites(program, "metta_il_run!")
    isempty(strip(data)) || space_add_all_sexpr!(cs.inner, data)
    if saturate
        rules = metta_il_lower_saturation(program)
        isempty(rules) && return String[]
        # opt-in magic-sets goal-direction (same shared SCOptions stage the Direct lane reaches)
        sc_execute!(cs, rules; opts = SCOptions(saturate = true, use_magic_sets = use_magic_sets,
            magic_query = String(magic_query), magic_bound = magic_bound))
    else
        exec = metta_il_lower(program)
        isempty(exec) && return String[]
        space_add_all_sexpr!(cs.inner, exec)
        space_metta_calculus!(cs.inner, steps)                      # single generation
    end
    heads = Set{String}()
    for (bang, f) in mm2_split_forms(program)
        (bang || mm2_head(f) != "~>") && continue
        push!(heads, mm2_head(mm2_expr_args(f)[3]))   # RHS head
    end
    sort(unique(String[strip(l) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                        if mm2_head(strip(l)) in heads]))
end

# --- Congruence: calculus reduction via subterm rewriting --------------------------------------------
# GSLT/mettail-rust `~>` for CALCULI is term REDUCTION WITH CONGRUENCE (a redex reduces inside any
# context), NOT the additive forward-derivation of metta_il_run!. Neither existing engine gives it free:
# the relational lane is additive; the interpreter does NOT reduce constructor/undefined-head subterms
# (verified — `(and (not T) Y)` stays unreduced). So congruence is BUILT here as a subterm-rewriting
# normalizer: rewrite any subterm matching a base-rewrite LHS, innermost, to fixpoint. The subterm
# descent IS the congruence — mettail-rust spells it out as explicit `rw_cat` rules ONLY because
# Ascent is relational and cannot descend into subterms; on a term engine it is structural.

# PARSE-HOISTED. The rules are FIXED for a whole normalization, and the previous form called the
# STRING method `mork_rule_rewrite(rule::AbstractString, data::AbstractString)` — which parses BOTH
# arguments — once per (subterm × rule). PROFILED (2026-07-23, `(d (Mul x (Mul x x)))`):
#   398 `sexpr_to_expr` calls for ONE normalization; 83% of samples inside the string
#   `mork_rule_rewrite`, 54% directly in `sexpr_to_expr`/`sexpr_parse!`; 1.03 ms, 0.43 MiB, gc 0%.
# So roughly half the parses were re-parsing the same four rule strings. Now: rules are parsed ONCE
# by the caller, and each subterm is parsed ONCE instead of once per rule — parse count drops from
# (subterms × rules × 2) to (subterms + rules). Pure implementation change: same innermost-to-fixpoint
# congruence, same results (guarded by the test_mettail/test_gslt congruence tests + JeTTa's own
# Derivative.metta oracle, which both lanes already reproduce byte-for-byte).
function _normalize_subterm(rules::Vector{MORK.Expr}, term::AbstractString)::String
    term = strip(term)
    if startswith(term, "(")                          # compound: normalize children first (← congruence)
        term = "(" * join([_normalize_subterm(rules, a) for a in mm2_expr_args(term)], " ") * ")"
    end
    te = MORK.sexpr_to_expr(String(term))             # parse the TERM once, not once per rule
    for rule in rules                                 # then a top-level reduction; renormalize on success
        r = mork_rule_rewrite(rule, te)               # Expr method — no parsing of either side
        r === nothing && continue
        rs = strip(MORK.expr_serialize(r.buf))
        rs != term && return _normalize_subterm(rules, rs)
    end
    term
end

"""
    metta_il_normalize(program, term) -> String

Reduce `term` to normal form under a MeTTa-IL calculus (the program's base rewrites `(~> LHS RHS)` as
reduction rules), rewriting subterms innermost to fixpoint. Congruence (reduction inside contexts) is
the subterm traversal — so GSLT/mettail-rust explicit congruence rules (`let Src ~> Tgt in …`), needed
only by relational backends, are unnecessary here.
"""
function metta_il_normalize(program::AbstractString, term::AbstractString)::String
    # Same silent-drop hole as the lowering entries: a non-`~>` form was filtered out below without a
    # word, so a rule the caller believed was in the calculus simply would not fire and the term would
    # come back under-reduced — indistinguishable from "already in normal form".
    _il_assert_all_rewrites(program, "metta_il_normalize")
    # Parse each `(= LHS RHS)` rule to a MORK.Expr ONCE for the whole normalization (see the
    # profile note on `_normalize_subterm`). Head and body must stay in ONE parsed expr so they
    # share a variable namespace — MORK vars are POSITIONAL (MorkBridge.jl CRUX); parsing them
    # separately silently reorders indices, e.g. `(q $y $x)` over `(p a b)` yielding `(q a b)`.
    rules = MORK.Expr[MORK.sexpr_to_expr("(= $(mm2_expr_args(f)[2]) $(mm2_expr_args(f)[3]))")
                      for (bang, f) in mm2_split_forms(program) if !bang && mm2_head(f) == "~>"]
    _normalize_subterm(rules, term)
end

# --- def/match/emit pipeline surface (scalable-infra §9.1, lowered to MM2 per §9.2) ------------------
# The paper's higher-level MeTTa-IL surface for STAGED relational pipelines (pattern-miners, agent
# loops). A `def` is a named stage; `match PAT…` binds inputs (conjunction); `when` guards; `emit`
# produces the next stage's facts (multiple allowed). The paper's own §9.2 lowering is `defreact`/
# `(exec PRIORITY (, PATS) [:guard G] (, EMITS))` — so each def becomes an exec whose PRIORITY is its
# stage order (the pipeline sequencing). This is sugar over the relational (additive) derivation mode
# (metta_il_run!), NOT term reduction — but it adds named, priority-ordered staging + multiple emits.

# parse `(def NAME (params) (match PAT… [(emit …)|(when G (emit …)…)]…))` → (pats, emits, guards)
function _parse_def_match(def::AbstractString)
    a = mm2_expr_args(def)
    (a[1] == "def" && length(a) >= 4) ||
        error("def: expected (def NAME (params) (match …)), got: $def")
    m = mm2_expr_args(a[4])
    m[1] == "match" || error("def body must be (match …), got '$(m[1])'")
    pats = String[]; emits = String[]; guards = String[]
    for arg in m[2:end]
        h = mm2_head(arg)
        if h == "emit"
            push!(emits, mm2_expr_args(arg)[2])
        elseif h == "when"                              # (when GUARD (emit …)…)
            wa = mm2_expr_args(arg)
            push!(guards, wa[2])
            for e in wa[3:end]
                mm2_head(e) == "emit" && push!(emits, mm2_expr_args(e)[2])
            end
        else
            push!(pats, arg)                            # a match pattern
        end
    end
    (pats = pats, emits = emits, guards = guards)
end

"Lower one `def/match/emit` stage to MM2 `(exec PRIORITY (, PATS GUARDS) (, EMITS))` (§9.2 `defreact`)."
function metta_il_lower_def(def::AbstractString, priority::Integer = 0)::String
    p = _parse_def_match(def)
    isempty(p.emits) && error("metta_il_lower_def: (match …) has no (emit …)")
    "(exec $priority (, $(join(vcat(p.pats, p.guards), " "))) (, $(join(p.emits, " "))))"
end

"Lower a `def/match/emit` pipeline → MM2 exec program; each def's PRIORITY is its stage order."
metta_il_lower_pipeline(program::AbstractString)::String =
    join([metta_il_lower_def(strip(f), i)
          for (i, (bang, f)) in enumerate(mm2_split_forms(program)) if !bang && mm2_head(f) == "def"],
         "\n")

_pipeline_emit_heads(program) = Set{String}(
    mm2_head(e) for (bang, f) in mm2_split_forms(program) if !bang && mm2_head(f) == "def"
                for e in _parse_def_match(strip(f)).emits)

"""
    metta_il_run_pipeline!(cs, data, program; steps=1_000_000) -> Vector{String}

Run a `def/match/emit` pipeline (§9.1) over `data`: lower each stage to a priority-ordered MM2 exec
rule (§9.2), step the calculus, return the emitted atoms (by every stage's emit head).
"""
function metta_il_run_pipeline!(cs::CoreSpace, data::AbstractString, program::AbstractString;
                                steps::Int = 1_000_000)
    isempty(strip(data)) || space_add_all_sexpr!(cs.inner, data)
    exec = metta_il_lower_pipeline(program)
    isempty(exec) && return String[]
    space_add_all_sexpr!(cs.inner, exec)
    space_metta_calculus!(cs.inner, steps)
    heads = _pipeline_emit_heads(program)
    sort(unique(String[strip(l) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                        if mm2_head(strip(l)) in heads]))
end
