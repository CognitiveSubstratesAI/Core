"""
Eval — MeTTa interpreter for Core.

Evaluates MeTTa expressions against a CoreSpace using:
  1. GROUNDED_REGISTRY — direct Julia function dispatch
  2. Rule lookup — (= head body) rewriting
  3. MORK exec atoms — space_metta_calculus! for MM2 expressions
  4. Special forms — match, let, if, collapse, superpose
"""

# Global default space (lazily initialised)
const _DEFAULT_SPACE = Ref{CoreSpace}()
function default_space()::CoreSpace
    isassigned(_DEFAULT_SPACE) || (_DEFAULT_SPACE[] = new_core_space())
    _DEFAULT_SPACE[]
end

# ── Evaluator depth bound ─────────────────────────────────────────────────────
# Per MeTTa spec, divergent recursion should return `(Error <expr> StackOverflow)`
# rather than crashing the host evaluator. Previously PRIMUS threw a Julia
# StackOverflowError on divergent input (factorial-with-no-base-case under
# streaming, badly written user rules, etc.), which takes down the whole
# eval loop and is unsafe in any self-modifying runtime that generates and
# evaluates its own atoms.
#
# Two protections in layers:
#  1. Soft counter bound (`_EVAL_DEPTH_BOUND`) catches divergence early —
#     1000 MeTTa levels is well within Julia's default stack and gives
#     terminating-but-deeply-nested programs plenty of room.
#  2. StackOverflowError catch is a backstop for cases where (a) the bound
#     is set too high, (b) a grounded function or unify call adds extra
#     Julia frames per MeTTa level, or (c) Julia is launched with a
#     reduced stack size. The host loop survives regardless.
const _EVAL_DEPTH_BOUND = 1_000
const _EVAL_DEPTH = Ref{Int}(0)

"""
    eval_metta(expr, space=default_space()) → Any

Evaluate a MeTTa expression (Julia value) against a CoreSpace.
Returns the reduced result or the expression itself if no rule fires.

Bounded by `_EVAL_DEPTH_BOUND` (soft) and a Julia `StackOverflowError`
catch (hard backstop). On either, returns the spec-conformant
`(Error <expr> StackOverflow)` atom instead of crashing the host.
"""
function eval_metta(@nospecialize(expr), space::CoreSpace = default_space())::Any
    _EVAL_DEPTH[] >= _EVAL_DEPTH_BOUND && return Any[Symbol("Error"), expr, Symbol("StackOverflow")]
    _EVAL_DEPTH[] += 1
    try
        return _eval_metta_bounded(expr, space)
    catch e
        e isa StackOverflowError && return Any[Symbol("Error"), expr, Symbol("StackOverflow")]
        rethrow(e)
    finally
        _EVAL_DEPTH[] -= 1
    end
end

function _eval_metta_bounded(@nospecialize(expr), space::CoreSpace)::Any
    # Variable — return as-is (bindings handled by caller)
    expr isa Symbol && startswith(string(expr), "\$") && return expr

    # Grounded literal (number, bool)
    (expr isa Number || expr isa Bool) && return expr

    # Symbol — check if it's a 0-arg rule head
    if expr isa Symbol
        rules = core_rules(space, expr)
        !isempty(rules) && return eval_metta(rules[1][2], space)
        return expr
    end

    # Non-expression — return as-is
    !(expr isa Vector) && return expr
    isempty(expr) && return expr

    head = expr[1]
    args = expr[2:end]

    # ── Special forms ─────────────────────────────────────────────────────────
    # Per MeTTa spec §Minimal MeTTa Instructions and cross-verified against
    # Mettatron eval/mod.rs, CeTTa grounded.c, hyperon-experimental interpreter.rs
    # PRIMUS_Core/interpreter/SpecialForms.jl (adopted + stripped of MeTTaTerm)

    head === :match && return _eval_match(args, space)
    head === Symbol("match") && return _eval_match(args, space)
    head === :let && return _eval_let(args, space)
    head === Symbol("let*") && return _eval_let_star(args, space)
    head === :if && return _eval_if(args, space)
    head === :collapse && return _eval_collapse(args, space)
    head === :superpose && return _eval_superpose(args, space)
    head === :case && return _eval_case(args, space)
    head === :switch && return _eval_case(args, space)
    head === :chain && return _eval_chain(args, space)
    head === :function && return _eval_function(args, space)
    head === :return && return _eval_return(args, space)
    head === :eval && return _eval_eval(args, space)
    head === :evalc && return _eval_eval(args, space)   # context ignored for now
    head === :unify && return _eval_unify(args, space)
    head === :quote && return _eval_quote(args)
    head === :unquote && return _eval_unquote(args, space)
    head === :empty && return nothing
    head === Symbol("noreduce-eq") && return _eval_noreduce_eq(args)  # no eval of args
    head === :noeval && return isempty(args) ? nothing : args[1]  # return unevaluated
    # Error is a constructor — args are NOT evaluated (prevents assertEqual infinite recursion)
    head === :Error && return vcat([Symbol("Error")], args)
    head === Symbol("Error") && return vcat([Symbol("Error")], args)
    head === :do && return _eval_do(args, space)
    head === :begin && return _eval_do(args, space)
    head === Symbol("import!") && return _eval_import!(args, space)
    head === Symbol("git-import!") && return _eval_git_import!(args, space)
    head === Symbol("bind!") && return _eval_bind!(args, space)
    head === Symbol("with-space") && return _eval_with_space(args, space)
    head === Symbol("add-atom") && return _eval_add_atom(args, space)
    head === Symbol("remove-atom") && return _eval_remove_atom(args, space)
    # ECAN bulk ops — Julia fast path for trie-wide STI/LTI updates.
    # Pure-MeTTa equivalents in t1_core_logic.metta become unreachable once
    # these special forms take dispatch precedence (head match happens before
    # rule lookup).  See benchmark in packages/ECAN/examples/Stability.metta.
    head === Symbol("decimate-importance!") && return _eval_decimate_importance!(args, space)
    head === Symbol("normalize-attention!") && return _eval_normalize_attention!(args, space)
    # exec atoms — add to MORK space and run calculus (AUSink/CountSink/HeadSink)
    head === :exec && return _eval_exec_atom(expr, space)
    head === Symbol("get-atoms") && return core_atoms(space)
    head === Symbol("new-space") && return new_core_space()
    head === Symbol("get-type-space") && return _eval_get_type_space(args, space)
    # get-type is dispatched as a special form (rather than the grounded
    # version registered in Primitives.jl) so it can consult the space for
    # `(: atom type)` declarations BEFORE falling back to structural inference.
    # Closes the three-oracle disagreement (get-type vs get-type-space vs
    # type-cast) for the common single-declaration case. Multi-typed atoms
    # still return only the first declared type — the multi-valued behavior
    # is the step-4 (streaming) consumer-migration item per resume notes.
    head === Symbol("get-type") && return _eval_get_type(args, space)
    # type-cast is dispatched as a special form (rather than the grounded
    # structural-only version in Primitives.jl) so it can read declared
    # types from the space and loop over them per the spec's type_cast
    # algorithm. First-match-success returns the atom; if no declared
    # type matches, accumulates BadType errors per non-matching type.
    head === Symbol("type-cast") && return _eval_type_cast(args, space)
    head === Symbol("add-reduct") && return _eval_add_reduct(args, space)
    head === Symbol("for-each-in-atom") && return _eval_for_each(args, space)
    # Higher-order atom ops — body arg must NOT be pre-evaluated (special forms)
    head === Symbol("foldl-atom") && return _eval_foldl_atom(args, space)
    head === Symbol("map-atom") && return _eval_map_atom(args, space)
    head === Symbol("filter-atom") && return _eval_filter_atom(args, space)

    # ── Grounded dispatch ─────────────────────────────────────────────────────
    if head isa Symbol && is_grounded(string(head))
        evaled_args = [eval_metta(a, space) for a in args]
        str_args = to_sexpr_atom.(evaled_args)   # quote-wraps String literals so primitives can tell "hi" from :hi
        raw = try
            GROUNDED_REGISTRY[string(head)](str_args)
        catch e
            ; @warn "grounded call failed" name=head exception=e; nothing;
        end
        raw === nothing && return expr
        # NotReducible protocol: per MeTTa spec, a grounded function returning
        # the symbol `NotReducible` signals "the interpreter should leave my
        # call unreduced." Honor the sentinel by returning the original expr
        # instead of the literal symbol.
        (raw === "NotReducible" || raw === :NotReducible) && return expr
        return if raw isa String
            from_sexpr(raw)
        elseif raw isa Vector{String}
            from_sexpr.(raw)
        else
            raw
        end
    end

    # ── Rule rewriting ────────────────────────────────────────────────────────
    if head isa Symbol
        evaled_args = [eval_metta(a, space) for a in args]

        # Per MeTTa spec: if `(: head (-> T1 T2 ... Tret))` is declared in the
        # space AND any arg's type doesn't match the corresponding expected
        # type, return (Error <expr> (BadArgType <pos> <expected> <actual>)).
        # Scoped to the rule-rewrite path — grounded primitives handle their
        # own type policy via the GROUNDED_REGISTRY callback's return.
        type_err = _check_arg_types(head, expr, evaled_args, space)
        type_err !== nothing && return type_err

        rules = core_rules(space, head)
        matched_arity = false
        for (head_params, body) in rules
            # Arity check first — lets us distinguish "no rule with right arity"
            # (→ IncorrectNumberOfArguments) from "unification failed on the value"
            # (→ return unreduced).
            length(head_params) == length(evaled_args) || continue
            matched_arity = true
            bindings = _unify_args(head_params, evaled_args)
            bindings === nothing && continue
            result = eval_metta(_apply_bindings(body, bindings), space)
            return result
        end
        # Per MeTTa spec: if rules exist for this head but none match the arity,
        # return (Error <expr> IncorrectNumberOfArguments) — auto-generated by
        # the interpreter. Previously PRIMUS returned the unreduced expr, which
        # silently masked arity bugs in user code.
        !isempty(rules) && !matched_arity && return Any[Symbol("Error"), expr, Symbol("IncorrectNumberOfArguments")]
        # No rule matched (and either no rules exist or rules existed with
        # right arity but unification failed on value) — return reduced expr.
        return vcat([head], evaled_args)
    end

    expr
end

# ── Type-check helpers ────────────────────────────────────────────────────────

"""
    _check_arg_types(head, expr, evaled_args, space) → nothing | Error-expr

If a declared signature `(: head (-> T1 T2 ... Tret))` exists in the space
and an arg's actual type doesn't match its expected type, returns the
spec-conformant Error atom `(Error <expr> (BadArgType <pos> <expected> <actual>))`.
Returns `nothing` (allow eval to continue) if:

  - No signature declared for this head.
  - The declared signature has different arity than the call.
  - All args' types pass the lenient `_types_match` check.

Lenient by design — `Atom` and `%Undefined%` match anything (per spec),
type variables (`\$t`) match anything (generic-parameter idiom from
`(: == (-> \$t \$t Bool))`), and Variable-typed actual args match anything
(since the var will be bound at unification).
"""
function _check_arg_types(head::Symbol, expr, evaled_args::Vector, space::CoreSpace)
    sig_matches = core_match(space, [Symbol(":"), head, Symbol("\$sig")])
    isempty(sig_matches) && return nothing
    for m in sig_matches
        m isa Vector && length(m) == 3 || continue
        sig = m[3]
        sig isa Vector && length(sig) >= 2 && sig[1] === Symbol("->") || continue
        # sig = [->, T1, T2, ..., TN, Tret]
        expected_arg_types = sig[2:(end - 1)]
        length(expected_arg_types) == length(evaled_args) || continue
        for (i, (arg, expected_t)) in enumerate(zip(evaled_args, expected_arg_types))
            actual_t = _infer_arg_type(arg, space)
            _types_match(actual_t, expected_t) && continue
            return Any[Symbol("Error"), expr, Any[Symbol("BadArgType"), i, expected_t, actual_t]]
        end
        return nothing
    end
    nothing
end

function _types_match(actual, expected)::Bool
    actual === expected && return true
    # Per spec: %Undefined% and Atom are universal in the type system
    actual === Symbol("%Undefined%") && return true
    expected === Symbol("%Undefined%") && return true
    expected === Symbol("Atom") && return true
    # Variable actual (at unification it'll be bound to something concrete)
    actual === Symbol("Variable") && return true
    # Generic parameters in the expected type — `(: id (-> $t $t))`
    expected isa Symbol && (startswith(string(expected), "\$") || startswith(string(expected), "__var_")) && return true
    false
end

function _infer_arg_type(atom, space::CoreSpace)
    # Identical resolution rule as _eval_get_type:
    # declared types in the space win, structural inference as fallback.
    matches = core_match(space, [Symbol(":"), atom, Symbol("\$t")])
    if !isempty(matches) && matches[1] isa Vector && length(matches[1]) >= 3
        return matches[1][3]
    end
    atom_s = to_sexpr_atom(atom)
    s = strip(atom_s)
    tryparse(Int, s) !== nothing && return Symbol("Number")
    tryparse(Float64, s) !== nothing && return Symbol("Number")
    (s == "True" || s == "False" || s == "true" || s == "false") && return Symbol("Bool")
    startswith(s, "\"") && return Symbol("String")
    startswith(s, "(") && return Symbol("Expression")
    startswith(s, "\$") && return Symbol("Variable")
    Symbol("Symbol")
end

"""
    _spec_types_match(t1, t2) :: Bool

Spec-conformant symmetric `match_types`. Per MeTTa spec:

    if t1 == %Undefined% or t1 == Atom or t2 == %Undefined% or t2 == Atom:
        match.
    else match if t1 == t2 (or, in the streaming version, run match_atoms).

Used by `_eval_type_cast` so both meta-type universals AND structural
equality fire correctly. Kept in lock-step with the grounded `match-types`
registration in Primitives.jl.
"""
function _spec_types_match(t1, t2)::Bool
    (t1 === Symbol("%Undefined%") || t1 === Symbol("Atom") || t2 === Symbol("%Undefined%") || t2 === Symbol("Atom")) &&
        return true
    t1 === t2
end

"""
    _eval_type_cast(args, space) → Atom | Error-expression

Special-form implementation of `(type-cast \$atom \$type \$space)`. Per the
spec's type_cast algorithm:

    \$types = <list of the types of \$atom from the \$space>
    \$no_match = []
    for \$t in \$types:
        if match_types(\$t, \$type) succeeds: return \$atom
        else: \$no_match += [\$t]
    return [(Error \$atom (BadType \$type \$t)) for \$t in \$no_match]

Differences from the previous grounded implementation:

  - Reads ALL declared types from the space, not just structural inference.
  - Loops over them with first-match-success (spec semantics).
  - Honors Atom and %Undefined% as universal via _spec_types_match.

Falls back to structural inference only when no declared types exist.
The grounded registration in Primitives.jl is kept for backwards
compatibility; the special-form dispatch fires first.
"""
function _eval_type_cast(args::Vector, space::CoreSpace)
    length(args) < 2 && return nothing
    atom = eval_metta(args[1], space)
    requested_t = eval_metta(args[2], space)
    # third arg is the space — we already have it via `space`.

    # Read all declared types from the space.
    matches = core_match(space, [Symbol(":"), atom, Symbol("\$t")])
    declared_types = Any[]
    for m in matches
        m isa Vector && length(m) == 3 && push!(declared_types, m[3])
    end

    if !isempty(declared_types)
        # Spec algorithm — loop, first match wins, else accumulate BadTypes.
        no_match = Any[]
        for t in declared_types
            _spec_types_match(t, requested_t) && return atom
            push!(no_match, t)
        end
        # No declared type matched. Per spec, return errors for each non-matching
        # type. Single-valued evaluator: return the first one (the additional
        # ones would be in the stream under streaming `=`).
        return Any[Symbol("Error"), atom, Any[Symbol("BadType"), requested_t, no_match[1]]]
    end

    # No declared types — fall back to structural inference.
    inferred = _infer_arg_type(atom, space)
    _spec_types_match(inferred, requested_t) && return atom
    Any[Symbol("Error"), atom, Any[Symbol("BadType"), requested_t, inferred]]
end

"""
    run_metta(source::String, space=default_space()) → Vector{Any}

Parse and evaluate a MeTTa source string.
Lines starting with `!` are executed; others are added as atoms.
"""
function run_metta(source::String, space::CoreSpace = default_space())::Vector{Any}
    results = Any[]
    # Use the proper parser to handle multi-line expressions and comments
    exprs = try
        parse_metta(source)
    catch e
        ; @warn "run_metta: parse error" exception=e; Any[]
    end
    for expr in exprs
        if expr isa Vector && !isempty(expr) && expr[1] === :!
            # Execution directive — evaluate the inner expression
            push!(results, eval_metta(expr[2], space))
        else
            core_add!(space, expr)
        end
    end
    results
end

"""
    run_file(path, space=default_space()) → Vector{Any}

Load and evaluate a .metta file. Atoms are added to space; `!` forms are executed.

Relative `import!` paths inside the file are resolved relative to the file's
own directory — matching PeTTa's behaviour.  The working directory is restored
after the file finishes loading.
"""
function run_file(path::String, space::CoreSpace = default_space())::Vector{Any}
    isfile(path) || error("File not found: $path")
    abs_path = abspath(path)
    prev_dir = pwd()
    try
        cd(dirname(abs_path))
        run_metta(read(abs_path, String), space)
    finally
        cd(prev_dir)
    end
end

# ── Special form implementations ──────────────────────────────────────────────

# Gather ALL match results as a Vector{Any}, with NO single-result unwrap.
# This is the faithful nondeterministic-stream form: a stream of one result
# that is itself an expression (e.g. a tuple `($r $c)`) stays a 1-element
# stream `[(r c)]` instead of being mistaken for the stream `[r, c]`.
# `collapse` consumes this directly; `_eval_match` adds the convenience unwrap.
function _eval_match_all(args::Vector, space::CoreSpace)::Vector{Any}
    length(args) < 2 && return Any[]
    pattern  = args[2]
    template = length(args) >= 3 ? args[3] : pattern
    s        = _resolve_space(args[1], space)
    results  = Any[]
    for cand in core_match(s, pattern)
        b = _unify(pattern, cand)
        b === nothing && continue
        # MeTTa spec: match returns the substituted template as DATA, not evaluated.
        # Evaluating the template would execute rule atoms matched by wildcards.
        push!(results, _apply_bindings(template, b))
    end
    results
end

function _eval_match(args::Vector, space::CoreSpace)
    length(args) < 2 && return nothing
    results = _eval_match_all(args, space)
    # Convenience unwrap for non-collapse callers: a lone result is returned
    # bare so `(let $x (match ...) ...)` etc. see a value, not a 1-list.
    isempty(results) ? [] : (length(results) == 1 ? results[1] : results)
end

function _eval_let(args::Vector, space::CoreSpace)
    length(args) < 3 && return nothing
    var = args[1]
    val = eval_metta(args[2], space)
    body = args[3]
    bindings = if var isa Symbol && startswith(string(var), "\$")
        Dict{Symbol, Any}(Symbol(string(var)[2:end]) => val)
    else
        Dict{Symbol, Any}()
    end
    eval_metta(_apply_bindings(body, bindings), space)
end

function _eval_if(args::Vector, space::CoreSpace)
    length(args) < 3 && return nothing
    cond = eval_metta(args[1], space)
    (cond === true || cond === :True || cond == "True") ? eval_metta(args[2], space) : eval_metta(args[3], space)
end

function _eval_collapse(args::Vector, space::CoreSpace)
    isempty(args) && return []
    inner = args[1]
    # Gather nondeterministic results WITHOUT match's single-result unwrap, so a
    # lone result that is itself an expression (e.g. a `($r $c)` tuple) stays one
    # element instead of being mistaken for the results list (the field values).
    if inner isa Vector && !isempty(inner)
        h = inner[1]
        (h === :match || h === Symbol("match")) && return _eval_match_all(inner[2:end], space)
        h === :superpose && return _eval_superpose(inner[2:end], space)
    end
    result = eval_metta(inner, space)
    result isa Vector ? result : [result]
end

function _eval_superpose(args::Vector, space::CoreSpace)
    isempty(args) && return nothing
    items = args[1] isa Vector ? args[1] : [args[1]]
    [eval_metta(item, space) for item in items]
end

function _eval_exec_atom(expr::Vector, space::CoreSpace)
    # exec atoms use MORK's MM2 calculus (AUSink/CountSink/HeadSink).
    # Results are written to the space as side effects; callers inspect afterward.
    #
    # When use_supercompiler=true (opt-in via enable_sc! or register_for_space!):
    #   MorkSupercompiler.plan! applies Rule-of-64 source decomposition and
    #   join-order reordering before running calculus.  Output contract is
    #   identical (same trie mutation: space_add_all_sexpr! + space_metta_calculus!).
    #   Approx pipeline is NOT engaged (plan! bypasses execute!/SCPipeline entirely).
    #
    #   SET semantics: safe by construction. flow_vars carries every variable the
    #   final template needs through all intermediate _sc_tmp* atoms, so MORK
    #   dedup of intermediates can only collapse bindings that produce the same
    #   final result — no distinct result is ever dropped.
    #
    #   Multiplicity caveat: when two distinct binding paths produce the SAME final
    #   atom, decomposed dedup collapses them earlier than the direct engine does.
    #   CountSink workloads (WILLIAM.count, WILLIAM.dict-size) should verify
    #   before opting in if they rely on duplicate-result counts being exact.
    if space.use_supercompiler
        MorkSupercompiler.plan!(space.inner, to_sexpr(expr), typemax(Int))
    else
        core_add!(space, expr)
        core_calculus!(space, 10_000)
    end
    nothing
end

function _eval_add_atom(args::Vector, space::CoreSpace)
    # Per MeTTa spec: add-atom HOLDS its atom argument — stores the
    # expression as data, unevaluated. add-reduct is the companion that
    # evaluates first. Previously PRIMUS evaluated, collapsing the
    # add-atom/add-reduct distinction and silently reducing any expression
    # whose inner subterms had grounded/rule definitions. This broke the
    # algorithm-layer use case of storing parameterised templates as
    # data (e.g. (add-atom &self (rule-template $x))) which is exactly
    # what self-modifying / ActPC workloads do.
    length(args) < 2 && return nothing
    sp = _resolve_space(args[1], space)
    atom = args[2]   # HELD — not evaluated
    core_add!(sp, atom)
    atom
end

function _eval_remove_atom(args::Vector, space::CoreSpace)
    # Same spec rule as add-atom: HOLD the atom argument. The user knows
    # what they stored; removing requires matching the literal atom shape.
    length(args) < 2 && return nothing
    sp = _resolve_space(args[1], space)
    atom = args[2]   # HELD — not evaluated
    core_remove!(sp, atom)
    atom
end

# ── ECAN bulk operations (Julia fast path) ──────────────────────────────────
#
# These walk the MORK trie ONCE collecting AV atoms, then mutate in a single
# pass.  Equivalent pure-MeTTa versions in t1_core_logic.metta are unreachable
# (special-form dispatch wins) — they remain as documentation of the algorithm.
#
# Speedup vs pure-MeTTa: avoids per-atom MeTTa eval overhead inside the bulk
# loop (rule lookup, binding allocation, _eval_let cascade).  Trie ops are
# still remove-then-add per atom (MORK byte-trie can't mutate float bytes
# in-place — value is part of the key path), but the per-atom JIT cost drops
# by ~10x.  Sufficient to bring a 100-tick ECAN heartbeat from minutes to
# sub-second at N=5-50 atoms.

function _coerce_float(x::Any)::Float64
    x isa Number && return Float64(x)
    if x isa String
        n = tryparse(Float64, x)
        n === nothing || return n
    end
    if x isa Symbol
        n = tryparse(Float64, string(x))
        n === nothing || return n
    end
    0.0
end

"""
    (decimate-importance! factor) → True

Multiply every AV atom's STI and LTI by (1 - factor).  VLTI preserved.
Implements ECAN's decay step; called from t1_ECAN_Policies.metta via
`(= (apply-decay!) (decimate-importance! (ecan-decay-factor)))`.
"""
function _eval_decimate_importance!(args::Vector, space::CoreSpace)
    length(args) < 1 && return :True
    factor = _coerce_float(eval_metta(args[1], space))
    retention = 1.0 - factor

    # One trie scan for all AV atoms.
    av_pattern = [Symbol("AV"), Symbol("\$id"), Symbol("\$sti"), Symbol("\$lti"), Symbol("\$vlti")]
    avs = core_match(space, av_pattern)

    for av in avs
        if av isa Vector && length(av) == 5 && av[1] === :AV
            id   = av[2]
            sti  = _coerce_float(av[3])
            lti  = _coerce_float(av[4])
            vlti = av[5]
            core_remove!(space, av)
            core_add!(space, [Symbol("AV"), id, sti * retention, lti * retention, vlti])
        end
    end
    :True
end

"""
    (normalize-attention! target) → True

Scale every AV atom's STI so the population sum equals `target`.  LTI and
VLTI preserved.  No-op if current sum is below ε (avoids division by zero).
"""
function _eval_normalize_attention!(args::Vector, space::CoreSpace)
    length(args) < 1 && return :True
    target = _coerce_float(eval_metta(args[1], space))

    av_pattern = [Symbol("AV"), Symbol("\$id"), Symbol("\$sti"), Symbol("\$lti"), Symbol("\$vlti")]
    avs = core_match(space, av_pattern)

    total = 0.0
    valid_avs = Tuple{Any, Float64, Float64, Any}[]
    for av in avs
        if av isa Vector && length(av) == 5 && av[1] === :AV
            id   = av[2]
            sti  = _coerce_float(av[3])
            lti  = _coerce_float(av[4])
            vlti = av[5]
            push!(valid_avs, (id, sti, lti, vlti))
            total += sti
        end
    end

    total < 1.0e-6 && return :True
    scale = target / total

    for (id, sti, lti, vlti) in valid_avs
        old_av = [Symbol("AV"), id, sti, lti, vlti]
        core_remove!(space, old_av)
        core_add!(space, [Symbol("AV"), id, sti * scale, lti, vlti])
    end
    :True
end

# ── Unification helpers ───────────────────────────────────────────────────────

"""
Unify two expressions, returning bindings Dict or nothing on failure.
"""
function _unify(@nospecialize(pattern), @nospecialize(value))::Union{Dict{Symbol, Any}, Nothing}
    bindings = Dict{Symbol, Any}()
    _unify!(pattern, value, bindings) ? bindings : nothing
end

function _unify!(@nospecialize(pat), @nospecialize(val), b::Dict{Symbol, Any})::Bool
    # Symmetric variable handling per MeTTa spec match_atoms: a variable on
    # either side binds to the other side. Previously PRIMUS only checked
    # the pat (first) position, so calls like
    #   _unify(42, $y)  →  failed
    # would skip the binding-creation branch even though $y is a free var
    # that should bind to 42. This broke the canonical
    #   (unify atom (quote $y) then else)  →  bind $y, take then
    # idiom because $y sits in val position after pattern descent.

    # Pat-is-var (original behavior)
    if pat isa Symbol
        pat_str = string(pat)
        if startswith(pat_str, "\$") || startswith(pat_str, "__var_")
            vname = startswith(pat_str, "__var_") ? Symbol("\$" * pat_str[7:end]) : Symbol(pat_str[2:end])
            existing = get(b, vname, nothing)
            existing !== nothing && return existing == val
            b[vname] = val
            return true
        end
    end

    # Symmetric: val-is-var (new — fixes the unify-against-quoted-pattern case)
    if val isa Symbol
        val_str = string(val)
        if startswith(val_str, "\$") || startswith(val_str, "__var_")
            vname = startswith(val_str, "__var_") ? Symbol("\$" * val_str[7:end]) : Symbol(val_str[2:end])
            existing = get(b, vname, nothing)
            existing !== nothing && return existing == pat
            b[vname] = pat
            return true
        end
    end

    pat == val && return true
    (pat isa Vector && val isa Vector) || return false
    length(pat) == length(val) || return false
    all(i -> _unify!(pat[i], val[i], b), eachindex(pat))
end

"""
Unify a list of patterns against a list of values.
"""
function _unify_args(params::Vector, args::Vector)::Union{Dict{Symbol, Any}, Nothing}
    length(params) == length(args) || return nothing
    _unify(params, args)
end

"""
Apply variable bindings to an expression.
"""
function _apply_bindings(@nospecialize(expr), b::Dict{Symbol, Any})::Any
    isempty(b) && return expr
    if expr isa Symbol
        s = string(expr)
        if startswith(s, "\$")
            return get(b, Symbol(s[2:end]), expr)
        elseif startswith(s, "__var_")
            return get(b, Symbol("\$" * s[7:end]), expr)
        end
    end
    expr isa Vector && return Any[_apply_bindings(e, b) for e in expr]
    expr
end

# ── Missing special form implementations ─────────────────────────────────────

function _eval_let_star(args::Vector, space::CoreSpace)
    # (let* (($v1 e1) ($v2 e2) ...) body)
    length(args) < 2 && return nothing
    bindings_list = args[1]
    body = args[2]
    b = Dict{Symbol, Any}()
    pairs = bindings_list isa Vector ? bindings_list : [bindings_list]
    for pair in pairs
        pair isa Vector && length(pair) >= 2 || continue
        var = pair[1]
        val = eval_metta(_apply_bindings(pair[2], b), space)
        if var isa Vector && !isempty(var)
            # Compound pattern: ((Constructor $x $y) val) — unify and merge bindings
            bindings = _unify(_apply_bindings(var, b), val)
            bindings !== nothing && merge!(b, bindings)
        else
            vname = _var_name(var)
            vname !== nothing && (b[vname] = val)
        end
    end
    eval_metta(_apply_bindings(body, b), space)
end

function _eval_case(args::Vector, space::CoreSpace)
    # (case val ((pat result) ...))
    length(args) < 2 && return nothing
    val   = eval_metta(args[1], space)
    pairs = args[2] isa Vector ? args[2] : args[2:end]
    for pair in pairs
        pair isa Vector && length(pair) >= 2 || continue
        pat    = pair[1]
        result = pair[2]
        b      = _unify(pat, val)
        b === nothing && continue
        return eval_metta(_apply_bindings(result, b), space)
    end
    nothing
end

function _eval_chain(args::Vector, space::CoreSpace)
    # (chain atom $var template) — per MeTTa spec §Minimal MeTTa Instructions
    # Evaluate atom, bind result to $var, then evaluate template with binding.
    length(args) < 3 && return nothing
    evaled   = eval_metta(args[1], space)
    var      = args[2]
    template = args[3]
    vname    = _var_name(var)
    if vname !== nothing
        eval_metta(_apply_bindings(template, Dict{Symbol, Any}(vname => evaled)), space)
    else
        eval_metta(template, space)
    end
end

# Sentinel type for function/return control flow
struct _ReturnValue
    val::Any
end

function _eval_function(args::Vector, space::CoreSpace)
    # (function body) — evaluate body; if result is (return val), unwrap val
    isempty(args) && return nothing
    result = eval_metta(args[1], space)
    result isa _ReturnValue && return result.val
    # If it's a list starting with :return, unwrap
    if result isa Vector && !isempty(result) && result[1] === :return
        return length(result) >= 2 ? result[2] : nothing
    end
    result
end

function _eval_return(args::Vector, space::CoreSpace)
    # (return val) — wraps value for function to unwrap
    isempty(args) && return _ReturnValue(nothing)
    _ReturnValue(eval_metta(args[1], space))
end

function _eval_eval(args::Vector, space::CoreSpace)
    # (eval atom) — force one evaluation step
    isempty(args) && return nothing
    inner = eval_metta(args[1], space)
    eval_metta(inner, space)
end

function _eval_unify(args::Vector, space::CoreSpace)
    # (unify atom pattern then else) — 4-arg canonical form per spec.
    # NEITHER atom nor pattern is evaluated — per the spec's match_atoms,
    # both sides match structurally as-is. The caller is responsible for
    # putting `atom` in the form they want to match against (typically via
    # chain's binding substitution, which already evaluated the value).
    # Previously PRIMUS evaluated both, which collapsed wrappers like
    # `(quote $y)` to bare `$y` and stripped quote-wrappers off computed
    # values — breaking the canonical
    #   (chain (quote (quote 42)) $x (unify $x (quote $y) $y else))
    # idiom because `$x` resolved to `(quote 42)` then evaluation stripped
    # the quote wrapper to bare `42`, which can't unify with `(quote $y)`.
    length(args) < 4 && return nothing
    a = args[1]   # ATOM — structural
    b = args[2]   # PATTERN — structural
    bindings = _unify(a, b)
    if bindings !== nothing
        eval_metta(_apply_bindings(args[3], bindings), space)
    else
        eval_metta(args[4], space)
    end
end

function _eval_quote(args::Vector)
    # (quote atom) — return atom unevaluated
    isempty(args) ? nothing : args[1]
end

function _eval_unquote(args::Vector, space::CoreSpace)
    # (unquote (quote atom)) → evaluate the quoted atom
    isempty(args) && return nothing
    inner = args[1]
    if inner isa Vector && !isempty(inner) && inner[1] === :quote
        length(inner) >= 2 ? eval_metta(inner[2], space) : nothing
    else
        eval_metta(inner, space)
    end
end

function _eval_do(args::Vector, space::CoreSpace)
    # (do e1 e2 ... eN) / (begin ...) — evaluate all, return last
    isempty(args) && return nothing
    result = nothing
    for expr in args
        result = eval_metta(expr, space)
    end
    result
end

# ── Package registry — maps package name → local path  ───────────────────────
# Populated by git-import!. Mirrors PeTTa's package cache (~/.metta/packages/).
const _PACKAGE_REGISTRY = Dict{String, String}()
const _METTA_PACKAGES_DIR = joinpath(homedir(), ".metta", "packages")
# Core/lib/ — algorithm libraries, mirrors PeTTa/lib/
const _CORE_LIB_DIR = joinpath(@__DIR__, "..", "..", "lib")

"""
Return the local path for a `(library pkg file)` import expression, or nothing.

Resolution order (directory form preferred so multi-file libraries can name
their entry point conventionally):

(library name)            tries  Core/lib/name/name.metta
Core/lib/name/loader.metta
Core/lib/name.metta
<package registry> ...
(library pkg file)        tries  Core/lib/pkg/file.metta
Core/lib/file.metta
<package registry> ...
"""
function _resolve_library(expr)::Union{String, Nothing}
    if expr isa Vector && !isempty(expr) && expr[1] === Symbol("library")
        parts = expr[2:end]
        if length(parts) == 2
            pkg  = string(parts[1])
            file = string(parts[2])
            # 1a. Core/lib/pkg/file.metta  (directory layout)
            p = joinpath(_CORE_LIB_DIR, pkg, file * ".metta")
            isfile(p) && return p
            # 1b. Core/lib/file.metta  (flat layout, back-compat)
            p = joinpath(_CORE_LIB_DIR, file * ".metta")
            isfile(p) && return p
            # 2. Registered via git-import!
            if haskey(_PACKAGE_REGISTRY, pkg)
                p = joinpath(_PACKAGE_REGISTRY[pkg], file * ".metta")
                isfile(p) && return p
            end
            # 3. ~/.metta/packages/pkg/file.metta
            p = joinpath(_METTA_PACKAGES_DIR, pkg, file * ".metta")
            isfile(p) && return p
        elseif length(parts) == 1
            name = string(parts[1])
            # 1a. Core/lib/name/name.metta  (directory canonical entry)
            p = joinpath(_CORE_LIB_DIR, name, name * ".metta")
            isfile(p) && return p
            # 1b. Core/lib/name/loader.metta  (directory loader form)
            p = joinpath(_CORE_LIB_DIR, name, "loader.metta")
            isfile(p) && return p
            # 1c. Core/lib/name.metta  (flat, back-compat — WILLIAM/MetaMo shape)
            p = joinpath(_CORE_LIB_DIR, name * ".metta")
            isfile(p) && return p
            # 2. Registered package
            if haskey(_PACKAGE_REGISTRY, name)
                p = joinpath(_PACKAGE_REGISTRY[name], name * ".metta")
                isfile(p) && return p
            end
            # 3. ~/.metta/packages/name/name.metta
            p = joinpath(_METTA_PACKAGES_DIR, name, name * ".metta")
            isfile(p) && return p
            # 4. ~/.metta/lib/name.metta  (PeTTa-compatible flat lib dir)
            p = joinpath(homedir(), ".metta", "lib", name * ".metta")
            isfile(p) && return p
        end
    end
    nothing
end

function _eval_import!(args::Vector, space::CoreSpace)
    # (import! &self "path/to/file.metta")        — file path
    # (import! &self (library pkg lib_name))       — package + file (git-import! style)
    # (import! &self (library lib_name))           — shorthand
    length(args) < 2 && return nothing
    path_arg = args[2]

    # Try library resolution first
    lib_path = _resolve_library(path_arg)
    if lib_path !== nothing
        run_file(lib_path, space)
        return path_arg
    end

    # Fall back to plain file path
    path = path_arg isa String ? path_arg : string(path_arg)
    isfile(path) || return [:Error, [:import!, path_arg], Symbol("FileNotFound")]
    run_file(path, space)
    path_arg
end

function _eval_git_import!(args::Vector, space::CoreSpace)
    # (git-import! "https://github.com/user/repo.git")
    # (git-import! "https://github.com/user/repo.git" "build.sh")
    # Clones/updates repo to ~/.metta/packages/<repo-name>/
    # Registers the path so (library ...) can find it.
    length(args) < 1 && return nothing
    url_arg = args[1]
    url = url_arg isa String ? url_arg : string(url_arg)

    # Derive repo name from URL  (last path segment, strip .git)
    repo_name = replace(split(url, "/")[end], r"\.git$" => "")
    # Primary: clone into Core/lib/<repo-name>/  (mirrors PeTTa/lib/ layout)
    dest = joinpath(_CORE_LIB_DIR, repo_name)
    mkpath(dirname(dest))

    if isdir(joinpath(dest, ".git"))
        run(`git -C $dest pull --quiet`; wait = true)
    else
        run(`git clone --quiet $url $dest`; wait = true)
    end

    # Run optional build script
    if length(args) >= 2
        build = string(args[2])
        build_path = joinpath(dest, build)
        isfile(build_path) && run(`bash $build_path`; wait = true)
    end

    _PACKAGE_REGISTRY[repo_name] = dest
    @info "git-import!: $repo_name → $dest"
    repo_name
end

function _eval_get_type_space(args::Vector, space::CoreSpace)
    # (get-type-space &self atom) → lookup : atom Type in space
    length(args) < 2 && return Symbol("%Undefined%")
    atom = eval_metta(args[2], space)
    atom_s = to_sexpr(atom)
    # Search for (: atom Type) in space
    matches = core_match(space, [Symbol(":"), atom, Symbol("\$t")])
    if isempty(matches)
        Symbol("%Undefined%")
    else
        (matches[1] isa Vector && length(matches[1]) >= 3 ? matches[1][3] : Symbol("%Undefined%"))
    end
end

"""
    _eval_get_type(args, space) → Symbol

Special-form implementation of `(get-type \$atom)`. Resolves the type by:

 1. Querying the space for `(: \$atom \$t)` declarations — declared types win.
 2. Falling back to structural inference if no declaration exists.

Closes the historic three-oracle disagreement on declared-but-non-structural
atoms — previously `get-type` ignored declarations and returned the
structural type, disagreeing with `get-type-space` and `type-cast`'s
inferred result.

First-declaration-wins matches `get-type-space` (single-valued). Under
streaming `=`, this should become multi-valued (stream of declared types),
but that's a downstream consumer migration tracked in the resume notes.
"""
function _eval_get_type(args::Vector, space::CoreSpace)
    isempty(args) && return Symbol("%Undefined%")
    atom = eval_metta(args[1], space)
    # Step 1 — query declared types from the space
    matches = core_match(space, [Symbol(":"), atom, Symbol("\$t")])
    if !isempty(matches) && matches[1] isa Vector && length(matches[1]) >= 3
        return matches[1][3]
    end
    # Step 2 — fall back to structural inference (same logic as the grounded
    # registration in Primitives.jl, kept in sync with that policy choice).
    atom_s = to_sexpr_atom(atom)
    s = strip(atom_s)
    tryparse(Int, s) !== nothing && return Symbol("Number")
    tryparse(Float64, s) !== nothing && return Symbol("Number")
    (s == "True" || s == "False" || s == "true" || s == "false") && return Symbol("Bool")
    startswith(s, "\"") && return Symbol("String")
    startswith(s, "(") && return Symbol("Expression")
    startswith(s, "\$") && return Symbol("Variable")
    Symbol("Symbol")
end

function _eval_add_reduct(args::Vector, space::CoreSpace)
    # (add-reduct &self expr) — evaluate expr, add result as atom
    length(args) < 2 && return nothing
    val = eval_metta(args[2], space)
    core_add!(space, val)
    val
end

function _eval_for_each(args::Vector, space::CoreSpace)
    # (for-each-in-atom list fn) — apply fn to each element
    length(args) < 2 && return nothing
    lst = eval_metta(args[1], space)
    fn = args[2]
    items = lst isa Vector ? lst : [lst]
    for item in items
        eval_metta([fn, item], space)
    end
    nothing
end

function _eval_noreduce_eq(args::Vector)
    # Compare atoms structurally WITHOUT evaluating — args arrive unevaluated
    length(args) < 2 && return false
    to_sexpr(args[1]) == to_sexpr(args[2]) ? :True : :False
end

# Named-space registry is scoped to the evaluation context (space.named_spaces).
# Process-global _NAMED_SPACES was removed — it caused data races, cross-context
# collisions, and unbounded memory leaks under concurrent/nested evaluation.
# Each CoreSpace carries its own registry; bind! writes to space.named_spaces.

function _resolve_space(sp_arg::Any, default::CoreSpace)::CoreSpace
    sp_arg === Symbol("&self") && return default
    if sp_arg isa Symbol
        v = get(default.named_spaces, sp_arg, nothing)
        v !== nothing && return v   # Dict{Symbol,CoreSpace} — always a CoreSpace if present
        # A &name that looks like a space reference but isn't bound is almost always a bug.
        # Silent fallthrough to `default` would mutate the wrong space with no error.
        sp_str = string(sp_arg)
        if startswith(sp_str, "&")
            error(
                "Unresolved space reference: $sp_arg\n" *
                "Use (bind! $sp_arg (new-space)) before using it as a space arg, " *
                "or (with-space $sp_arg (new-space) ...) for a transient scope.",
            )
        end
    end
    resolved = try
        eval_metta(sp_arg, default)
    catch
        ; nothing
    end
    resolved isa CoreSpace ? resolved : default
end

function _eval_with_space(args::Vector, space::CoreSpace)
    # (with-space $var init-expr body...)
    # Binds $var to a new (or provided) space for the dynamic extent of body,
    # then removes the root reference on exit — enforces transient scratch lifetime.
    # This is the language-level equivalent of "create in Julia, pass as arg":
    #   (with-space &scratch (new-space)
    #     (add-atom &scratch (candidate-rule))
    #     (WILLIAM.Learn &scratch (test-atom)))
    length(args) < 3 && return nothing
    name     = args[1]                           # e.g. Symbol("&scratch")
    init_val = eval_metta(args[2], space)        # evaluated ONCE at entry
    init_val isa CoreSpace || return nothing
    # Save-and-restore: if &name was already bound (shadowing or nesting),
    # restore it on exit rather than unconditionally deleting.
    # Handles: (with-space &s ... (with-space &s ...)) — inner exit restores outer.
    prior = name isa Symbol ? get(space.named_spaces, name, nothing) : nothing
    name isa Symbol && (space.named_spaces[name] = init_val)
    result = nothing
    try
        for body_expr in args[3:end]
            result = eval_metta(body_expr, space)
        end
    finally
        if name isa Symbol
            if prior === nothing
                delete!(space.named_spaces, name)   # wasn't bound before — release
            else
                space.named_spaces[name] = prior    # was bound — restore prior
            end
        end
    end
    result
end

function _eval_bind!(args::Vector, space::CoreSpace)
    # (bind! name expr) — Stage 1 semantics (canonical-aligned, with
    # prefix-as-metadata for Stage 2 shared-trie evolution):
    #
    #   - If `val` is a CoreSpace AND `name` starts with `&`, register the
    #     name → CoreSpace mapping AND record a derived byte-prefix in
    #     PREFIX_REGISTRY as METADATA.  The CoreSpace keeps its own
    #     independent MORK trie (canonical isolation — same as
    #     hyperon-experimental / CeTTa / PeTTa do today).
    #
    #   - The prefix metadata is the architectural hook for Stage 2:
    #     when shared-trie + byte-prefix isolation is wired up,
    #     `rebind_to_shared_prefix` flips on and the existing prefix
    #     machinery (PREFIX_REGISTRY, with_read/write_permit, prefix-aware
    #     core_match/add) activates.  Stage 1 ships the architecture
    #     dormant; Stage 2 flips the polarity by uncommenting one line.
    #
    #   - Otherwise (non-CoreSpace value), fall through to `(= name val)`
    #     rule registration.
    length(args) < 2 && return nothing
    name = args[1]
    val  = eval_metta(args[2], space)
    if val isa CoreSpace && name isa Symbol
        derived = derive_prefix_from_name(name)
        derived !== nothing && register_prefix!(name, derived)
        space.named_spaces[name] = val
        return val
    end
    core_add!(space, [:(=), name, val])
    val
end

# ── Variable name extraction ──────────────────────────────────────────────────

function _var_name(var::Any)::Union{Symbol, Nothing}
    var isa Symbol || return nothing
    s = string(var)
    startswith(s, "\$") && return Symbol(s[2:end])
    startswith(s, "__var_") && return Symbol("\$" * s[7:end])
    nothing
end

# ── Higher-order special forms (body must NOT be pre-evaluated) ───────────────
# foldl-atom, map-atom, filter-atom receive the body as a raw unevaluated
# expression. We substitute the accumulator/element variables manually and
# call eval_metta on each substituted body — no string round-trip needed.

function _eval_foldl_atom(args::Vector, space::CoreSpace)
    # (foldl-atom $list $init $acc $elem $body)
    length(args) < 5 && return args[2]  # return init on bad arity
    list_val = eval_metta(args[1], space)
    acc      = eval_metta(args[2], space)
    acc_var  = args[3]   # NOT evaluated — variable name
    elem_var = args[4]   # NOT evaluated — variable name
    body     = args[5]   # NOT evaluated — template

    acc_name  = _var_name(acc_var)
    elem_name = _var_name(elem_var)

    items = if list_val isa Vector
        list_val
    elseif list_val isa String
        begin
        p = from_sexpr(list_val)
        p isa Vector ? p : (p === nothing ? [] : [p])
    end
    else
        [list_val]
    end

    for item in items
        b = Dict{Symbol, Any}()
        acc_name !== nothing && (b[acc_name] = acc)
        elem_name !== nothing && (b[elem_name] = item)
        acc = eval_metta(_apply_bindings(body, b), space)
    end
    acc
end

function _eval_map_atom(args::Vector, space::CoreSpace)
    # (map-atom $list $var $body)
    length(args) < 3 && return []
    list_val = eval_metta(args[1], space)
    elem_var = args[2]   # NOT evaluated
    body     = args[3]   # NOT evaluated

    elem_name = _var_name(elem_var)

    items = if list_val isa Vector
        list_val
    elseif list_val isa String
        begin
        p = from_sexpr(list_val)
        p isa Vector ? p : (p === nothing ? [] : [p])
    end
    else
        [list_val]
    end

    results = Any[]
    for item in items
        b = Dict{Symbol, Any}()
        elem_name !== nothing && (b[elem_name] = item)
        push!(results, eval_metta(_apply_bindings(body, b), space))
    end
    results
end

function _eval_filter_atom(args::Vector, space::CoreSpace)
    # (filter-atom $list $var $pred)
    length(args) < 3 && return []
    list_val = eval_metta(args[1], space)
    elem_var = args[2]   # NOT evaluated
    pred     = args[3]   # NOT evaluated

    elem_name = _var_name(elem_var)

    items = if list_val isa Vector
        list_val
    elseif list_val isa String
        begin
        p = from_sexpr(list_val)
        p isa Vector ? p : (p === nothing ? [] : [p])
    end
    else
        [list_val]
    end

    kept = Any[]
    for item in items
        b = Dict{Symbol, Any}()
        elem_name !== nothing && (b[elem_name] = item)
        r = eval_metta(_apply_bindings(pred, b), space)
        (r === true || r === :True || r == "True") && push!(kept, item)
    end
    kept
end

export eval_metta, run_metta, run_file, default_space
export register_core_primitives!
