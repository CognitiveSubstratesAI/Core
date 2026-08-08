"""
Primitives — grounded MeTTa operations for Core.

Registered via MORK.register_grounded! — callable from space_metta_calculus!
and eval_metta. Only operations that MUST be in Julia are here; everything
expressible as (= pattern body) lives in stdlib/*.metta.

Cross-verified against:
  CeTTa/src/grounded.c       — op_plus/op_minus/etc., math builtins
  Mettatron eval/builtin.rs  — arithmetic, math, *-math naming convention
  hyperon-experimental       — arithmetics.rs, math.rs, atom.rs
  PRIMUS_Core/core/StdLib.jl — adopted arithmetic, comparison, I/O, vectors
                               (ARCHIVED — port-source quarry, not a live cross-check;
                                see ~/PRIMUS/packages/PRIMUS_Core/STATUS.md)
"""

# ── Arithmetic ────────────────────────────────────────────────────────────────

"""
    _gnum(s) -> Union{Int, Float64, Nothing}

Type-preserving numeric parse for a grounded argument — a thin local alias for `MORK.grounded_num`.

DO NOT reimplement here. This used to be its own copy, one of THREE (with `_g2atom` below and
`MorkSupercompiler`'s `_kb_num`), all parsing every operand as `Float64`; the full account of the
defect that caused — exact numbers, the broken KBSaturation bisimulation, and the numeric-model
decision — lives at `MORK.grounded_num`, which is the single definition all consumers now share.
Keeping the rationale in one place is the same discipline as keeping the code in one place.
"""
_gnum(s::AbstractString) = MORK.grounded_num(s)

function _register_arithmetic!()
    # `/` and `%` come from NumericSeam — the SINGLE owner both lanes consult. Int÷Int is INTEGER
    # division and a zero divisor is a DivisionByZero DECISION (hyperon arithmetics.rs:154-155;
    # LeaTTa Stdlib.lean:86-101). This lane RENDERS that decision as a decline (`nothing`, leaving
    # the term unreduced) rather than an atom, which is what it already did for `(% x 0)` and what
    # `gcall("%", [7,0]) === nothing` pins. The interpreter renders the same decision as an
    # `(Error … DivisionByZero)` atom. Same decision, two renderings — that is the seam's contract.
    for (name, op) in [("+", +), ("-", -), ("*", *),
                       ("/", NumericSeam.seam_div), ("%", NumericSeam.seam_mod)]
        MORK.register_grounded!(name, args -> begin
            # STRICTLY BINARY (was `< 2`, which admitted 2 OR MORE and then read only args[1..2],
            # so `(+ 1 2 3)` answered 3 with argument 3 SILENTLY IGNORED — measured 2026-07-29).
            # The interpreter's `_num_binop` requires exactly 2 (`length(xs) == 2 || ExecNoReduce`),
            # so anything else must decline here too, not quietly truncate.
            length(args) == 2 || return nothing
            a = _gnum(args[1]); b = _gnum(args[2])
            (a === nothing || b === nothing) && return nothing
            # `rem(::Int, 0)` throws a Julia DivideError. A HOST exception must never escape into
            # MeTTa evaluation, so decline (leave the term unreduced) instead of crashing — and
            # instead of the old code's silent `NaN`, which came from doing integer rem in floats.
            # (The interpreter's own `%` DOES currently throw here; tracked separately, since
            # changing it needs the hyperon oracle to say what `(% 7 0)` should produce.)
            r = op(a, b)
            r isa NumericSeam.SeamError && return nothing   # decline; see the note above
            string(r)
        end)
    end
end

# ── Comparison ────────────────────────────────────────────────────────────────

function _register_comparison!()
    # `_gnum`, not `tryparse(Float64, …)` — the SAME precision defect applied here: two distinct
    # Int64s above 2^53 coerce to the same Float64, so `(< 9007199254740993 9007199254740994)`
    # compared EQUAL and answered False. Type-preserving parse + Julia's own promotion is exact.
    for (name, op) in [("<", <), (">", >), ("<=", <=), (">=", >=), ("==", ==)]
        MORK.register_grounded!(name, args -> begin
            length(args) == 2 || return nothing      # strictly binary — see _register_arithmetic!
            a = _gnum(args[1]); b = _gnum(args[2])
            if a !== nothing && b !== nothing
                return op(a, b) ? "True" : "False"
            end
            (op === (==)) ? (args[1] == args[2] ? "True" : "False") : nothing
        end)
    end
end

# ── String / Symbol ops ───────────────────────────────────────────────────────

function _register_string_ops!()
    MORK.register_grounded!("concat", args -> join(args, ""))
    MORK.register_grounded!("str-length", args -> begin
        isempty(args) && return nothing
        s = strip(args[1], ['(', ')'])
        string(length(s))
    end)
    MORK.register_grounded!("println!", args -> begin
        println(join(args, " "))
        "()"
    end)
    # trace! <label> <expr> — print label, return expr (pass-through debug)
    # Per MeTTa stdlib: !(trace! "label" expr) → prints "label", returns expr
    MORK.register_grounded!("trace!", args -> begin
        label = length(args) >= 1 ? args[1] : ""
        val   = length(args) >= 2 ? args[2] : "()"
        println("[trace] ", label, " = ", val)
        val   # pass the value through
    end)
end

# ── Type checks ───────────────────────────────────────────────────────────────

function _register_type_checks!()
    MORK.register_grounded!("is-number", args -> begin
        isempty(args) && return "False"
        tryparse(Float64, args[1]) !== nothing ? "True" : "False"
    end)
    MORK.register_grounded!("is-symbol", args -> begin
        isempty(args) && return "False"
        s = args[1]
        !startswith(s, "(") && tryparse(Float64, s) === nothing ? "True" : "False"
    end)
    MORK.register_grounded!("is-empty", args -> begin
        isempty(args) && return "True"
        s = strip(args[1])
        (s == "()" || isempty(s)) ? "True" : "False"
    end)
end

# ── List ops ─────────────────────────────────────────────────────────────────
# REMOVED 2026-06-10: car/cdr/cons/size-atom were double-registered here AND in
# AtomOps.jl `_register_atom_ops!`, which runs LATER (register_core_primitives! →
# _register_atom_ops!) and therefore WON. These copies were dead (last-writer-wins).
# The canonical, more-complete versions live in AtomOps.jl. See
# docs/PRIMITIVE_SURFACE_AND_ECOSYSTEM_TOOLING_2026-06-10.md §1 (double-registration).

# ── Boolean ops ───────────────────────────────────────────────────────────────

function _register_boolean_ops!()
    MORK.register_grounded!("and", args -> begin
        all(a -> a == "True", args) ? "True" : "False"
    end)
    MORK.register_grounded!("or", args -> begin
        any(a -> a == "True", args) ? "True" : "False"
    end)
    MORK.register_grounded!("not", args -> begin
        isempty(args) && return "False"
        args[1] == "False" || args[1] == "()" ? "True" : "False"
    end)
end

# ── Extended math (*-math suffix — Mettatron/CeTTa convention) ───────────────

"""
    _g2atom(s) -> Atom

A grounded ARGUMENT string as a typed interpreter atom, preserving Int vs Float. The distinction is
load-bearing: `metta_grammar.ebnf` makes GROUNDED one of the four ATOM kinds, and hyperon's math
rules are stated IN TERMS of it ("abs/trunc/ceil/floor/round PRESERVE type; sqrt/log/trig ALWAYS
Float"), so collapsing `4` and `4.0` makes those rules unstatable.
"""
_g2atom(s::AbstractString) = begin
    v = MORK.grounded_num(s); v !== nothing && return StandardMeTTa.Grounded(v)   # 2nd copy, gone
    # STRING is GROUNDED, not SYMBOL — `GROUNDED ::= STRING | WORD` (metta_grammar.ebnf). Without this
    # a quoted literal fell through to `Sym(Symbol("\"hello\""))`, i.e. a symbol whose NAME included
    # the quotes, where the interpreter's own `parse_atom` (Eval.jl:2453) yields
    # `Grounded("hello")`. Same unquoting rule as the parser: strip the leading quote.
    startswith(s, "\"") && return StandardMeTTa.Grounded(String(s[nextind(s, 1):(endswith(s, "\"") && length(s) >= 2 ? prevind(s, lastindex(s)) : lastindex(s))]))
    # VARIABLE is one of the grammar's FOUR atom kinds (metta_grammar.ebnf), so it must not fall
    # through to Sym. Two spellings reach here: parse-time `$x`, and `__var_x` — the GROUND symbol
    # `load_metta!(::CoreSpace)` writes so a variable's NAME survives the MORK round trip. Collapsing
    # either into a Sym is what makes `(get-metatype __var_x)` answer Symbol instead of Variable.
    (startswith(s, "\$") || startswith(s, _CORE_VAR_PREFIX_G)) &&
        return StandardMeTTa.Var(startswith(s, "\$") ? s[nextind(s, 1):end] : s[7:end])
    # EXPRESSION — the fourth kind. Do NOT hand-roll a parser: `expr_to_atom` (MM2Router.jl:638) is
    # the byte-level reader that already rebuilds structure AND de Bruijn co-reference. Wrapping the
    # text in a single Sym is what made `(get-metatype (A B))` answer Symbol instead of Expression
    # (a regression I introduced and measured on the way in).
    if startswith(s, "(")
        return try
            expr_to_atom(MORK.sexpr_to_expr(String(s)))
        catch
            StandardMeTTa.Sym(Symbol(s))   # unparseable: treat as an opaque symbol
        end
    end
    StandardMeTTa.Sym(Symbol(s))
end
const _CORE_VAR_PREFIX_G = "__var_"

"""
    _delegate_grounded(name, args) -> Union{String, Nothing}

Run a MORK-lane grounded call through the INTERPRETER'S implementation of the same op, and return
its result as an s-expression string.

⚠️ WHY THIS DELEGATES INSTEAD OF COMPUTING (measured 2026-07-29). `CoreMathOps.jl` (included at
`Eval.jl:2520`) already implements the `*-math` surface FAITHFULLY to hyperon-experimental's
`lib/src/metta/runner/stdlib/math.rs`, and documents its rules verbatim:

    sqrt/log/sin/asin/cos/acos/tan/atan  -> ALWAYS Float
    abs/trunc/ceil/floor/round           -> PRESERVE type (Int->Int, Float->Float)
    isnan/isinf                          -> True/False symbol
    domain errors (sqrt(-x), asin(>1))   -> NaN, like Rust f64 (Julia THROWS, so it is caught)

This file previously re-implemented all sixteen with `isinteger(r) ? string(Int(r)) : string(r)` and
an UNGUARDED `_fn(x)`. Differentially tested against the faithful implementation, **9 of 14 cases
diverged**:

    (sqrt-math 4)    -> 2                  faithful 2.0     (the ALWAYS-Float rule)
    (sqrt-math -4)   -> THREW DomainError  faithful NaN     (host exception escaping MeTTa)
    (asin-math 2)    -> THREW DomainError  faithful NaN
    (floor-math 2.7) -> 2                  faithful 2.0     (the PRESERVE-type rule)
    (ceil-math 2.1)  -> 3                  faithful 3.0
    (log-math 1)     -> 0                  faithful ARITY ERROR — hyperon's log-math takes TWO
                                           arguments (base, value); this copy took one

A second implementation of a surface that already has a faithful one is not a second lane, it is a
divergence generator. Delegating gives ONE source of truth and fixes all nine at once.

Resolution is deferred to CALL time, which is what makes this legal: `Primitives.jl` is included at
`MeTTaCore.jl:52`, before `module Eval` exists at :62 — but these closures only ever run once
a grounded op is invoked, by which point it does.

`ExecNoReduce`/`ExecRuntime` both return `nothing` (= "not applicable", the registry's own protocol),
so a host exception can never escape. Carrying `ExecRuntime`'s message through as a MeTTa `Error`
atom needs the registry's return protocol to grow an error case — tracked, not done here.
"""
function _delegate_grounded(name::String, args)
    R = Eval.TOKEN_REGISTRY
    haskey(R, name) || return nothing
    g = R[name]
    (g isa StandardMeTTa.Grounded && g.value isa Eval.Operation) || return nothing
    r = Eval.execute(g, StandardMeTTa.Atom[_g2atom(a) for a in args], nothing)
    r isa Eval.ExecOk || return nothing
    length(r.results) == 1 || return nothing
    string(r.results[1])
end

function _register_math!()
    # Every op here EXISTS in CoreMathOps.jl (hyperon-faithful) — delegate, never re-derive.
    for name in ["sqrt-math", "abs-math", "log-math", "floor-math", "ceil-math", "round-math",
                 "trunc-math", "sin-math", "cos-math", "tan-math", "asin-math", "acos-math",
                 "atan-math", "pow-math", "isnan-math", "isinf-math"]
        local _n = name
        MORK.register_grounded!(_n, args -> _delegate_grounded(_n, args))
    end
    # `exp-math` has NO counterpart in CoreMathOps (hyperon's math.rs does not define it) — it is our
    # own addition, so it is implemented here, following the same ALWAYS-Float + catch-domain rule.
    MORK.register_grounded!("exp-math", args -> begin
        isempty(args) && return nothing
        x = tryparse(Float64, args[1])
        x === nothing && return nothing
        string(try exp(x) catch e; e isa DomainError ? NaN : rethrow() end)
    end)
end

# Vector ops are PRIMUS-specific extensions (ECAN, PLN cosine-similarity).
# They do NOT belong in Core's standard primitives — not in any reference
# implementation (hyperon-experimental, CeTTa, Mettatron, PeTTa).
# They will live in a separate PRIMUS extension layer on top of Core.
function _register_vector_ops!() end

# ── repr / parse ──────────────────────────────────────────────────────────────

function _register_repr!()
    MORK.register_grounded!("repr", args -> begin
        isempty(args) ? "\"\"" : "\"$(args[1])\""
    end)
    MORK.register_grounded!("parse", args -> begin
        isempty(args) && return nothing
        strip(args[1], ['"', ' '])
    end)
end

# ── Equality / alpha-equivalence ──────────────────────────────────────────────
# Per MeTTa spec: =alpha checks structural equivalence ignoring var names.
# noreduce-eq compares atoms WITHOUT evaluating them first (must be grounded
# so the evaluator does not reduce args before comparison).

function _register_equality_ops!()
    # =alpha: structural equality ignoring variable names
    # (=alpha (Father $X) (Father $Y)) → True  (same structure, vars renamed)
    # (=alpha (Father $X) (Son $X))   → False (different head)
    MORK.register_grounded!("=alpha", args -> begin
        length(args) < 2 && return "False"
        _alpha_eq(args[1], args[2]) ? "True" : "False"
    end)

    # noreduce-eq: structural equality WITHOUT evaluating args.
    # Grounded because it must receive unevaluated S-expression strings.
    MORK.register_grounded!("noreduce-eq", args -> begin
        length(args) < 2 && return "False"
        args[1] == args[2] ? "True" : "False"
    end)
end

# Alpha-equivalence: two expressions are alpha-equal if they have the same
# structure with variables renamed consistently.
function _alpha_eq(a::String, b::String) :: Bool
    a_parsed = MeTTaCore.from_sexpr(a)
    b_parsed = MeTTaCore.from_sexpr(b)
    _alpha_eq_val(a_parsed, b_parsed, Dict{Symbol,Symbol}(), Dict{Symbol,Symbol}())
end

function _alpha_eq_val(a, b, ab::Dict{Symbol,Symbol}, ba::Dict{Symbol,Symbol}) :: Bool
    a_is_var = a isa Symbol && startswith(string(a), "\$")
    b_is_var = b isa Symbol && startswith(string(b), "\$")
    if a_is_var && b_is_var
        # Both vars: check consistent renaming
        prev_ab = get(ab, a, nothing)
        prev_ba = get(ba, b, nothing)
        if prev_ab === nothing && prev_ba === nothing
            ab[a] = b; ba[b] = a; return true
        end
        return prev_ab === b && prev_ba === a
    end
    (a_is_var || b_is_var) && return false
    if a isa Vector && b isa Vector
        length(a) == length(b) || return false
        return all(i -> _alpha_eq_val(a[i], b[i], ab, ba), eachindex(a))
    end
    a == b
end

# ── State atoms (change-state!, get-state, new-state) ─────────────────────────
# Per MeTTa spec: mutable state via (State <value>) atom wrapper.
# States are atoms in the space; change-state! replaces the State atom.

"""
    _register_state_ops!()

🔴 REGISTERS NOTHING, DELIBERATELY (2026-07-29). Mutable state is not representable on this lane.

This used to register `new-state` / `get-state` / `change-state!` as string transforms, and all three
were unsound. Measured:

    new-state 42               -> "(State 42)"      a String, not a handle
    change-state! <that> 99    -> "(State 99)"      a NEW string; NOTHING is mutated
    get-state <that> AFTER     -> "42"              the STALE value
    get-state "no-such-handle" -> "no-such-handle"  echoes its argument back

The old `change-state!` said so itself — *"actual mutation via bind! in calling context"* — but this
lane has no `bind!`, so no caller ever performed the mutation. `get-state` on a non-State argument
fell through to `else s`, returning the argument unchanged.

Both violate LeaTTa's kernel-checked model of exactly this boundary
(`MettaHyperonFull/Core/MorkGroundedRegistry.lean`, proofs in `Proofs/MorkGroundedRegistry.lean`):

    structure Registry where live : Nat → Option Atom        -- handle id ⇒ CURRENT value
    theorem passesHandle_bound_same  -- a row holding the CURRENT live value passes
    theorem passesHandle_missing_handle : passesHandle … = false   -- a MISSING handle FAILS

A `String` cannot be a `HostHandle`: there is no identity to re-read, so `currentValue` can never
observe a mutation, and an unknown handle fails OPEN instead of closed.

WHY REMOVED RATHER THAN MADE TO DECLINE: a name that IS registered but returns `nothing` yields 0
paths from `GroundedSource`, and `isempty(result_paths) && break` (`MORK/src/kernel/Space.jl:556`)
then SILENTLY DROPS THE WHOLE JOIN ROW — no error, no warning. Leaving the name unregistered lets the
`I`-pattern fall through to an ordinary structural trie source, which is the honest "not implemented
here". Declining would have been quieter AND more wrong.

The working implementation is the interpreter's, over a genuinely mutable `StateCell`
(`Eval.jl:384`, a `mutable struct`) reached through the grounded-ATOM model — and
`mm2_is_relational` already keeps these heads on that lane. Restoring them here needs the atom-based
boundary (`expr_to_atom`), not another string transform.
"""
function _register_state_ops!()
    return nothing
end

# ── Type system ops ───────────────────────────────────────────────────────────
# get-type, type-cast, match-types — per MeTTa spec §Type System

function _register_type_ops!()
    # 🔴 `get-type` is NOT registered here — REMOVED 2026-07-29. It is unimplementable on this lane.
    #
    # `get-type` answers "what type is DECLARED for this atom", which means querying the SPACE for
    # `(: x T)` atoms. The interpreter's is a SpaceOp for exactly that reason:
    #     GET_TYPE = Grounded(SpaceOp("get-type", (xs, space) -> arg_actual_types(xs[1], space)))
    #                                                     ^^^^^  Eval.jl:2181
    # This shim receives a decoded STRING and has no space, so the old implementation guessed from
    # the argument's TEXT instead — which is `get-metatype`'s question, not `get-type`'s. Measured
    # divergence against the interpreter (the lane gated by hyperon-234 + the 21/21 type-system
    # conformance):
    #     (get-type True)  -> "Bool"        interpreter %Undefined%   (nothing is declared for True)
    #     (get-type (A B)) -> "Expression"  interpreter %Undefined%
    #     (get-type foo)   -> "Symbol"      interpreter %Undefined%
    # `%Undefined%` is the CORRECT answer for an undeclared atom; the shim's more-informative-looking
    # replies were a category error. Removed rather than made to decline, for the same reason as the
    # state ops: a registered name returning `nothing` yields 0 paths and
    # `isempty(result_paths) && break` (MORK Space.jl:556) drops the whole join row silently.
    # `mm2_is_relational` already keeps this head on the interpreter lane.

    # `get-metatype` DOES belong here — it asks only "which of the four grammar kinds is this atom",
    # needs no space, and the interpreter's is a pure `Operation` (Eval.jl:2043), so it can be
    # delegated. Doing so fixes `(get-metatype True)`: Core's `True` is a `Sym`, not a grounded Bool,
    # so the answer is Symbol — the old local copy said Grounded.
    MORK.register_grounded!("get-metatype", args -> _delegate_grounded("get-metatype", args))

    MORK.register_grounded!("match-types", args -> begin
        length(args) < 4 && return nothing
        t1, t2, yes, no = args[1], args[2], args[3], args[4]
        # Per MeTTa spec match_types:
        #   if t1 == %Undefined% or t1 == Atom or t2 == %Undefined% or t2 == Atom:
        #       return [bindings]
        #   else return match_atoms(t1, t2)
        # Five universal short-circuits (four meta-type cases + structural equality).
        matches = (t1 == "%Undefined%" || t1 == "Atom" ||
                   t2 == "%Undefined%" || t2 == "Atom" ||
                   t1 == t2)
        matches ? yes : no
    end)

    MORK.register_grounded!("type-cast", args -> begin
        # (type-cast atom type space) → atom if type matches, Error if not
        length(args) < 2 && return nothing
        atom, typ = args[1], args[2]
        inferred = begin
            s = strip(atom)
            tryparse(Int, s) !== nothing    ? "Number" :
            tryparse(Float64, s) !== nothing ? "Number" :
            (s == "True" || s == "False" || s == "true" || s == "false") ? "Bool" :
            startswith(s, "\"")            ? "String" :
            startswith(s, "(")             ? "Expression" : "Symbol"
        end
        (typ == "Atom" || typ == "%Undefined%" || typ == inferred) ? atom :
            "(Error $atom (BadType $typ $inferred))"
    end)

    MORK.register_grounded!("match-type-or", args -> begin
        length(args) < 3 && return "False"
        val, t1, t2 = args[1], args[2], args[3]
        (val == "True" && (t1 == "Bool" || t2 == "Bool")) ||
        (t1 == t2) ? "True" : val
    end)

    MORK.register_grounded!("first-from-pair", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            tokens = MeTTaCore._tokenise(s[2:end-1])
            isempty(tokens) ? nothing : tokens[1]
        else
            s
        end
    end)
end

# ── String / format ops ───────────────────────────────────────────────────────

function _register_format_ops!()
    MORK.register_grounded!("format-args", args -> begin
        length(args) < 2 && return isempty(args) ? "\"\"" : args[1]
        template = strip(args[1], ['"'])
        vals_s   = strip(args[2])
        vals = if startswith(vals_s, "(") && endswith(vals_s, ")")
            MeTTaCore._tokenise(vals_s[2:end-1])
        else
            [vals_s]
        end
        result = template
        for v in vals
            i = findfirst("{}", result)
            i === nothing && break
            result = result[1:first(i)-1] * v * result[last(i)+1:end]
        end
        "\"$result\""
    end)

    MORK.register_grounded!("str-concat", args -> begin
        "\"$(join(strip.(args, ['"']), ""))\""
    end)
end

# ── Nondeterministic set ops (superpose-based, not -atom suffix) ──────────────
# unique, union, intersection, subtraction operate on nondeterministic streams.
# In Core's string-based model, these work on the serialised result.

function _register_ndet_set_ops!()
    MORK.register_grounded!("unique", args -> begin
        isempty(args) && return nothing
        # In stream context each call returns one value; deduplicate in collapse
        args[1]
    end)

    # add-reduct: add an evaluated rule to the space
    # Distinct from add-atom — evaluates body before adding
    MORK.register_grounded!("add-reduct", args -> begin
        # (add-reduct &self (= (f) body)) → evaluates body, stores (= (f) <result>)
        # In Core's grounded context this is a hint — actual eval happens in eval_metta
        length(args) < 2 && return "()"
        "()"   # side-effect happens in the eval layer via add-atom
    end)
end

# ── Random ops (stubbed — need RNG resource) ─────────────────────────────────

function _register_random_ops!()
    MORK.register_grounded!("random-int", args -> begin
        length(args) < 2 && return "0"
        lo = tryparse(Int, args[end-1]); hi = tryparse(Int, args[end])
        (lo === nothing || hi === nothing) && return "0"
        string(rand(lo:hi))
    end)

    MORK.register_grounded!("random-float", args -> begin
        length(args) < 2 && return "0.0"
        lo = tryparse(Float64, args[end-1]); hi = tryparse(Float64, args[end])
        (lo === nothing || hi === nothing) && return "0.0"
        string(lo + rand() * (hi - lo))
    end)
end

# ── WILLIAM algorithm primitives ─────────────────────────────────────────────
# WILLIAM.lgg — Least-General Generalization via MORK's _au_merge! directly.
# Bypasses the exec/AUSink path (which needs an accumulating-sink fix) and
# calls the anti-unification algorithm directly on MORK byte arrays.
# Both arguments arrive as S-expression strings; result is serialised back.

function _register_metamo_primitives!()
    # MetaMo.blend-vec: implements equation #9 component-wise blend.
    # args = [alpha_str, current_vec_str, target_vec_str]
    # current/target are (G g1 g2 ...) or (M m1 m2 ...) atoms — tag preserved.
    # Returns a new atom of same type with blended numeric values.
    MORK.register_grounded!("MetaMo.blend-vec", args -> begin
        length(args) < 3 && return args[1]
        alpha = tryparse(Float64, args[1])
        alpha === nothing && return args[2]   # fallback: return current unchanged
        cur_s = strip(args[2]); tgt_s = strip(args[3])
        # Parse tagged vectors: (G 0.8 0.3) → tag="G", vals=[0.8, 0.3]
        if !startswith(cur_s, "(") || !startswith(tgt_s, "(")
            return args[2]
        end
        cur_toks = MeTTaCore._tokenise(cur_s[2:prevind(cur_s, lastindex(cur_s))])
        tgt_toks = MeTTaCore._tokenise(tgt_s[2:prevind(tgt_s, lastindex(tgt_s))])
        (isempty(cur_toks) || isempty(tgt_toks)) && return args[2]
        tag = cur_toks[1]   # preserve the G or M tag
        cur_nums = tryparse.(Float64, cur_toks[2:end])
        tgt_nums = tryparse.(Float64, tgt_toks[2:end])
        (any(isnothing, cur_nums) || any(isnothing, tgt_nums)) && return args[2]
        length(cur_nums) != length(tgt_nums) && return args[2]
        blended = [(1-alpha) * c + alpha * t
                   for (c, t) in zip(cur_nums, tgt_nums)]
        "($tag $(join(round.(blended, digits=6), " ")))"
    end)
end

function _register_william_primitives!()
    MORK.register_grounded!("WILLIAM.lgg", args -> begin
        length(args) < 2 && return "\$"
        a_str = args[1]; b_str = args[2]
        a_expr = try MORK.sexpr_to_expr(a_str) catch; return "\$" end
        b_expr = try MORK.sexpr_to_expr(b_str) catch; return "\$" end
        out = sizehint!(Vector{UInt8}(), max(length(a_expr.buf), length(b_expr.buf), 16))
        st  = MORK._AuState()
        MORK._au_merge!(a_expr.buf, 1, b_expr.buf, 1, out, st)
        try MORK.expr_serialize(out) catch; "\$" end
    end)
end

# ── Registration entry point ──────────────────────────────────────────────────

"""Register all built-in grounded primitives into MORK.GROUNDED_REGISTRY."""
function register_core_primitives!()
    _register_arithmetic!()
    _register_comparison!()
    _register_string_ops!()
    _register_type_checks!()
    # car/cdr/cons/size-atom are registered by AtomOps.jl (canonical) — the former
    # _register_list_ops!() duplicate here was dead (AtomOps wins). Removed 2026-06-10.
    _register_boolean_ops!()
    _register_math!()
    _register_vector_ops!()
    _register_repr!()
    _register_equality_ops!()
    # _register_state_ops! is a DELIBERATE NO-OP since 2026-07-29 — mutable state is not
    # representable as a string transform (it silently never mutated, and an unknown handle failed
    # OPEN). See its docstring for the measurements and LeaTTa's proved laws. Kept as a call so the
    # explanation is reachable from here; the working implementation is the interpreter's StateCell.
    _register_state_ops!()
    _register_type_ops!()
    _register_format_ops!()
    _register_ndet_set_ops!()
    _register_random_ops!()
    _register_william_primitives!()
    _register_metamo_primitives!()
end

export register_core_primitives!
