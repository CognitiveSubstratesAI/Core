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
"""

# ── Arithmetic ────────────────────────────────────────────────────────────────

function _register_arithmetic!()
    for (name, op) in [("+", +), ("-", -), ("*", *), ("/", /), ("%", rem)]
        MORK.register_grounded!(name, args -> begin
            length(args) < 2 && return nothing
            a = tryparse(Float64, args[1]); b = tryparse(Float64, args[2])
            (a === nothing || b === nothing) && return nothing
            r = op(a, b)
            isinteger(r) ? string(Int(r)) : string(r)
        end)
    end
end

# ── Comparison ────────────────────────────────────────────────────────────────

function _register_comparison!()
    for (name, op) in [("<", <), (">", >), ("<=", <=), (">=", >=), ("==", ==)]
        MORK.register_grounded!(name, args -> begin
            length(args) < 2 && return nothing
            a = tryparse(Float64, args[1]); b = tryparse(Float64, args[2])
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

function _register_math!()
    for (name, fn) in [
        ("sqrt-math", sqrt), ("abs-math",   abs),
        ("log-math",  log),  ("exp-math",   exp),
        ("floor-math", floor), ("ceil-math", ceil),
        ("round-math", round), ("trunc-math", trunc),
        ("sin-math",  sin),  ("cos-math",  cos),  ("tan-math",  tan),
        ("asin-math", asin), ("acos-math", acos), ("atan-math", atan),
    ]
        local _fn = fn
        MORK.register_grounded!(name, args -> begin
            isempty(args) && return nothing
            x = tryparse(Float64, args[1])
            x === nothing && return nothing
            r = _fn(x)
            isinteger(r) ? string(Int(r)) : string(r)
        end)
    end
    MORK.register_grounded!("pow-math", args -> begin
        length(args) < 2 && return nothing
        b = tryparse(Float64, args[1]); e = tryparse(Float64, args[2])
        (b === nothing || e === nothing) && return nothing
        string(b ^ e)
    end)
    MORK.register_grounded!("isnan-math", args -> begin
        isempty(args) && return "False"
        x = tryparse(Float64, args[1])
        x !== nothing && isnan(x) ? "True" : "False"
    end)
    MORK.register_grounded!("isinf-math", args -> begin
        isempty(args) && return "False"
        x = tryparse(Float64, args[1])
        x !== nothing && isinf(x) ? "True" : "False"
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
    a_is_var || b_is_var && return false
    if a isa Vector && b isa Vector
        length(a) == length(b) || return false
        return all(i -> _alpha_eq_val(a[i], b[i], ab, ba), eachindex(a))
    end
    a == b
end

# ── State atoms (change-state!, get-state, new-state) ─────────────────────────
# Per MeTTa spec: mutable state via (State <value>) atom wrapper.
# States are atoms in the space; change-state! replaces the State atom.

function _register_state_ops!()
    MORK.register_grounded!("new-state", args -> begin
        init = isempty(args) ? "()" : join(args, " ")
        "(State $init)"
    end)

    MORK.register_grounded!("get-state", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(State ") && endswith(s, ")")
            strip(s[8:end-1])
        else
            s
        end
    end)

    MORK.register_grounded!("change-state!", args -> begin
        length(args) < 2 && return nothing
        # Return new State atom; actual mutation via bind! in calling context
        "(State $(args[2]))"
    end)
end

# ── Type system ops ───────────────────────────────────────────────────────────
# get-type, type-cast, match-types — per MeTTa spec §Type System

function _register_type_ops!()
    MORK.register_grounded!("get-type", args -> begin
        isempty(args) && return "%Undefined%"
        s = strip(args[1])
        # Grounded type inference from value
        tryparse(Int, s) !== nothing    && return "Number"
        tryparse(Float64, s) !== nothing && return "Number"
        (s == "True" || s == "False" || s == "true" || s == "false") && return "Bool"
        startswith(s, "\"")            && return "String"
        startswith(s, "(")             && return "Expression"
        startswith(s, "\$")            && return "Variable"
        "Symbol"
    end)

    MORK.register_grounded!("get-metatype", args -> begin
        isempty(args) && return "Symbol"
        s = strip(args[1])
        # Variables arrive either as parse-time `$x` or eval-renamed `__var_x`.
        (startswith(s, "\$") || startswith(s, "__var_")) && return "Variable"
        startswith(s, "(")   && return "Expression"
        tryparse(Float64, s) !== nothing && return "Grounded"
        (s == "True" || s == "False" || s == "true" || s == "false") && return "Grounded"
        "Symbol"
    end)

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
        isempty(cur_toks) || isempty(tgt_toks) && return args[2]
        tag = cur_toks[1]   # preserve the G or M tag
        cur_nums = tryparse.(Float64, cur_toks[2:end])
        tgt_nums = tryparse.(Float64, tgt_toks[2:end])
        any(isnothing, cur_nums) || any(isnothing, tgt_nums) && return args[2]
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
    _register_state_ops!()
    _register_type_ops!()
    _register_format_ops!()
    _register_ndet_set_ops!()
    _register_random_ops!()
    _register_william_primitives!()
    _register_metamo_primitives!()
end

export register_core_primitives!
