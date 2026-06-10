"""
AtomOps — grounded atom/expression operations for Core.

Per MeTTa spec + cross-verified against Mettatron (eval/mod.rs), CeTTa
(grounded.c), and hyperon-experimental (stdlib/atom.rs):

These operations MUST be grounded (not pure MeTTa) because they:
  - Operate on the structural representation of atoms
  - Control evaluation order (foldl-atom, map-atom, filter-atom)
  - Are tied to the host language's data model (cons, car, cdr)
  - Require access to the evaluator's call mechanism (map/filter need
    to call back into eval_metta for each element)

Names follow hyperon-experimental / MeTTa spec (with -atom suffix).
"""

function _register_atom_ops!(eval_fn::Function)
    # ── Expression construction / deconstruction ──────────────────────────────
    # Spec: cons-atom, decons-atom, car-atom, cdr-atom, size-atom, index-atom

    MORK.register_grounded!("cons-atom", args -> begin
        length(args) < 2 && return nothing
        head = args[1]
        tail = strip(args[2])
        tail == "()" && return "($head)"
        startswith(tail, "(") ? "($head $(tail[2:end-1]))" : "($head $tail)"
    end)

    MORK.register_grounded!("decons-atom", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            tokens = MeTTaCore._tokenise(s[2:end-1])
            isempty(tokens) && return nothing
            head = tokens[1]
            tail = length(tokens) == 1 ? "()" : "($(join(tokens[2:end], " ")))"
            return "($head $tail)"
        end
        nothing
    end)

    MORK.register_grounded!("car-atom", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            tokens = MeTTaCore._tokenise(s[2:end-1])
            isempty(tokens) ? nothing : tokens[1]
        else
            s
        end
    end)

    MORK.register_grounded!("cdr-atom", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            tokens = MeTTaCore._tokenise(s[2:end-1])
            length(tokens) <= 1 ? "()" : "($(join(tokens[2:end], " ")))"
        else
            "()"
        end
    end)

    MORK.register_grounded!("size-atom", args -> begin
        isempty(args) && return "0"
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            string(length(MeTTaCore._tokenise(s[2:end-1])))
        else
            "1"
        end
    end)

    MORK.register_grounded!("take-atom", args -> begin
        length(args) < 2 && return "()"
        list_s = strip(args[1])
        n = tryparse(Int, args[2])
        n === nothing && return list_s
        if startswith(list_s, "(") && endswith(list_s, ")")
            tokens = MeTTaCore._tokenise(list_s[2:end-1])
            "($(join(tokens[1:min(n, length(tokens))], " ")))"
        else
            n > 0 ? list_s : "()"
        end
    end)

    MORK.register_grounded!("drop-atom", args -> begin
        length(args) < 2 && return "()"
        list_s = strip(args[1])
        n = tryparse(Int, args[2])
        n === nothing && return list_s
        if startswith(list_s, "(") && endswith(list_s, ")")
            tokens = MeTTaCore._tokenise(list_s[2:end-1])
            "($(join(tokens[n+1:end], " ")))"
        else
            "()"
        end
    end)

    MORK.register_grounded!("index-atom", args -> begin
        length(args) < 2 && return nothing
        s   = strip(args[1])
        idx = tryparse(Int, args[2])
        idx === nothing && return nothing
        if startswith(s, "(") && endswith(s, ")")
            tokens = MeTTaCore._tokenise(s[2:end-1])
            (idx < 0 || idx >= length(tokens)) && return "(Error (index-atom) IndexOutOfBounds)"
            tokens[idx + 1]   # 0-based index per MeTTa spec
        else
            idx == 0 ? s : "(Error (index-atom) IndexOutOfBounds)"
        end
    end)

    MORK.register_grounded!("min-atom", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            nums = filter(!isnothing, tryparse.(Float64, MeTTaCore._tokenise(s[2:end-1])))
            isempty(nums) && return nothing
            r = minimum(nums)
            isinteger(r) ? string(Int(r)) : string(r)
        else
            args[1]
        end
    end)

    MORK.register_grounded!("max-atom", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            nums = filter(!isnothing, tryparse.(Float64, MeTTaCore._tokenise(s[2:end-1])))
            isempty(nums) && return nothing
            r = maximum(nums)
            isinteger(r) ? string(Int(r)) : string(r)
        else
            args[1]
        end
    end)

    # ── Higher-order list operations (need eval callback) ─────────────────────
    # Spec: foldl-atom, map-atom, filter-atom
    # These call back into the evaluator — hence grounded, not pure MeTTa.
    # Signature: (foldl-atom $list $init $acc $elem $body)
    #            (map-atom   $list $var  $body)
    #            (filter-atom $list $var $pred-body)

    MORK.register_grounded!("foldl-atom", args -> begin
        # args = [list_str, init_str, acc_var_str, elem_var_str, body_str]
        length(args) < 5 && return nothing
        list_s = strip(args[1])
        items  = if startswith(list_s, "(") && endswith(list_s, ")")
            MeTTaCore._tokenise(list_s[2:end-1])
        else
            isempty(list_s) || list_s == "()" ? String[] : [list_s]
        end
        acc    = args[2]   # initial accumulator value (string)
        acc_v  = args[3]   # accumulator variable name (e.g. "__var_acc")
        elem_v = args[4]   # element variable name (e.g. "__var_x")
        body   = args[5]   # body template (string)

        result = acc
        for item in items
            # Substitute acc_v and elem_v in body, then eval
            bound = replace(replace(body, acc_v => result), elem_v => item)
            result = eval_fn(bound)
        end
        result
    end)

    MORK.register_grounded!("map-atom", args -> begin
        length(args) < 3 && return nothing
        list_s = strip(args[1])
        items  = if startswith(list_s, "(") && endswith(list_s, ")")
            MeTTaCore._tokenise(list_s[2:end-1])
        else
            isempty(list_s) || list_s == "()" ? String[] : [list_s]
        end
        var_s  = args[2]
        body   = args[3]
        results = [eval_fn(replace(body, var_s => item)) for item in items]
        "($(join(results, " ")))"
    end)

    MORK.register_grounded!("filter-atom", args -> begin
        length(args) < 3 && return nothing
        list_s = strip(args[1])
        items  = if startswith(list_s, "(") && endswith(list_s, ")")
            MeTTaCore._tokenise(list_s[2:end-1])
        else
            isempty(list_s) || list_s == "()" ? String[] : [list_s]
        end
        var_s = args[2]
        body  = args[3]
        kept  = filter(items) do item
            r = eval_fn(replace(body, var_s => item))
            r == "True" || r == "true"
        end
        "($(join(kept, " ")))"
    end)

    # ── Set operations ─────────────────────────────────────────────────────────
    # Per Mettatron set.rs and hyperon stdlib

    MORK.register_grounded!("unique-atom", args -> begin
        isempty(args) && return "()"
        s = strip(args[1])
        tokens = if startswith(s, "(") && endswith(s, ")")
            MeTTaCore._tokenise(s[2:end-1])
        else
            [s]
        end
        "($(join(unique(tokens), " ")))"
    end)

    MORK.register_grounded!("union-atom", args -> begin
        length(args) < 2 && return "()"
        t1 = startswith(strip(args[1]), "(") ? MeTTaCore._tokenise(strip(args[1])[2:end-1]) : [args[1]]
        t2 = startswith(strip(args[2]), "(") ? MeTTaCore._tokenise(strip(args[2])[2:end-1]) : [args[2]]
        "($(join(unique(vcat(t1, t2)), " ")))"
    end)

    MORK.register_grounded!("intersection-atom", args -> begin
        length(args) < 2 && return "()"
        t1 = startswith(strip(args[1]), "(") ? MeTTaCore._tokenise(strip(args[1])[2:end-1]) : [args[1]]
        t2 = Set(startswith(strip(args[2]), "(") ? MeTTaCore._tokenise(strip(args[2])[2:end-1]) : [args[2]])
        "($(join(filter(x -> x ∈ t2, t1), " ")))"
    end)

    MORK.register_grounded!("subtraction-atom", args -> begin
        length(args) < 2 && return "()"
        t1 = startswith(strip(args[1]), "(") ? MeTTaCore._tokenise(strip(args[1])[2:end-1]) : [args[1]]
        t2 = Set(startswith(strip(args[2]), "(") ? MeTTaCore._tokenise(strip(args[2])[2:end-1]) : [args[2]])
        "($(join(filter(x -> x ∉ t2, t1), " ")))"
    end)

    # ── Collapse / Superpose (evaluator-tied, must be grounded) ───────────────
    # Per spec §"Special Function Results" and all 4 references.
    # collapse gathers all nondeterministic results into a list.
    # superpose distributes a list as nondeterministic results.
    # Here implemented as string-level for MORK exec-atom context.

    MORK.register_grounded!("collapse", args -> begin
        isempty(args) && return "()"
        # In exec-atom context, result is already a single value string
        "($(args[1]))"
    end)

    MORK.register_grounded!("superpose", args -> begin
        isempty(args) && return nothing
        s = strip(args[1])
        if startswith(s, "(") && endswith(s, ")")
            items = MeTTaCore._tokenise(s[2:end-1])
            isempty(items) ? nothing : items
        else
            [s]
        end
    end)

    # ── Type predicates ────────────────────────────────────────────────────────
    # NOTE: get-metatype is registered in Primitives.jl _register_type_ops!.
    # An older duplicate registration here overrode the more-complete version
    # (no True/False → Grounded). Removed 2026-05-29.

    MORK.register_grounded!("is-number", args -> begin
        isempty(args) && return "False"
        tryparse(Float64, strip(args[1])) !== nothing ? "True" : "False"
    end)

    MORK.register_grounded!("is-symbol", args -> begin
        isempty(args) && return "False"
        s = strip(args[1])
        !startswith(s, "(") && !startswith(s, "\$") &&
            tryparse(Float64, s) === nothing ? "True" : "False"
    end)

    MORK.register_grounded!("is-variable", args -> begin
        isempty(args) && return "False"
        # Variables arrive as parse-time `$x` or eval-renamed `__var_x`.
        s = strip(args[1])
        (startswith(s, "\$") || startswith(s, "__var_")) ? "True" : "False"
    end)

    MORK.register_grounded!("is-expression", args -> begin
        isempty(args) && return "False"
        startswith(strip(args[1]), "(") ? "True" : "False"
    end)

    MORK.register_grounded!("empty", _args -> nothing)
end

export _register_atom_ops!
