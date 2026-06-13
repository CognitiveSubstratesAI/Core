# ── Core grounded extensions ──────────────────────────────────────────────────
# Grounded ops that Core's algorithm libraries (MetaMo, MOSES, …) need but that are NOT part of
# hyperon's stdlib. Everything ABOVE in Minimal.jl + stdlib.metta is the hyperon-FAITHFUL core;
# 234/234 conformance is defined against it. This file augments `TOKEN_REGISTRY` ADDITIVELY — it
# only registers NEW operator names, never modifies the faithful set.
#
# INVARIANT (the gate that keeps "Minimal = faithful core + Core extensions" honest): the full
# 26-script conformance matrix must stay 234/234 with this file loaded. The conformance scripts
# never call these ops, so registering them is provably non-invasive — re-run the matrix to prove it.
#
# As further libraries migrate onto the Minimal evaluator, their grounded ops (MetaMo.blend-vec,
# WILLIAM.lgg, the MOSES set, …) register HERE, keeping the faithful core uncontaminated.

# Numeric leaf ops (bare names). Legacy Core exposes the unary ones as `<f>-math` in Primitives.jl
# with a bare→-math rule layer on top; here they are bare grounded ops directly.
_ext_isnum(a::Atom) = a isa Grounded && a.value isa Number
function _ext_unop(name, f)
    Grounded(Operation(name, function (xs::Vector{Atom})
        (length(xs) == 1 && _ext_isnum(xs[1])) || return ExecNoReduce()
        ExecOk(Atom[Grounded(f(xs[1].value))])
    end))
end
function _ext_binop(name, f)
    Grounded(Operation(name, function (xs::Vector{Atom})
        (length(xs) == 2 && _ext_isnum(xs[1]) && _ext_isnum(xs[2])) || return ExecNoReduce()
        ExecOk(Atom[Grounded(f(xs[1].value, xs[2].value))])
    end))
end
const CLAMP = Grounded(Operation("clamp", function (xs::Vector{Atom})
    (length(xs) == 3 && all(_ext_isnum, xs)) || return ExecNoReduce()
    ExecOk(Atom[Grounded(clamp(xs[1].value, xs[2].value, xs[3].value))])
end))

# Register the Core extensions into the shared TOKEN_REGISTRY (additive — see invariant above).
function _register_core_extensions!()
    for (n, f) in (("exp", exp), ("log", log), ("sqrt", sqrt), ("abs", abs), ("floor", floor), ("ceil", ceil))
        TOKEN_REGISTRY[n] = _ext_unop(n, f)
    end
    for (n, f) in (("max", max), ("min", min), ("pow", ^))
        TOKEN_REGISTRY[n] = _ext_binop(n, f)
    end
    TOKEN_REGISTRY["clamp"] = CLAMP
    return nothing
end
_register_core_extensions!()
