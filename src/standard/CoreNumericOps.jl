# ── Core grounded numeric ops — the MeTTa↔Julia numeric ADAPTER ──────────────────────────────────────
# NOT a numpy reimplementation. Base Julia (broadcasting / reductions) IS the numerics. This file is the
# thin grounded-op adapter that marshals MeTTa atoms ↔ Julia arrays and encodes upstream's conventions
# (ddof=0, rounding) so the answers match numpy's, not the platonic ideal. The numeric expression in each
# op is one line; the marshalling (atom-unwrap → native-call → atom-rewrap, bad-arg → ExecNoReduce) is the
# layer. Spec + conformance: docs/CORE_NUMERIC_BACKEND_SPEC.md + MetaMo core/tests/helpers_test.metta.
# Additive into Minimal's TOKEN_REGISTRY (the 234/234 matrix must stay green with this loaded).
# Mirrors upstream MetaMo helpers.py (the numpy `py-call` surface) so the ports drop py-call for these ops.

# ── marshalling shim (the actual content; numerics in the closures are trivial) ──
_cno_fvec(a::Atom) = begin                      # Expression of Grounded numbers → Vector{Float64}, else nothing
    a isa Expression || return nothing
    v = Vector{Float64}(undef, length(a.children))
    @inbounds for (i, c) in enumerate(a.children)
        (c isa Grounded && c.value isa Number) || return nothing
        v[i] = Float64(c.value)
    end
    v
end
_cno_num(a::Atom) = (a isa Grounded && a.value isa Number) ? Float64(a.value) : nothing
_cno_int(a::Atom) = (a isa Grounded && a.value isa Number && isinteger(a.value)) ? Int(a.value) : nothing
_cno_wrapv(v) = Expression(Atom[Grounded(Float64(x)) for x in v])     # Vector → Expression of Grounded
# op of fixed arity; the closure unwraps + computes + wraps, returning `nothing` on any bad arg → ExecNoReduce
function _cno(name, n, fn)
    Grounded(Operation(name, function (xs::Vector{Atom})
        length(xs) == n || return ExecNoReduce()
        r = fn(xs)
        r === nothing ? ExecNoReduce() : ExecOk(Atom[r])
    end))
end

# ── conventions encoded here (NOT defaults) — see spec §3 ──
#   variance/std: population (ddof=0)  ·  std: round-2  ·  vectorAdd: round-8  ·  indices: 0-based
_cno_mean(v) = sum(v) / length(v)
_cno_var(v)  = (m = _cno_mean(v); sum(abs2, v .- m) / length(v))      # population denominator N

function _register_core_numeric_ops!()
    R = TOKEN_REGISTRY
    # vec → scalar
    R["norm"]     = _cno("norm", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing ? nothing : Grounded(isempty(v) ? 0.0 : sqrt(sum(abs2, v)))))
    R["sum"]      = _cno("sum", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing ? nothing : Grounded(sum(v; init=0.0))))
    R["product"]  = _cno("product", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing ? nothing : Grounded(prod(v; init=1.0))))
    R["mean"]     = _cno("mean", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing||isempty(v) ? (v===nothing ? nothing : Grounded(0.0)) : Grounded(_cno_mean(v))))
    R["variance"] = _cno("variance", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing||isempty(v) ? (v===nothing ? nothing : Grounded(0.0)) : Grounded(_cno_var(v))))
    R["std"]      = _cno("std", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing||isempty(v) ? (v===nothing ? nothing : Grounded(0.0)) : Grounded(round(sqrt(_cno_var(v)); digits=2))))
    # (vec,vec) → scalar
    R["calculateNormDifference"] = _cno("calculateNormDifference", 2, xs -> (a=_cno_fvec(xs[1]); b=_cno_fvec(xs[2]); (a===nothing||b===nothing||length(a)!=length(b)) ? nothing : Grounded(sum(abs2, a .- b; init=0.0))))
    R["dotProduct"] = _cno("dotProduct", 2, xs -> (a=_cno_fvec(xs[1]); b=_cno_fvec(xs[2]); (a===nothing||b===nothing||length(a)!=length(b)) ? nothing : Grounded(isempty(a) ? 0.0 : sum(a .* b))))
    # (vec,vec) → vec
    R["listDifference"] = _cno("listDifference", 2, xs -> (a=_cno_fvec(xs[1]); b=_cno_fvec(xs[2]); (a===nothing||b===nothing||length(a)!=length(b)) ? nothing : _cno_wrapv(a .- b)))
    R["vectorAdd"]      = _cno("vectorAdd", 2, xs -> (a=_cno_fvec(xs[1]); b=_cno_fvec(xs[2]); (a===nothing||b===nothing||length(a)!=length(b)) ? nothing : _cno_wrapv(round.(a .+ b; digits=8))))
    R["averageArrays"]  = _cno("averageArrays", 2, xs -> (a=_cno_fvec(xs[1]); b=_cno_fvec(xs[2]); (a===nothing||b===nothing||length(a)!=length(b)) ? nothing : _cno_wrapv((a .+ b) ./ 2)))
    # vec → vec
    R["normalizeVector"] = _cno("normalizeVector", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing ? nothing : (n=(isempty(v) ? 0.0 : sqrt(sum(abs2,v))); _cno_wrapv(n>0 ? v ./ n : v))))
    R["softmax"] = _cno("softmax", 1, xs -> (v=_cno_fvec(xs[1]); v===nothing ? nothing : (isempty(v) ? _cno_wrapv(Float64[]) : (e=exp.(v .- maximum(v)); s=sum(e); _cno_wrapv(s==0 ? Float64[] : e ./ s)))))
    # (vec, scalar…) → vec
    R["scaleArray"] = _cno("scaleArray", 2, xs -> (v=_cno_fvec(xs[1]); s=_cno_num(xs[2]); (v===nothing||s===nothing) ? nothing : _cno_wrapv(v .* s)))
    R["clipVector"] = _cno("clipVector", 3, xs -> (v=_cno_fvec(xs[1]); lo=_cno_num(xs[2]); hi=_cno_num(xs[3]); (v===nothing||lo===nothing||hi===nothing) ? nothing : _cno_wrapv(clamp.(v, lo, hi))))
    R["roundList"]  = _cno("roundList", 2, xs -> (v=_cno_fvec(xs[1]); d=_cno_int(xs[2]); (v===nothing||d===nothing) ? nothing : _cno_wrapv(round.(v; digits=d))))
    # scalar → scalar
    R["positivePart"]  = _cno("positivePart", 1, xs -> (x=_cno_num(xs[1]); x===nothing ? nothing : Grounded(max(0.0, x))))
    R["sigmoidNumber"] = _cno("sigmoidNumber", 1, xs -> (x=_cno_num(xs[1]); x===nothing ? nothing : Grounded(1.0/(1.0+exp(-x)))))
    R["absNumber"]     = _cno("absNumber", 1, xs -> (x=_cno_num(xs[1]); x===nothing ? nothing : Grounded(abs(x))))
    R["expNumber"]     = _cno("expNumber", 1, xs -> (x=_cno_num(xs[1]); x===nothing ? nothing : Grounded(exp(x))))
    R["roundNum"]      = _cno("roundNum", 2, xs -> (x=_cno_num(xs[1]); d=_cno_int(xs[2]); (x===nothing||d===nothing) ? nothing : Grounded(round(x; digits=d))))
    # (vec, index-vec) → scalar  ·  0-based indices (numpy)
    R["meanAtIndices"] = _cno("meanAtIndices", 2, xs -> begin
        v=_cno_fvec(xs[1]); (v===nothing) && return nothing
        (xs[2] isa Expression) || return nothing
        idx = Int[]; for c in xs[2].children; (c isa Grounded && c.value isa Number && isinteger(c.value)) || return nothing; push!(idx, Int(c.value)); end
        isempty(idx) && return Grounded(0.0)
        all(i -> 0 <= i < length(v), idx) || return nothing
        Grounded(sum(v[i+1] for i in idx) / length(idx))
    end)
    return nothing
end
_register_core_numeric_ops!()
