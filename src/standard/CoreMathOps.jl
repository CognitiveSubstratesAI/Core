# CoreMathOps.jl — the hyperon math library as grounded ops (sqrt/pow/abs/log/trunc/ceil/floor/round/
# sin/asin/cos/acos/tan/atan/isnan/isinf). ADDITIVE into TOKEN_REGISTRY (234/234 + unit corpus stay green;
# this only adds ops, touches no existing path). Faithful to hyperon-experimental
#   lib/src/metta/runner/stdlib/math.rs:
#   - sqrt/log/sin/asin/cos/acos/tan/atan  → ALWAYS Float (Rust Number::Float(input.f()))
#   - abs/trunc/ceil/floor/round           → PRESERVE type (Int→Int, Float→Float)
#   - isnan/isinf                          → True/False symbol (Int → False)
#   - pow                                  → Float; a too-big Integer power errors
# Minimal's Number `==` is loose (Atoms.jl:50: Grounded == compares .value), so (sqrt-math 4) == 2
# even though sqrt returns Float(2.0) — matching hyperon, whose own test asserts the same (math.rs:462).
# Domain errors: Rust f64 returns NaN for sqrt(-x)/asin(>1)/…; Julia THROWS DomainError, so the
# always-Float wrapper catches it → NaN (the corpus asserts (sqrt-math -4) is NaN). Error strings verbatim.

_mnum(a::Atom) = (a isa Grounded && a.value isa Number) ? a.value : nothing

# unary, always-Float (NaN on domain error, like Rust f64)
function _math_un_float(name, f, errmsg)
    Grounded(Operation(name, function (xs::Vector{Atom})
        (length(xs) == 1 && (x = _mnum(xs[1])) !== nothing) || return ExecRuntime(errmsg)
        r = try f(Float64(x)) catch e; e isa DomainError ? NaN : rethrow() end
        ExecOk(Atom[Grounded(r)])
    end))
end
# unary, PRESERVE type: Int → fi(Int), Float → ff(Float)
function _math_un_preserve(name, fi, ff, errmsg)
    Grounded(Operation(name, function (xs::Vector{Atom})
        (length(xs) == 1 && (x = _mnum(xs[1])) !== nothing) || return ExecRuntime(errmsg)
        ExecOk(Atom[Grounded(x isa Integer ? fi(x) : ff(Float64(x)))])
    end))
end
# unary, Bool: Int → False, Float → test(x)
function _math_un_bool(name, test, errmsg)
    Grounded(Operation(name, function (xs::Vector{Atom})
        (length(xs) == 1 && (x = _mnum(xs[1])) !== nothing) || return ExecRuntime(errmsg)
        ExecOk(Atom[(x isa Integer ? false : test(x)) ? Sym("True") : Sym("False")])
    end))
end

const SQRT_MATH = _math_un_float("sqrt-math", sqrt, "sqrt-math expects one argument: number")
const SIN_MATH  = _math_un_float("sin-math",  sin,  "sin-math expects one argument: input number")
const ASIN_MATH = _math_un_float("asin-math", asin, "asin-math expects one argument: input number")
const COS_MATH  = _math_un_float("cos-math",  cos,  "cos-math expects one argument: input number")
const ACOS_MATH = _math_un_float("acos-math", acos, "acos-math expects one argument: input number")
const TAN_MATH  = _math_un_float("tan-math",  tan,  "tan-math expects one argument: input number")
const ATAN_MATH = _math_un_float("atan-math", atan, "atan-math expects one argument: input number")

const ABS_MATH   = _math_un_preserve("abs-math",   abs,      abs,   "abs-math expects one argument: number")
const TRUNC_MATH = _math_un_preserve("trunc-math", identity, trunc, "trunc-math expects one argument: input number")
const CEIL_MATH  = _math_un_preserve("ceil-math",  identity, ceil,  "ceil-math expects one argument: input number")
const FLOOR_MATH = _math_un_preserve("floor-math", identity, floor, "floor-math expects one argument: input number")
const ROUND_MATH = _math_un_preserve("round-math", identity, round, "round-math expects one argument: input number")

const ISNAN_MATH = _math_un_bool("isnan-math", isnan, "isnan-math expects one argument: input number")
const ISINF_MATH = _math_un_bool("isinf-math", isinf, "isinf-math expects one argument: input number")

# pow-math (base power) → Float; a negative or > u32::MAX Integer power is rejected (Rust uses u32 int-pow).
const POW_MATH = Grounded(Operation("pow-math", function (xs::Vector{Atom})
    (length(xs) == 2 && (b = _mnum(xs[1])) !== nothing && (p = _mnum(xs[2])) !== nothing) ||
        return ExecRuntime("pow-math expects two arguments: number (base) and number (power)")
    (p isa Integer && (p < 0 || p > typemax(UInt32))) &&
        return ExecRuntime("power argument is too big, try using float value")
    ExecOk(Atom[Grounded(Float64(b) ^ Float64(p))])
end))
# log-math (base input) → Float; log_base(input) = log(input)/log(base)
const LOG_MATH = Grounded(Operation("log-math", function (xs::Vector{Atom})
    (length(xs) == 2 && (base = _mnum(xs[1])) !== nothing && (input = _mnum(xs[2])) !== nothing) ||
        return ExecRuntime("log-math expects two arguments: base (number) and input value (number)")
    r = try log(Float64(base), Float64(input)) catch e; e isa DomainError ? NaN : rethrow() end
    ExecOk(Atom[Grounded(r)])
end))

function _register_core_math_ops!()
    R = TOKEN_REGISTRY
    R["sqrt-math"]=SQRT_MATH;   R["pow-math"]=POW_MATH;     R["abs-math"]=ABS_MATH;   R["log-math"]=LOG_MATH
    R["trunc-math"]=TRUNC_MATH; R["ceil-math"]=CEIL_MATH;   R["floor-math"]=FLOOR_MATH; R["round-math"]=ROUND_MATH
    R["sin-math"]=SIN_MATH;     R["asin-math"]=ASIN_MATH;   R["cos-math"]=COS_MATH;   R["acos-math"]=ACOS_MATH
    R["tan-math"]=TAN_MATH;     R["atan-math"]=ATAN_MATH;   R["isnan-math"]=ISNAN_MATH; R["isinf-math"]=ISINF_MATH
end
_register_core_math_ops!()
