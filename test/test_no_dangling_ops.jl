# test/test_no_dangling_ops.jl
#
# Structural lint (the dual of test_no_stdlib_shadow.jl): no lib/**/*.metta may CALL an op that the
# LIVE engine doesn't resolve but that *looks* available because it exists in the dead top-level
# stdlib/ (or is a known upstream-only stdlib name). This is the "ported-dangling primitive" class:
# a library inherits an op name from upstream (hyperon / metta-morph) that Core's live stdlib never
# defines, so the call silently stays unreduced — MeTTa does NOT error on an undefined op.
#
# How this slips through without the lint: green tests on the maintained path + algorithm/conformance
# comparisons never check op-RESOLUTION per library. Caught for real on 2026-06-30 in PLN
# (TupleConcat->append, Unique->list_to_set, Without->exclude-item — fixed to union-atom/unique-atom/
# subtraction-atom). This lint makes that check permanent.
#
# Precision: we only flag a called op that is BOTH (a) unresolved in the complete live op set AND
# (b) a known "should-be-a-function" name (a def in the dead stdlib/, or a curated metta-morph name).
# That excludes domain data constructors (mkInst, dtv, v2, …) which are meant to stay unreduced.
using Test

const _DOP_ROOT = normpath(joinpath(@__DIR__, ".."))
_dop_strip(t) = join((replace(ln, r";.*$" => "") for ln in split(t, '\n')), '\n')
const _DOP_HEAD = r"\(\s*([A-Za-z_][A-Za-z0-9_?!*<>./%=+-]*)"
const _DOP_DEFLHS = r"(?m)^\s*\(=\s*\(\s*([A-Za-z_][A-Za-z0-9_?!*<>./%=+-]*)"
_dop_heads(t) = Set(m.captures[1] for m in eachmatch(_DOP_HEAD, _dop_strip(t)))
_dop_deflhs(t) = Set(m.captures[1] for m in eachmatch(_DOP_DEFLHS, _dop_strip(t)))
function _dop_metta(dir)
    fs = String[]
    isdir(dir) || return fs
    for (r, _, files) in walkdir(dir), f in files
        endswith(f, ".metta") && push!(fs, joinpath(r, f))
    end
    fs
end

@testset "lint — no lib/ op calls a dangling (live-undefined, dead-stdlib/upstream-only) primitive" begin
    # (1) COMPLETE live op set. Crucial lesson: grounded ops are registered MANY ways (literal
    # register_grounded!("x"), Operation("x"), and LOOP tuples like CoreExtensions' (("exp",exp),…)).
    # So harvest every op-name-shaped quoted string from the primitive .jl files (over-inclusive on
    # purpose — better to under-report a dangle than to false-positive a constructor).
    grounded = Set{String}()
    for dir in ("src/primitives", "src/standard"),
        f in readdir(joinpath(_DOP_ROOT, dir); join=true)

        endswith(f, ".jl") || continue
        for m in eachmatch(r"\"([a-zA-Z][a-zA-Z0-9_?!*<>./%+-]*)\"", read(f, String))
            push!(grounded, m.captures[1])
        end
    end
    livestd = Set{String}()
    for f in readdir(joinpath(_DOP_ROOT, "src", "standard"); join=true)
        endswith(f, ".metta") && union!(livestd, _dop_deflhs(read(f, String)))
    end
    alllib = Set{String}()
    for f in _dop_metta(joinpath(_DOP_ROOT, "lib"))
        union!(alllib, _dop_deflhs(read(f, String)))
    end
    builtins = Set(["if", "let", "let*", "match", "case", "eval", "evalc", "chain",
        "function", "return",
        "unify", "quote", "superpose", "collapse", "sequential", "add-atom", "remove-atom",
        "get-atoms",
        "new-space", "bind!", "and", "or", "not", "sealed", "empty", "import!", "Error",
        "True", "False"])
    live = union(grounded, livestd, alllib, builtins)

    # (2) "should-have-resolved" reference: ops defined in the DEAD top-level stdlib/ (look available,
    # engine never loads them) + curated upstream-only names ports have used.
    deadup = Set{String}()
    for f in (
        if isdir(joinpath(_DOP_ROOT, "stdlib"))
            readdir(joinpath(_DOP_ROOT, "stdlib"); join=true)
        else
            String[]
        end
    )
        endswith(f, ".metta") && union!(deadup, _dop_deflhs(read(f, String)))
    end
    union!(deadup, Set(["list_to_set", "exclude-item", "append"]))

    offenders = Dict{String, Vector{String}}()
    for f in _dop_metta(joinpath(_DOP_ROOT, "lib"))
        for op in _dop_heads(read(f, String))
            (op in live) && continue          # resolves live → fine
            (op in deadup) || continue        # not a known function name → a domain constructor → fine
            push!(get!(offenders, op, String[]), relpath(f, _DOP_ROOT))
        end
    end
    for (op, fs) in offenders
        @warn "lib/ calls a DANGLING primitive (undefined in the live engine; exists only in dead stdlib/ or upstream) — reuse the live grounded op instead" op=op files=unique(
            fs
        )
    end
    @test isempty(offenders)
end
