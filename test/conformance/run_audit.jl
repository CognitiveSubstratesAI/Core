# Core ↔ hyperon-experimental conformance harness.
# Runs hyperon reference scripts through Core, comparing each !(assert… tested expected)'s
# `tested` eval to `expected`. See docs/CONFORMANCE_AUDIT.md for the classified results.
#
#   HE_SCRIPTS=/path/to/hyperon-experimental/python/tests/scripts \
#     julia --project=. test/conformance/run_audit.jl
#
# NB: assertEqualToResult expects a result-SET (X); Core returns the single value X — the raw
# string compare flags GOT=X vs WANT=(X) as fail though Core is correct. Unwrap singleton sets
# for exact numbers (TODO). Reference scripts are not vendored; point HE_SCRIPTS at a local checkout.
using MeTTaCore
register_all_primitives!()
const DIR = get(ENV, "HE_SCRIPTS",
    joinpath(homedir(), "JuliaAGI/dev-zone/hyperon-experimental/python/tests/scripts"))
const ASS = ("assertEqual","assertEqualToResult","assertAlphaEqual","assertAlphaEqualToResult","assertNotEqual")
evalsx(x, s) = try; to_sexpr(eval_metta(x, s)); catch e; "ERR:"*first(split(sprint(showerror,e),'\n')); end
function audit(name)
    s = new_core_space(); load_stdlib!(s)
    path = joinpath(DIR, name*".metta")
    isfile(path) || (println(name, " MISSING (set HE_SCRIPTS)"); return (0,0))
    forms = try parse_metta(read(path, String)); catch e; println(name," PARSE-ERR ",e); return (0,0); end
    p = f = 0
    for fm in forms
        try
            if fm isa Vector && length(fm) >= 2 && fm[1] === Symbol("!")
                inner = fm[2]
                if inner isa Vector && !isempty(inner) && inner[1] isa Symbol && string(inner[1]) in ASS
                    got  = evalsx(inner[2], s)
                    want = occursin("ToResult", string(inner[1])) ? to_sexpr(inner[3]) : evalsx(inner[3], s)
                    ok = got == want; ok ? (p += 1) : (f += 1)
                    println("  [", ok ? "PASS" : "FAIL", "] ", to_sexpr(inner[2]), "  GOT=", got, "  WANT=", want)
                end
            else
                core_add!(s, fm)
            end
        catch e; println("  FORM-ERR ", first(split(sprint(showerror, e), '\n'))); end
    end
    println("## ", name, ": ", p, " pass / ", f, " fail"); (p, f)
end
SCRIPTS = get(ENV, "HE_AUDIT_SCRIPTS", "b0_chaining_prelim b1_equal_chain b2_backchain b3_direct b4_nondeterm b5_types_prelim")
for n in split(SCRIPTS); println("\n######## ", n, " ########"); audit(String(n)); end
