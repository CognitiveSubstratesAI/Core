# Runs the CANONICAL test_moses.jl assertions on the MeTTaCore.Interpreter evaluator instead of the
# legacy eval_metta/CoreSpace harness. Only the `qm` harness is swapped (to tools/repl.jl's Minimal-
# backed `q`); every @test assertion is test_moses.jl's own. The MOSES library is loaded via the
# self-resolving import! loader. No legacy-only serialization testsets exist in test_moses.jl (the
# heavy runMoses full-learn is out-of-band/commented), so nothing is skipped here — a clean parametric
# run of all assertions on Minimal.
#
# Run:  julia --project=. test/test_moses_minimal.jl
#   or: printf 'include("test/test_moses_minimal.jl"); exit()\n' | julia --project=. -i tools/repl.jl
@isdefined(q) || include(joinpath(@__DIR__, "..", "tools", "repl.jl"))
lib!("MOSES")                        # load the MOSES library into the persistent Minimal space
const MINIMAL_QMM = true             # tells test_moses.jl to use the injected qm + skip legacy setup
qm = q                               # Interpreter-backed harness: query -> Julia values (via mval)
include(joinpath(@__DIR__, "test_moses.jl"))
