# Runs the CANONICAL test_metamo.jl assertions on the StandardMeTTa.Minimal evaluator instead of the
# legacy eval_metta/CoreSpace harness. Only the `qmm` harness is swapped (to tools/repl.jl's Minimal-
# backed `q`); every @test assertion is the file's own. The M5 bridge + 12-tick trajectory testsets use
# legacy to_sexpr serialization and are skipped here (guarded by MINIMAL_QMM) pending a Minimal serializer.
#
# Run:  julia --project=. test/test_metamo_minimal.jl
#   or: printf 'include("test/test_metamo_minimal.jl"); exit()\n' | julia --project=. -i tools/repl.jl
@isdefined(q) || include(joinpath(@__DIR__, "..", "tools", "repl.jl"))
lib!("metamo")                       # load the MetaMo library into the persistent Minimal space
const MINIMAL_QMM = true             # tells test_metamo.jl to use the injected qmm + skip legacy-only sets
qmm = q                              # Minimal-backed harness: query -> Julia values (via mval)
include(joinpath(@__DIR__, "test_metamo.jl"))
