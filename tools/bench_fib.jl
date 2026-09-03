# bench_fib.jl — THE tabled/untabled fib benchmark. Cite this script in any perf claim.
#
# ─── WHY THIS EXISTS ─────────────────────────────────────────────────────────────────────────────
# 2026-09-03 produced FIVE wrong performance numbers before one right one, and every one looked like
# a result:
#   1. cross-day        — compared against CODEMAP row 233's 08-29 figures. Attributes nothing.
#   2. unwarmed         — 28.6s/3.97s first-call, would have been reported as a 9x REGRESSION.
#   3. wrong field      — guessed `evaluated`; `compile_run` returns `answers`. Every run said
#                         `<none>`, so 20.7s timed a computation nobody confirmed produced 987.
#   4. both arms one tree — a `cd` the second invocation inherited; would have printed a convincing
#                         "no difference" from a comparison that never happened.
#   5. script never written — its heredoc was inside a command a hook blocked, so both arms failed
#                         identically on a missing file.
# And a 6th, reported and retracted: "Core is 14x slower than PeTTa on tabled fib" — Core-COLD vs
# PeTTa-at-steady-state. Warm, Core does tabled fib(30) in 0.08s against PeTTa's 0.35s.
#
# ⇒ the repo-owned form of a perf check, the way `tools/lib_decline_survey.jl` is for coverage.
# It WARMS, VERIFIES THE ANSWER against a BigInt reference, runs N times, reports MIN AND SPREAD,
# and prints the TREE IDENTITY so an A/B cannot silently measure one side twice.
#
# Usage:  bash tools/run_tests.sh tools/bench_fib.jl
#         BENCH_RUNS=5 BENCH_TABLED_N=2000 BENCH_UNTABLED_N=20 bash tools/run_tests.sh tools/bench_fib.jl
using MeTTaCore
using MeTTaCore.Eval

const RUNS        = parse(Int, get(ENV, "BENCH_RUNS", "5"))
# 🔴 WHY 90 AND NOT 2000. MEASURED 2026-09-03, and the BigInt reference below is what caught it:
#   * fib(93)+ returns a WRONG ANSWER SILENTLY — Core's MeTTa arithmetic is Int64-backed and
#     overflows without error or promotion. fib(93) comes back as -6246583658587674878.
#     fib(92) is the last correct value.
#   * fib(2000) tabled dies with StackOverflowError — even tabled, the first evaluation recurses
#     2000 levels and something on that path is genuinely Julia-stack-recursive, despite
#     `Eval.jl`'s "deep MeTTa recursion grows the heap plan, not the Julia stack".
# ⇒ a benchmark above 92 times a WRONG answer at speed, which is worse than timing nothing.
const TABLED_N    = parse(Int, get(ENV, "BENCH_TABLED_N", "90"))
# 🔴 16, NOT 20. MEASURED: untabled fib(20) burns 23s and returns <EMPTY> — it exhausts the
# interpret step budget (`_INTERPRET_MAX`, default 512_000) and `compile_run` surfaces that in
# `exhausted` rather than throwing. fib(16) fits and returns 987. A benchmark of an exhausted run
# is a clean-looking measurement of nothing.
const UNTABLED_N  = parse(Int, get(ENV, "BENCH_UNTABLED_N", "16"))

_prog(n) = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n!(fib $n)\n"

"Reference value, computed here in BigInt — never typed. A wrong answer must fail the bench."
function _ref(n::Int)
    a, b = big(0), big(1)
    for _ in 1:n; a, b = b, a + b; end
    a
end

"Answer string from `compile_run`'s return — the field is `answers`, read from CompileLane."
function _answer(r)::String
    isempty(r.answers) && return "<EMPTY>"
    v = last(first(r.answers))
    isempty(v) ? "<EMPTY>" : String(first(v))
end

function bench(label::String, n::Int, at::Bool)
    MeTTaCore.compile_run(_prog(10); auto_table=at)          # WARMUP — discarded. Never time a first call.
    want = string(_ref(n))
    ts, got = Float64[], ""
    r_last = nothing
    for _ in 1:RUNS
        r = nothing
        push!(ts, @elapsed (r = MeTTaCore.compile_run(_prog(n); auto_table=at)))
        got = _answer(r); r_last = r
    end
    exh = try isempty(r_last.exhausted) ? "" : "  ⚠️ EXHAUSTED=$(length(r_last.exhausted))" catch; "" end
    ok = got == want
    spread = maximum(ts) / max(minimum(ts), eps())
    println("  ", rpad(label, 22),
        " min=", rpad(string(round(minimum(ts); digits=4)), 9),
        " max=", rpad(string(round(maximum(ts); digits=4)), 9),
        " spread=", round(spread; digits=2), "x",
        ok ? "  ANSWER OK" : "  🔴 ANSWER WRONG got=$(first(got,18)) want=$(first(want,18))", exh)
    (; min=minimum(ts), spread, ok)
end

# TREE IDENTITY — so an A/B cannot measure one side twice without it being visible.
"Count the shapes that identify WHICH tree is loaded — a function, because a top-level `for`
does not assign to outer bindings in module scope (measured: UndefVarError on first run)."
function _tree_identity(srcdir)
    nrule, ninline = 0, 0
    for (root, _, files) in walkdir(srcdir), f in files
        endswith(f, ".jl") || continue
        for l in eachline(joinpath(root, f))
            occursin("function rule_results(", l) && (nrule += 1)
            occursin("Expression(Sym(\"=\")", l) && occursin(", X)", l) && (ninline += 1)
        end
    end
    (nrule, ninline)
end

let srcdir = dirname(pathof(MeTTaCore))
    (nrule, ninline) = _tree_identity(srcdir)
    println("  TREE: src=", srcdir)
    println("  TREE: rule_results=", nrule, "  inlined_lookups=", ninline,
            nrule == 1 && ninline == 1 ? "   (refactored)" : "   (PRE-refactor)")
end
println("  RUNS=", RUNS, "  tabled_n=", TABLED_N, "  untabled_n=", UNTABLED_N)

bench("tabled fib($TABLED_N)",     TABLED_N,   true)
bench("untabled fib($UNTABLED_N)", UNTABLED_N, false)
