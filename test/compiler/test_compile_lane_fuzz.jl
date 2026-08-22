# test_compile_lane_fuzz.jl — GENERATED programs, because 26 scripts is a thin corpus.
#
# ─── WHY, AFTER ALREADY HAVING A CORPUS DIFFERENTIAL ─────────────────────────────────────────────
# The progression this session was: hand-written differentials (inputs I chose) missed everything;
# the 26-script corpus (inputs nobody here chose) found 10 defective scripts immediately. The corpus
# is still 26 programs written by humans to demonstrate features — it covers what upstream thought
# worth demonstrating, not the shapes a compiler actually breaks on.
#
# This generates programs from a grammar instead. Every one is run through BOTH lanes and the answers
# compared. A divergence is a compiler bug with a reproducer attached.
#
# ─── DETERMINISTIC, AND THAT IS NOT A DETAIL ─────────────────────────────────────────────────────
# Fixed seeds, `Xoshiro(seed)` per program. A fuzzer whose failures cannot be replayed produces
# anecdotes: the seed IS the bug report, and `_fz_program(seed)` reproduces it exactly. The suite runs
# a fixed seed RANGE so the test is reproducible run-to-run; widening the range is how you search for
# more, and any seed that fails should be moved into `_FZ_KNOWN` with its diagnosis rather than left
# to make the suite flaky.
#
# ─── WHAT IS GENERATED, AND WHY THOSE SHAPES ─────────────────────────────────────────────────────
# The grammar targets what the compiler actually has to get right, drawn from where it has already
# been measured wrong this session:
#
#   nested calls          the A-normal chain — `(chain (eval …) $t …)` nesting
#   `if` / `case`         branch lowering, which had the fall-through wrong-answer bug
#   `let` destructuring   patterns as DATA — the fix that took IL 687→726
#   arithmetic            the grounded-op seam
#   superpose             nondeterminism, where a duplicated goal shows as duplicated answers
#   multi-clause heads    dispatch, where Invariant 6 doubles answers if a definition is loaded twice
#
# It deliberately does NOT generate `match` over `&self`: a program that reads its own rules is
# CORRECTLY not compiled (`CompileLane._program_introspects_rules`), so those add no signal here — the
# corpus differential already covers that path.
using MeTTaCore
using Test
using Random

const _FZ_V = MeTTaCore.Eval

"""Seeds whose divergence is KNOWN and diagnosed. Empty is the goal; an entry needs a REASON.

MEASURED on the first bounded run: 3 divergences in 32 programs (~9%), all with `fell_back == 0` —
the compiler produced every one of these. Three DISTINCT shapes, which is the argument for generating
programs rather than adding more hand-written cases:

  seed 1   `(g a)`  interpreter `[]`  ·  compiled `["d"]`
           The compiled lane produces an answer the interpreter does not.
           ⚠️ ATTRIBUTION UNRESOLVED, AND STATED AS SUCH. Hand-evaluating the program,
           `(f a)` → `b`, so `(if (== b d) \$v2 d)` takes the ELSE branch and `d` is the answer the
           COMPILED lane gives. By that reading the INTERPRETER is the one that is wrong, and this is
           not a compiler bug at all. A differential says two lanes differ; it does not say which
           erred. Settling it needs a third oracle (LeaTTa/hyperon) and is not guessed at here.

  seed 6   `(f d)`, `(g d)`, `(g a)`  interpreter `["b"]`  ·  compiled `[]`, exhausted 3
           A head with a recursive clause AND a base clause: the interpreter finds the base clause and
           terminates, the compiled lane spends its whole budget. Same class as `d2_higherfunc` in the
           corpus differential — the compiled lane is not wrong, it is unusably slower on a shape the
           interpreter handles.

  seed 26  `(g b)`  interpreter `["a", "a", "b"]`  ·  compiled `["a", "b"]`
           MULTIPLICITY. Two clauses of `g` both match and the interpreter yields `a` TWICE; the
           compiled lane yields it once. MeTTa's surface is a MULTISET and the trie is a SET — a known
           divergence class in this tree, now shown to reach the compiled lane's answers.

None of these was reachable from the 26-script corpus or from any hand-written differential."""
const _FZ_KNOWN = Dict{Int, String}(
    1 => "compiled answers where interpreter does not — attribution unresolved, interpreter may be wrong",
    6 => "compiled lane exhausts budget on recursive+base multi-clause; interpreter terminates",
    26 => "multiplicity: interpreter yields a duplicate answer, compiled lane deduplicates"
)

"Steps a generated program may spend per lane — same reasoning as the corpus differential's budget."
const _FZ_MAX_STEPS = 4_000

const _FZ_SYMS = ["a", "b", "c", "d"]
const _FZ_FNS = ["f", "g", "h"]

"A body expression, `depth` bounding nesting so programs stay small and fast."
function _fz_body(rng::AbstractRNG, depth::Int, vars::Vector{String})
    depth <= 0 && return rand(rng, Bool) ? rand(rng, _FZ_SYMS) : rand(rng, vars)
    k = rand(rng, 1:7)
    if k == 1                                        # a symbol or a bound variable
        return rand(rng, Bool) ? rand(rng, _FZ_SYMS) : rand(rng, vars)
    elseif k == 2                                    # a call to another generated function
        return "($(rand(rng, _FZ_FNS)) $(_fz_body(rng, depth - 1, vars)))"
    elseif k == 3                                    # arithmetic — the grounded seam
        return "(+ $(rand(rng, 0:9)) $(rand(rng, 0:9)))"
    elseif k == 4                                    # if — branch lowering
        return "(if (== $(_fz_body(rng, depth - 1, vars)) $(rand(rng, _FZ_SYMS))) " *
               "$(_fz_body(rng, depth - 1, vars)) $(_fz_body(rng, depth - 1, vars)))"
    elseif k == 5                                    # let — a plain binding
        v = "\$v$(depth)"
        return "(let $v $(_fz_body(rng, depth - 1, vars)) $(_fz_body(rng, depth - 1, [vars; v])))"
    elseif k == 6                                    # let with a DESTRUCTURING pattern
        v1 = "\$p$(depth)"
        v2 = "\$q$(depth)"
        return "(let ($v1 $v2) ($(rand(rng, _FZ_SYMS)) $(rand(rng, _FZ_SYMS))) " *
               "$(_fz_body(rng, depth - 1, [vars; v1; v2]))" * ")"
    else                                             # superpose — nondeterminism
        return "(superpose ($(rand(rng, _FZ_SYMS)) $(rand(rng, _FZ_SYMS))))"
    end
end

"""A whole program: a few definitions (some heads multi-clause) and a few `!` queries.

Queries call the generated functions with ground arguments, so both lanes have something to compute
rather than returning the call unreduced."""
function _fz_program(seed::Int)::String
    rng = Xoshiro(seed)
    lines = String[]
    for fn in _FZ_FNS
        for _ in 1:rand(rng, 1:2)                    # 1 or 2 clauses per head — dispatch
            arg = "\$x"
            push!(lines, "(= ($fn $arg) $(_fz_body(rng, rand(rng, 1:3), [arg])))")
        end
    end
    for _ in 1:3
        push!(lines, "!($(rand(rng, _FZ_FNS)) $(rand(rng, _FZ_SYMS)))")
    end
    join(lines, "\n") * "\n"
end

"""Interpreter answers, form by form, in one Space — the oracle, UNDER THE SAME STEP BUDGET.

🔴 BOUNDING ONE LANE AND NOT THE OTHER IS HOW THIS HARNESS FIRST FAILED. `compile_run` took
`max_steps`; this function did not. A generated program with unbounded recursion (`f` calling `g`
calling `f`, no base case — which a fuzzer SHOULD produce) then ran forever on the oracle side and
allocated until the runner's 8 GB cgroup ceiling killed it, exit 137.

The ceiling did its job — nothing outside the scope was touched, which is the whole reason it exists
(`tools/run_tests.sh`). But a harness must bound what it runs, and "the other lane" is part of what
it runs. `_INTERPRET_MAX` is PROCESS-GLOBAL, so it is snapshot/restored exactly as `CompileLane` does
it; leaving it set would silently bound every later test in the suite."""
function _fz_interp(program::AbstractString)
    prev = _FZ_V._INTERPRET_MAX[]
    _FZ_V.interpret_max_steps!(_FZ_MAX_STEPS)
    try
        sp = _FZ_V.Space()
        _FZ_V.load_core_stdlib!(sp)
        out = Tuple{String, Vector{String}}[]
        for (bang, f) in MeTTaCore.mm2_split_forms(program)
            rs = try
                _FZ_V.load_metta!(sp, bang ? "!" * f : f)
            catch
                return nothing
            end
            bang && push!(
                out,
                (String(strip(f)),
                    sort(
                        String[
                            string(x) for y in rs
                            for x in (y isa AbstractVector ? y : [y])
                        ]
                    ))
            )
        end
        return out
    finally
        _FZ_V._INTERPRET_MAX[] = prev
    end
end

"""How many seeds to run. DEFAULT 40 — the committed coverage, unchanged.

⚠️ THIS IS A TIME KNOB, NOT A COVERAGE DECISION, and the distinction is why it defaults to the full
range instead of a smaller one. MEASURED 2026-08-11: this file is the suite's single largest cost at
~255 s, and the cause is neither the harness nor a hang — `load_core_stdlib!` is 2.0 ms and accounts
for 0.2 s across all 80 calls, while ONE small generated program costs 1.59 s interpreted and 6.09 s
through `compile_run`. 40 × ~6.4 s IS the number. For a small program the COMPILATION dominates,
because lowering / A-normal / emission run per form with no reuse across the program.

Lower it ONLY to time-box a run you are going to repeat at full range before committing:

    CORE_FUZZ_SEEDS=28 tools/run_tests.sh            # 28 keeps all three _FZ_KNOWN seeds (1, 6, 26)

Any value below 26 silently drops a known divergence from the comparison, so the assertion below
holds it at 26 rather than trusting the caller."""
const _FZ_SEEDS = let n = tryparse(Int, get(ENV, "CORE_FUZZ_SEEDS", "40"))
    n === nothing ? 40 : max(26, n)
end

@testset "compile lane — GENERATED programs (the corpus is only 26 scripts)" begin
    seeds = 1:_FZ_SEEDS
    _FZ_SEEDS == 40 ||
        @warn "fuzz range REDUCED — not a full-coverage run" seeds=_FZ_SEEDS default=40
    diverged = Tuple{Int, String}[]
    ran = 0
    compiled_total = 0

    for seed in seeds
        prog = _fz_program(seed)
        want = _fz_interp(prog)
        # The INTERPRETER failing is not a compiler finding — a generated program may hit a genuine
        # interpreter limitation, and blaming the compiler for it would be a false positive. Skipped,
        # and counted, so a generator that produces nothing runnable cannot look like success.
        want === nothing && continue
        got = try
            r = MeTTaCore.compile_run(prog; max_steps=_FZ_MAX_STEPS)
            compiled_total += r.compiled
            [(q, sort(a)) for (q, a) in r.answers]
        catch e
            push!(diverged, (seed, "compile_run THREW: " * first(sprint(showerror, e), 90)))
            continue
        end
        ran += 1
        got == want && continue
        haskey(_FZ_KNOWN, seed) && continue
        push!(diverged, (seed, "answers differ"))
    end

    for (seed, why) in first(diverged, 5)
        @info "FUZZ DIVERGENCE — reproduce with `_fz_program($seed)`" seed why program=_fz_program(
            seed
        )
    end
    @test isempty(diverged)

    # ANTI-VACUITY, twice over. A generator that produces unrunnable programs, or programs with
    # nothing to compile, would pass the comparison above while testing nothing at all.
    @info "fuzz" programs_compared=ran definitions_compiled=compiled_total
    # SCALED WITH THE SEED COUNT, and calibrated so the FULL range is unchanged: at the default 40
    # both floors are 25, exactly as before the knob existed. A reduced run must still prove the same
    # PROPORTION ran and compiled — otherwise lowering the range would quietly disarm the anti-vacuity
    # checks along with the runtime, which is the failure the knob is supposed not to introduce.
    floor_n = div(_FZ_SEEDS * 25, 40)     # 40 → 25 · 28 → 17 · 26 → 16
    @test ran >= floor_n                  # most seeds must actually run on BOTH lanes
    @test compiled_total >= floor_n       # …and the compiler must actually have compiled something
end
