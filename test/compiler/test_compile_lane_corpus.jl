# test_compile_lane_corpus.jl — the compiled lane against the REAL corpus, not programs I chose.
#
# ─── WHY THIS EXISTS SEPARATELY FROM `test_compile_lane.jl` ──────────────────────────────────────
# That file's differentials are hand-written programs, and a hand-written differential is the weakest
# form of oracle: it tests the cases the author thought of. This session produced two demonstrations
# of what that misses — the IL stage scored 832 while emitting `<unrenderable:IRSpecial>` as a symbol,
# and the shared renderer silently widened MM2 into emitting a `match` its target cannot run. Both
# were wrong ANSWERS, both invisible to every count, and both caught only by execution against the
# interpreter on cases that happened to be in range.
#
# So the input here is a corpus nobody in this repo chose: the 26 hyperon-experimental interpreter
# scripts vendored verbatim in `test/standard/conformance/`. `test_conformance.jl` runs them through
# the INTERPRETER and asserts 234/234 directives pass. This file runs the same scripts through
# `compile_run` — compiler primary, interpreter fallback — and asserts the compiled lane does not do
# worse.
#
# ─── THE SELF-CHECKING PROPERTY IS WHAT MAKES THIS CHEAP ─────────────────────────────────────────
# Every `!`-directive in the corpus is an assert-family call returning the unit atom `()` on pass and
# `(Error <call> AssertionFailed)` on fail. So agreement needs no output diffing and no expected-value
# table of mine: COUNT THE ERROR DIRECTIVES. The interpreter's count is the baseline, and it is
# already pinned at zero by `test_conformance.jl`.
#
# ─── THE TRAP THIS FILE IS SHAPED AROUND, AND IT IS THE SAME ONE AS EVER ─────────────────────────
# `compile_run` FALLS BACK to source for any definition it declines. A corpus differential that only
# checked error counts would go green while every single definition fell back — proving the
# interpreter equals itself and nothing about the compiler. So the compiled/fell-back split is
# MEASURED AND ASSERTED per script, and the totals are printed every run so the real state is visible
# rather than summarised into a pass.
using MeTTaCore
using Test

const _CC_V = MeTTaCore.Eval
const _CC_DIR = joinpath(@__DIR__, "..", "standard", "conformance")

# The conformance scripts `import!` each other, so the module path must include their directory —
# same requirement `test_conformance.jl` has, and appended rather than replaced for the same reason
# (a destructive assignment there once broke every later test file by wiping `lib/`).
_CC_DIR in _CC_V._MODULE_PATH[] || push!(_CC_V._MODULE_PATH[], _CC_DIR)

"Error directives produced by running `src` on the INTERPRETER — the baseline this lane must match."
function _cc_interp_errors(src::AbstractString)::Int
    sp = _CC_V.Space(); _CC_V.load_core_stdlib!(sp)
    rs = try _CC_V.load_metta!(sp, src) catch; return -1 end
    count(r -> r isa MeTTaCore.StandardMeTTa.Expression && !isempty(r.children) &&
               r.children[1] == MeTTaCore.StandardMeTTa.Sym("Error"), rs)
end

"""Steps a single script may spend in the compiled lane before its queries are cut off.

⚠️ NOT A TUNING KNOB — WITHOUT IT THIS FILE CANNOT BE IN A SUITE. MEASURED 2026-08-10 on
`d2_higherfunc.metta`, where the compiled lane's cost per step explodes:

    max_steps =   2 000  →   15.9 s   (2 queries exhausted)
    max_steps =  20 000  →  307.1 s   (2 queries exhausted)
    max_steps = 100 000  →  did not finish in 10 minutes

`compile_run`'s own default is 512 000. The lane is not diverging — the budget stops it and
`exhausted` reports which queries hit it — but at the default this script is effectively
non-terminating, and the first version of this file sat at 98% CPU for 20+ minutes on it with an
empty log. A harness must bound what it runs; that is the same lesson as the memory ceiling in
`tools/run_tests.sh`, arriving from the other direction."""
const _CC_MAX_STEPS = 4_000

"Error directives produced by the COMPILED lane, plus how much compiled and what ran out of budget."
function _cc_compiled(src::AbstractString)
    r = try MeTTaCore.compile_run(src; max_steps = _CC_MAX_STEPS)
        catch e; return (errors = -1, compiled = 0, fell_back = 0, exhausted = 0,
                         why = sprint(showerror, e)) end
    errs = 0
    for (_, answers) in r.answers, a in answers
        startswith(a, "(Error ") && (errs += 1)
    end
    (errors = errs, compiled = r.compiled, fell_back = r.fell_back,
     exhausted = length(r.exhausted), why = "")
end

"""Scripts where the COMPILED lane is known to disagree with the interpreter, or to run out of budget.

🔴 THESE ARE REAL DEFECTS, RECORDED SO THEY CANNOT GET WORSE — not accepted, and not fixed here.
Every one was found by pointing this differential at a corpus nobody in this repo chose; none was
visible to `test_compile_lane.jl`'s hand-written programs, to the coverage ratchet, or to the LeaTTa
proved oracle (which runs the INTERPRETER — `compile_run` appears nowhere in it).

The value is a number: `(extra error directives, queries that exhausted the budget)`. A script that
gets WORSE fails this test; a script that gets BETTER also fails it, forcing the baseline down
deliberately rather than letting an improvement go unrecorded — the same discipline
`test_conformance.jl` uses for its own matrix.

⚠️ THE NUMBERS ARE BUDGET-DEPENDENT, and that is why `_CC_MAX_STEPS` sits next to them. Measured at
the default 512 000 steps, `c3_pln_stv` showed 2 extra errors and 0 exhausted; at 4 000 it shows 1 and
2. The budget converts "wrong answer eventually" into "ran out of room", so these are the numbers AT
THIS BUDGET and changing the budget invalidates them.

MEASURED 2026-08-10 over all 26 scripts: 10 deviate — 6 with wrong answers, 4 exhausting budget."""
const _CC_KNOWN = Dict{String, Tuple{Int, Int}}(
    # b3_direct and b4_nondeterm were HERE and are FIXED — both introspect their own rules, and
    # `CompileLane._program_introspects_rules` now compiles nothing for such a program. Removed rather
    # than left as passing entries, so the ratchet keeps working in the improving direction too.
    #
    # e2_states was HERE at (3, 0) and is FIXED, 2026-08-11. Root: the compile lane serializes IL to
    # TEXT and re-parses it, and `Grounded{StateCell}` prints as `(State (A B))`, which re-parses as
    # an ordinary Expression — the cell's IDENTITY is gone, so `get-state` and every later
    # `change-state!` see a different thing. `e2_states.metta:17` is literally
    # `(= (get-token) &state-token)`, a definition whose whole body is a parse-time-bound state cell.
    # `CompileLane._unroundtrippable` now declines such a definition; it falls back and answers
    # correctly. That guard fired EXACTLY ONCE across all 26 scripts (`total_compiled` 56 → 55), which
    # is why the floor below moved by exactly one.
    "c3_pln_stv.metta"    => (1, 2),
    #
    # d2_higherfunc's shapes are NESTED-HEAD definitions — `(= (((curry $f) $x) $y) ($f $x $y))`,
    # `(= ((lambda $v $b) $arg) …)`. Both halves are declined: a variable-headed BODY is
    # "GResidual (unflattened node: IRExpression)", and `Frontend.definition_name` (`:349`) has no
    # case for a head whose first child is an Expression, so it returns `Symbol("")`. Since
    # `lower_program` groups clauses BY NAME, N such definitions in one call MERGE into one group —
    # measured: 3 distinct functions → 1 IRFunctionDefinition with 3 clauses. Latent in this lane
    # (`compile_definition` runs per form) and absent from the ratchet corpus (0 nested heads there),
    # so no number moves today; recorded because the ratchet DOES lower whole files.
    "d2_higherfunc.metta" => (3, 2),
    #
    # e1_kb_write's root was NARROWED 2026-08-11 and is NOT what its error text suggests. The text
    # reads `(add-atom &self …)` for source that says `&kb`, but that is only `Grounded{Space}`'s
    # printing (see `test_il_roundtrip.jl`) — and `&kb` never appears inside a DEFINITION in that
    # script, only in `!` directives, so the round-trip guard correctly does not fire.
    # Witnessed instead, smaller than the script and with nothing declined (`compiled=6 fell_back=0`):
    #     (= (croaks Fritz) True)     (= (croaks Sam) True)
    #     (= (eat_flies Fritz) True)  (= (eat_flies Sam) True)
    #     (= (frog $x) (and (croaks $x) (eat_flies $x)))
    #     (= (green $x) (frog $x))
    #     !(green $x)
    #   interpreter  ["True", "True"]
    #   compiled     ["(function (chain (eval (and (croaks $x) (eat_flies $x))) NotReducible (return NotReducible)))"]
    # An unbound argument is NOT the problem — `!(croaks $x)` and the same call through a definition
    # both AGREE at 2 answers. The CONJUNCTION is: `(and A B)` lowers to a single opaque `eval`, so
    # the two conjuncts cannot share a binding for `$x`, and the clause returns unreduced with raw IL
    # leaking into the answer. Same family as PLeaTTa's ROOT 3 (bindings not flowing between goals).
    "e1_kb_write.metta"   => (2, 0),
    "f1_imports.metta"    => (0, 1),
    "g1_docs.metta"       => (0, 1),
)

@testset "compile lane — the REAL corpus (26 hyperon scripts), not programs we chose" begin
    scripts = sort([f for f in readdir(_CC_DIR) if endswith(f, ".metta")])
    @test length(scripts) == 26                       # the corpus is intact, not silently shrunk

    total_compiled = 0; total_fell_back = 0; worse = String[]
    println("\n  ── compile-lane corpus differential (compiled / fell-back · errors interp→compiled) ──")
    for name in scripts
        src = read(joinpath(_CC_DIR, name), String)
        print("     … $name\r"); flush(stdout)      # visible BEFORE the work, so a hang names itself
        base = _cc_interp_errors(src)
        got  = _cc_compiled(src)
        total_compiled += got.compiled; total_fell_back += got.fell_back
        want_extra, want_exh = get(_CC_KNOWN, name, (0, 0))
        extra = got.errors - base
        ok = extra == want_extra && got.exhausted == want_exh
        flag = ok ? " " : "✗"
        println("     $flag $(rpad(name, 26)) $(lpad(got.compiled, 3))/$(lpad(got.fell_back, 3))   " *
                "$base → $(got.errors)  exh=$(got.exhausted)" *
                (want_extra + want_exh > 0 ? "   [known $want_extra/$want_exh]" : "") *
                (isempty(got.why) ? "" : "   " * first(got.why, 80)))
        # FLUSH PER SCRIPT. Julia buffers stdout when it is redirected, so a run that hangs prints
        # NOTHING and the hanging script cannot be identified from the log — measured on the first
        # run of this file, which sat at 98% CPU for ten minutes with an empty log.
        flush(stdout)
        # THE ASSERTION. Not "zero errors" — the compiled lane must not do WORSE than the interpreter
        # on the same script. Pinning zero would encode `test_conformance.jl`'s baseline twice and
        # break here for a reason that has nothing to do with the compiler.
        ok || push!(worse, "$name: extra errors $extra (known $want_extra), " *
                            "exhausted $(got.exhausted) (known $want_exh)")
    end
    for w in worse; @info "compile-lane corpus DEVIATION" detail=w; end
    @test isempty(worse)

    println("     TOTAL compiled=$total_compiled  fell_back=$total_fell_back")
    # ⚠️ THE ANTI-VACUITY ASSERTION. Without this the testset passes when EVERY definition falls back,
    # which proves the interpreter equals itself. A number rather than `> 0` so a collapse from
    # hundreds to a handful is a failure and not a shrug; raise it when the compiler covers more.
    # MEASURED 56 of 266 definitions across the corpus — down from 89 because every script that
    # INTROSPECTS its own rules now compiles nothing, which is the correct answer for those programs.
    # (Estimated 64 by subtracting only the two scripts with wrong answers; the guard correctly fires
    # on more than those, which is why this number is measured and not computed.) Pinned exactly, not `> 0`: a collapse to a
    # handful must FAIL rather than pass quietly, and a rise must be recorded deliberately.
    #
    # 56 → 55 on 2026-08-11, and the ONE definition given up is named: `e2_states.metta:17`
    # `(= (get-token) &state-token)`, whose body is a `Grounded{StateCell}` that cannot survive the
    # IL text round-trip (`CompileLane._unroundtrippable`). Compiling it produced 3 wrong answers;
    # declining it produces 0. That is coverage traded for correctness, deliberately, and the trade is
    # visible here rather than buried — the guard fired exactly once corpus-wide, so this floor moved
    # by exactly one and any wider effect would have shown up as a bigger drop.
    @test total_compiled >= 55
    @test total_compiled + total_fell_back > 0
end

# ── SECOND CORPUS: the LeaTTa PROVED oracle, pointed at the COMPILED lane ──────────────────────────
#
# WHY A SECOND ONE, when the conformance differential above already found three wrong answers. Because
# that differential's baseline is CORE'S OWN INTERPRETER: it asks "does the compiled lane agree with
# the interpreted lane", and if both were wrong the same way it goes green. The LeaTTa corpus carries
# MACHINE-PROVED values — LeaTTa is a Lean-4 MeTTa whose `interpretAtom`/`mettaEval` come with checked
# TypeSoundness / Preservation / Confluence / MatcherCorrect proofs, and it PROVES all 270 directives
# pass. So here a deviation is OUR bug, not a difference of opinion.
#
# ⚠️ AND THE ORACLE DID NOT ALREADY COVER THIS. `test/oracle/leatta/test_leatta_oracle.jl` runs its
# corpus through `_LI.Space` — the INTERPRETER — and `compile_run` appears nowhere in it. The proved
# oracle has been gating `Eval` only; the compiled lane was never on the path it exercises, so its
# CORE_BUG=0 says nothing whatsoever about the compiler. Pointing the same corpus at the other lane
# costs one file and closes that.
#
# The corpus is self-checking in the same way: each `!`-directive returns the unit atom `()` on pass.
"""Known compiled-lane deviations from the PROVED values. Same shape as `_CC_KNOWN`.

⚠️ THE TWO CORPORA OVERLAP HEAVILY — both vendor Hyperon's own test corpus, so most filenames appear
in each. Measured: the LeaTTa half reproduces 7 of the conformance half's deviations and adds
`test_stdlib.metta`, which is clean. The second run is therefore NOT extra coverage; its value is the
BASELINE, which here is machine-proved rather than self-referential."""
const _CC_KNOWN_LEATTA = Dict{String, Tuple{Int, Int}}(
    "c3_pln_stv.metta"    => (1, 2),
    "d2_higherfunc.metta" => (3, 2),
    "e1_kb_write.metta"   => (2, 0),
    # e2_states was (3, 0) here too and is FIXED against the PROVED baseline as well — the same
    # `_unroundtrippable` decline. Worth stating separately from the conformance half: that half's
    # baseline is our own interpreter, so "agrees" there could in principle mean two lanes wrong
    # together. Here the 3 errors are gone measured against machine-proved values, which is the
    # stronger claim and the reason both corpora are run.
    "g1_docs.metta"       => (0, 1),
)

const _CC_LEATTA = joinpath(@__DIR__, "..", "oracle", "leatta", "corpus")

@testset "compile lane — the LeaTTa PROVED corpus (deviation ⇒ our bug, not an opinion)" begin
    scripts = sort([f for f in readdir(_CC_LEATTA) if endswith(f, ".metta")])
    @test length(scripts) >= 20                       # the vendored corpus is intact

    total_compiled = 0; total_fell_back = 0; worse = String[]
    println("\n  ── LeaTTa-corpus compile-lane differential (compiled / fell-back · errors) ──")
    for name in scripts
        src = read(joinpath(_CC_LEATTA, name), String)
        print("     … $name\r"); flush(stdout)
        # ⚠️ THE BASELINE HERE IS ZERO, NOT THE INTERPRETER, and that is the entire reason to use this
        # corpus twice. LeaTTa PROVES all 270 directives pass, so "0 error directives" is a
        # machine-checked fact rather than Core's opinion of itself. Baselining against
        # `_cc_interp_errors` would ask "does the compiled lane agree with the interpreted lane" —
        # green if both are wrong the same way, which is exactly the weakness the conformance half
        # already has.
        base = 0
        got  = _cc_compiled(src)
        total_compiled += got.compiled; total_fell_back += got.fell_back
        want_extra, want_exh = get(_CC_KNOWN_LEATTA, name, (0, 0))
        extra = got.errors - base
        ok = extra == want_extra && got.exhausted == want_exh
        println("     $(ok ? " " : "✗") $(rpad(name, 30)) " *
                "$(lpad(got.compiled, 3))/$(lpad(got.fell_back, 3))   $base → $(got.errors)" *
                "  exh=$(got.exhausted)$(isempty(got.why) ? "" : "   " * first(got.why, 80))")
        flush(stdout)
        ok || push!(worse, "$name: extra $extra (known $want_extra), exh $(got.exhausted) (known $want_exh)")
    end
    println("     TOTAL compiled=$total_compiled  fell_back=$total_fell_back")
    @test isempty(worse)
    @test total_compiled > 0                          # anti-vacuity: something was actually compiled
end
