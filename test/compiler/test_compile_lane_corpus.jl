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
    # 🔴 2026-08-11 — EMITTING `metta` INSTEAD OF `eval` AT CALL SITES REMOVED EVERY EXTRA ERROR IN
    # THIS CORPUS. `EmitIL._instr(::GCall, …)` emitted `(chain (eval (f a)) $out …)`; `eval` makes ONE
    # STEP (`metta.txt:96`), so `$out` was bound to the callee's BODY, not its value, and everything
    # downstream computed on an unreduced term. `metta` interprets. Measured effect here:
    #
    #     e1_kb_write   2 errors → 0      (entry REMOVED — it now agrees)
    #     c3_pln_stv    1 error  → 0      exhausted 2 → 3
    #     c1_grounded_basic 0    → 0      exhausted 0 → 1   (NEW entry)
    #
    # THE EXHAUSTIONS ARE BUDGET, NOT DEFECTS, and that is measured rather than assumed: at 40 000
    # steps ALL THREE are 0 errors / 0 exhausted — and FASTER in wall time (c1 8.06 s → 0.22 s),
    # because burning the 4 000 budget and throwing costs more than finishing. `metta` fully
    # interprets each call where `eval` did one step, so a clause needs more steps; `_CC_MAX_STEPS`
    # stays at 4 000 for the reason its own docstring gives (d2_higherfunc), so the cost shows up here.
    # A wrong answer traded for "needs more room" is the right direction.
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
    # c3_pln_stv ROOT-CAUSED 2026-08-11, and it is the SAME family as e1_kb_write: the emitted
    # `eval` chain does not reproduce the interpreter's no-result semantics.
    #
    # 🔴 THE 4 000-STEP BUDGET HIDES IT. At 4 000 this shows (1 error, 2 exhausted); at 60 000 the
    # interpreter passes ALL THREE and the compiled lane fails two outright. Diagnosing at the suite
    # budget would have mis-read two real wrong answers as "slower". The actual values:
    #
    #   (TV (And (Evaluation (Predicate P) (Concept A)) (Evaluation (Predicate P) (Concept B))))
    #       interpreter  (stv 0.3 0.8)
    #       compiled     (stv NotReducible NotReducible)          ← ×3
    #   (TV (frog Fritz))
    #       interpreter  (stv 0.783 0.68)
    #       compiled     (stv (* 0.9 (function (return NotReducible))) …)
    #
    # WHY. `TV` has THREE clauses; two are `match &self` lookups that yield NO RESULT for a given
    # argument, and the interpreter prunes that nondeterministic branch. The emitted
    # `(chain (eval (TV $a)) $__t1 …)` instead binds `$__t1` to `NotReducible` — a VALUE — which then
    # flows into the `stv` constructor. `metta.txt:78-79` draws exactly this distinction: `Empty` is
    # "the function doesn't return any result" (absorbing), `NotReducible` "returns the unchanged
    # function call instead". `eval` produces the second where the interpreter produces the first.
    # Same mechanism measured directly today: `(chain (eval (Cons 1 Nil)) $t $t)` ⟶ `NotReducible`.
    #
    # CONTROLS, so this is not read wider than it is: `(TV (croaks Fritz))` (a plain fact lookup) and
    # `(TV (Evaluation …))` (one conjunct alone) both AGREE. It takes a multi-clause head whose other
    # clauses fail to trigger it.
    #
    # ⚠️ NOT the `is_fun` root, which was the obvious guess and is wrong here: `TV` IS hoisted (it is
    # the head being compiled, so it is in `funs`), and the un-hoisted `min`/`s-tv` are USER-DEFINED
    # heads, which are safe under one `eval` (measured: `(eval (member2 $x (cdr-atom $l)))` → True).
    "c1_grounded_basic.metta" => (0, 1),   # NEW: needs >4 000 steps under `metta`; clean at 40 000
    "c3_pln_stv.metta"    => (0, 3),       # error GONE; 3 queries now want more than 4 000 steps
    #
    # d2_higherfunc's shapes are NESTED-HEAD definitions — `(= (((curry $f) $x) $y) ($f $x $y))`,
    # `(= ((lambda $v $b) $arg) …)`. Both halves are declined: a variable-headed BODY is
    # "GResidual (unflattened node: IRExpression)", and `Frontend.definition_name` (`:349`) has no
    # case for a head whose first child is an Expression, so it returns `Symbol("")`. Since
    # `lower_program` groups clauses BY NAME, N such definitions in one call MERGE into one group —
    # measured: 3 distinct functions → 1 IRFunctionDefinition with 3 clauses. Latent in this lane
    # (`compile_definition` runs per form) and absent from the ratchet corpus (0 nested heads there),
    # FIXED 2026-08-11 (the merge half): `definition_name` now DESCENDS a compound head, so the three
    # are `curry` / `curry-a` / `lambda` again and `lower_program` no longer groups them. MEASURED
    # effect here: exhausted 2 → 0 — two queries that used to burn the whole budget now terminate.
    # The 3 extra errors are UNCHANGED and are the OTHER half: a variable-headed BODY is still
    # declined as "GResidual (unflattened node: IRExpression)", which is PLeaTTa's `EX.variable_head`
    # obligation (their status: GAP, no proof). Ratchet unmoved at IL 847 / MM2 377, as predicted —
    # the ratchet corpus has 0 nested heads.
    "d2_higherfunc.metta" => (3, 0),
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
    # both AGREE at 2 answers. Nor is it `and`: the SAME failure occurs for `+`.
    #
    # ROOT CAUSE, found 2026-08-11 by printing every lowering stage, and it is NOT specific to any
    # operator. A-normal DOES flatten arguments (`ANormal.jl:216-219`) — but only for a head that
    # `is_fun` recognises, and `is_fun` is resolved from the definitions visible in THIS
    # `lower_program` call. `compile_definition` compiles ONE FORM AT A TIME. So while `frog` is
    # compiled, `croaks` is not a known function, its call is classified as DATA, and it is never
    # hoisted out of argument position. Same source, more knowledge, different IL:
    #
    #   frog ALONE          (chain (eval (and (croaks $x) (eat_flies $x))) $__t1 (return $__t1))
    #   frog WITH callees   (chain (eval (croaks $x)) $__t1 (chain (eval (eat_flies $x)) $__t2
    #                         (chain (eval (and $__t1 $__t2)) $__t3 (return $__t3))))
    #
    # Run by hand, the first returns the clause UNREDUCED and the second returns ["True","True"],
    # matching the interpreter. The `+` control behaves identically, so the corpus passes only
    # because its grounded calls take ATOMIC arguments (`(+ $x $x)`, `(+ 1 2)`).
    #
    # THE FIX IS A TWO-PASS COMPILE LANE: collect every defined head, then compile each form with
    # that set — exactly what `test_coverage_ratchet.jl` already does (Pass 1 `allfuns` → Pass 2
    # `extra_funs`). ⚠️ NOT DONE HERE, and not merely for lack of time: passing `extra_funs` was
    # TRIED earlier in this arc and REVERTED because it exposed ANSWER DOUBLING. So the two-pass
    # change must come with an explanation of that doubling first, or it trades a wrong answer for a
    # different wrong answer.
    # e1_kb_write's entry is REMOVED — 2 extra errors → 0 under `metta`. Its diagnosis above is kept
    # because it is the clearest statement of the class this change closed.
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
    # Same `metta`-at-call-sites effect as the other dict, measured against the PROVED baseline:
    # every extra error gone, two scripts now wanting more than 4 000 steps.
    "c1_grounded_basic.metta" => (0, 1),
    "c3_pln_stv.metta"    => (0, 3),
    "d2_higherfunc.metta" => (3, 0),   # exhausted 2 → 0, compound-head fix; see the other dict
    # e1_kb_write REMOVED — 2 → 0 errors.
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
