# §7.11.2 `answer_abstract(N)` — WIRED, and the test is about the wiring, not the mechanism.
#
# The mechanism (`trie_insert_answer_restrained!`, `answer_size_abstract`, the tripwire actions) has
# been correct since 2026-08-18 and is covered by `test_abstract.jl`. What it did NOT have was a
# CALLER: `grep` found the function referenced only from its own docstring. It was correct and
# unreachable — `[[feedback_green_suite_hides_unwired_correct_code]]`, which says to ask "is X what
# the live path CALLS", never "is X implemented".
#
# ─── WHY `_merge_partial` AND NOT THE COMPLETION MIRROR ──────────────────────────────────────────
# The obvious site is where completed answers are mirrored into the trie. It cannot work: this
# restraint exists to bound a derivation that GROWS WITHOUT BOUND, so on exactly the programs it is
# for, completion NEVER HAPPENS and the mirror never runs. MEASURED 2026-08-19:
#     (= (p) 0)   (= (p) (s (p)))     under answer_abstract(2)
# spun for over TWENTY MINUTES without terminating while the restraint was unwired; with the wiring
# at the production site it returns 5 answers in ~7 s, the last being `(s (s (s $_sa#1)))`.
# Abstracting at completion would also be abstracting AFTER the term growth it exists to prevent.
#
# ─── WHY THIS FILE USES A TERMINATING PROGRAM ────────────────────────────────────────────────────
# 🔴 The growing program is the honest demonstration and the WRONG regression test: if the wiring
# ever goes inert again, that test does not FAIL, it HANGS — and it takes the whole suite with it.
# So this file uses five ground facts, which terminate either way, and asserts the DIFFERENCE the
# restraint makes to the stored term. Same evidence, no hang.

using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _AR = Eval

const _AR_PROG =
    raw"(= (q) 0)" * "\n" * raw"(= (q) (s 0))" * "\n" * raw"(= (q) (s (s 0)))" * "\n" *
    raw"(= (q) (s (s (s 0))))" * "\n" * raw"(= (q) (s (s (s (s 0)))))" * "\n"

"Run the program with `n > 0` ⇒ `answer_abstract(n)` under bounded rationality, else plain tabling."
function _ar_run(n::Int)::Vector{String}
    _AR.untable_all!()
    _AR.abolish_all_tables!()
    _AR.clear_answer_abstract!()
    _AR.clear_answer_delays!()
    s = Space()
    load_core_stdlib!(s)
    load_metta!(s, _AR_PROG)
    if n > 0
        _AR.table_as!(:q, :answer_abstract => n)
        # SWI's DEFAULT action here is `error`, not abstraction — storing a generalised CONDITIONAL
        # answer is opt-in, and asserting the default would be asserting a different feature.
        _AR.set_max_table_answer_size_action!(_AR.TW_BOUNDED_RATIONALITY)
    else
        _AR.table!(:q)
    end
    String[string(x) for x in load_metta!(s, "!(q)\n")]
end

@testset "§7.11.2 answer_abstract is WIRED at the answer-production site" begin
    try
        plain = _ar_run(0)
        # ANTI-VACUITY: if the program stopped producing answers, every claim below is about nothing.
        @test length(plain) == 5
        @test "(s (s (s (s 0))))" in plain          # the deep answer is stored WHOLE without a restraint

        bounded = _ar_run(2)
        @test length(bounded) == 5                   # same count — the answer is GENERALISED, not dropped
        # 🔴 THE ASSERTION THAT FAILS IF THE WIRING GOES INERT. Without a live caller the engine
        # stores the deep term verbatim and this is false.
        @test !("(s (s (s (s 0))))" in bounded)
        @test any(a -> occursin("_sa", a), bounded)  # …replaced by an abstracted, variable-tailed term

        # shallow answers are untouched — the bound generalises the deep ones only
        for a in ("0", "(s 0)", "(s (s 0))")
            @test a in bounded
        end
    finally
        _AR.untable_all!()
        _AR.abolish_all_tables!()
        _AR.clear_answer_abstract!()
        _AR.clear_answer_delays!()
        # 🔴 RESTORE THE TRIPWIRE ACTION TOO. `set_max_table_answer_size_action!` is PROCESS-GLOBAL,
        # and its documented default is `TW_ERROR` (`pl-tabling.c:9341`) — leaving it on
        # bounded-rationality would silently change how every LATER file's restraint behaves. That is
        # the exact leak class the suite's re-runnability fix closed on 2026-08-18, and upstream's own
        # driver does the same thing (`xsb_test_tables.pl:64-71` resets all six restraint flags around
        # each test).
        _AR.set_max_table_answer_size_action!(_AR.TW_ERROR)
        _AR.reset_execution_flags!()
    end
end
