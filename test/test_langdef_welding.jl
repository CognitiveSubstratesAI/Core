# LangDef disable-to-prove welding — the rule_enabled hook welded into Interpreter.jl dispatch.
# Demonstrates that disabling a covered rule actually disables its evaluation path (no legacy
# compensation), proving the rule is load-bearing. Conformance-at-default is gated separately by
# test/standard/test_conformance.jl (stays 234/234 because the guard defaults to enabled).
using MeTTaCore
const SM = MeTTaCore.Interpreter
using Test

_eval(q) = (sp = SM.Space(); SM.load_core_stdlib!(sp);
            res = SM.load_metta!(sp, q);
            sort([string(x) for r in res for x in (r isa AbstractVector ? r : [r])]))

@testset "LangDef disable-to-prove (HES_Chain welded)" begin
    try
        SM.langdef_reset!()
        @test SM.rule_enabled("HES_Chain")                        # default: enabled
        base = _eval(raw"!(chain (+ 1 2) $x $x)")
        @test base == ["3"]                                       # chain reduces (+ 1 2)→3, binds $x

        SM.langdef_disable!("HES_Chain")                          # disable the rule
        @test !SM.rule_enabled("HES_Chain")
        @test _eval(raw"!(chain (+ 1 2) $x $x)") != base          # ⇒ chain no longer fires (load-bearing)

        SM.langdef_reset!()                                       # re-enable
        @test SM.rule_enabled("HES_Chain")
        @test _eval(raw"!(chain (+ 1 2) $x $x)") == base          # works again
    finally
        SM.langdef_reset!()                                       # never leak disabled state into the suite
    end
end

@testset "LangDef weld FAILS CLOSED — unknown and non-live rule names" begin
    # REGRESSION. `rule_enabled` was `!(name in _langdef_disabled())` and never consulted
    # HE_SMALL_STEP_RULES, so it failed OPEN twice over:
    #   * a MISTYPED name is not in the disabled set ⇒ read as ENABLED. `langdef_disable!("HES_Chian")`
    #     disabled nothing, and a disable-to-prove test built on it would pass while proving NOTHING —
    #     precisely the "test that cannot fail" shape this table exists to prevent.
    #   * a rule the table marks `live = false` (structural metadata, not an executable branch) still
    #     reported enabled, because the `live` field was never read.
    # The table already had the right predicate (`langdef_rule_enabled`, LangDefPack.jl:123 → `r.live`);
    # the interpreter simply had a second, weaker copy. Now the table is injected and is the only source.
    try
        # a name that is not in the table at all must RAISE, not silently read as enabled
        @test_throws Exception SM.rule_enabled("HES_Chian")          # transposed typo of HES_Chain
        @test_throws Exception SM.rule_enabled("")
        @test_throws Exception SM.rule_enabled("not-a-rule-at-all")
        # every live rule in the table is known to the interpreter, and agrees with the table
        live_names  = String[r.name for r in MeTTaCore.HE_SMALL_STEP_RULES if r.live]
        struct_names = String[r.name for r in MeTTaCore.HE_SMALL_STEP_RULES if !r.live]
        @test !isempty(live_names) && !isempty(struct_names)         # both classes exist to test
        for n in live_names
            @test SM.rule_enabled(n)                                 # live + not disabled ⇒ enabled
        end
        # structural (non-live) rules are NOT executable branches — must report disabled, not enabled
        for n in struct_names
            @test !SM.rule_enabled(n)
        end
        # and disabling still works through the weld
        SM.langdef_disable!(first(live_names))
        @test !SM.rule_enabled(first(live_names))
    finally
        SM.langdef_reset!()
    end
end
