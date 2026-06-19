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
