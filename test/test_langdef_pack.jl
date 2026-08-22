# LangDefPack (src/standard/LangDefPack.jl) — reflectable HE small-step rule-table, CeTTa-adopted.
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "LangDefPack — reflectable HE small-step rule table" begin
    pack = he_small_step_pack()

    @testset "table shape (14 rules: 10 live + 4 quiescent)" begin
        @test length(pack.rules) == 14
        @test count(r -> r.live, pack.rules) == 10
        @test count(r -> !r.live, pack.rules) == 4
        @test pack.language_id == "HE" && pack.granularity == "small-step" &&
            pack.schema_version == 2
        @test pack.rules[1].name == "HES_GroundedDispatch" &&
            pack.rules[1].claim == "rule-sound"
    end

    @testset "content-addressed digest is stable" begin
        d1 = langdef_digest("HE", "he-extended", "small-step", 2, HE_SMALL_STEP_RULES)
        @test pack.source_digest == d1                       # deterministic
        @test d1 isa UInt64 && d1 != 0
        @test pack.source_digest == 0x12eec5b655a75904       # BYTE-IDENTICAL to CeTTa upstream
    end                                                      # (CeTTa tests/test_step_rules.metta:26)

    @testset "digest EXCLUDES claim (evidence ≠ content), INCLUDES provenance" begin
        repl(i, newr) = (out=copy(pack.rules); out[i]=newr; out)
        r6 = pack.rules[6]
        # bump a claim level (bag-tested → rule-sound) ⇒ digest UNCHANGED
        bumped = repl(
            6,
            MC.LangDefRule(
                r6.name, r6.rule_id, r6.profiles, r6.provenance, "rule-sound", r6.live
            )
        )
        @test langdef_digest("HE", "he-extended", "small-step", 2, bumped) ==
            pack.source_digest
        # change provenance ⇒ digest CHANGES
        provd = repl(
            6,
            MC.LangDefRule(
                r6.name, r6.rule_id, r6.profiles, "DIFFERENT", r6.claim, r6.live
            )
        )
        @test langdef_digest("HE", "he-extended", "small-step", 2, provd) !=
            pack.source_digest
    end

    @testset "rule_enabled: live & not-disabled" begin
        @test langdef_rule_enabled(pack, MC.HES_GROUNDED_DISPATCH)    # live
        @test !langdef_rule_enabled(pack, MC.HES_QUOTE_QUIESCENT)     # non-live (structural)
    end

    @testset "env disable → rule_enabled false (disable-to-prove)" begin
        dp = he_small_step_pack(; env="HES_Let,HES_Case")
        @test !langdef_rule_enabled(dp, MC.HES_LET)
        @test !langdef_rule_enabled(dp, MC.HES_CASE)
        @test langdef_rule_enabled(dp, MC.HES_EVAL)                   # untouched
        @test dp.source_digest == pack.source_digest                 # disabling ≠ content change
    end

    @testset "reflection atom" begin
        s = langdef_step_rules_atom(pack)
        @test occursin("(step-rules HE small-step", s)
        @test occursin("fnv1a64:", s) && occursin("(schema 2)", s)
        @test occursin("(HES_GroundedDispatch rule-sound)", s)
        @test occursin("(disabled)", s)                      # empty disabled — exact CeTTa format
        @test all(occursin("($(r.name) $(r.claim))", s) for r in pack.rules)  # full inventory ≡ upstream
        dp = he_small_step_pack(; env="HES_Let")
        @test occursin("(disabled HES_Let)", langdef_step_rules_atom(dp))
    end
end
