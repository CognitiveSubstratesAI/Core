# test_lib_policy.jl — policy constants stay MeTTa atoms, and Julia can ASK for them.
#
# WHY THIS EXISTS. Three times, host-language code needed a value that lives in a lib/*.metta atom,
# had no way to reach it, and wrote a copy instead:
#   2026-07-22  PLN truth formulas transcribed into Beliefs.jl (`c_new = n/(n+1)`, under a comment
#               naming the canonical `Truth_w2c` it was copying).
#   2026-05-10  MORKTensorNetworks/src/ecan/ECANTensorBridge.jl implemented ECAN in Julia without
#               anyone opening lib/ecan/.
#   2026-08-05  while fixing that, `hebbian_max_allocation = 0.05f0` was written against
#               lib/ecan/ECAN_Policies.metta's `(hebbian-max-allocation-percentage) 0.5` — a 10x
#               divergence, same day.
# WorldModel/src/PLNCore.jl:189 states the cause: "Being unable to reach the canonical formula is
# exactly what made someone write it out again."
#
# THE ASSERTION THAT CARRIES THIS FILE is the rewrite test. A reader that returns the file's declared
# default is indistinguishable from a working one until the day self-evolution edits an atom and
# nothing changes. ECAN_Policies.metta:5 promises "the AGI can rewrite them without restarting
# Julia"; :62 heads the section "Spreading Parameters (overridden by self-evolution)". If those
# promises are false the whole design is decorative, so they are pinned here.
using Test
using MeTTaCore

@testset "LibPolicy — policy constants are read from the live space" begin
    @testset "reads lib/ecan's declared values" begin
        cs = new_core_space()
        load_core_lib!(cs, :ecan)
        # The two that produced the 2026-08-05 divergence. 0.5 is Core's value and is DELIBERATE —
        # upstream metta-attention's AttentionParam.metta says 0.05. Do not "reconcile" it.
        @test lib_policy(cs, "max-spread-percentage") ≈ 0.3
        @test lib_policy(cs, "hebbian-max-allocation-percentage") ≈ 0.5
        @test lib_policy_int(cs, "max-spreading-depth") == 3
    end

    @testset "a RUNTIME REWRITE is visible — self-evolution actually reaches the value" begin
        cs = new_core_space()
        load_core_lib!(cs, :ecan)
        @test lib_policy(cs, "max-spread-percentage") ≈ 0.3
        core_remove!(cs, "(= (max-spread-percentage) 0.3)")
        core_add!(cs, "(= (max-spread-percentage) 0.42)")
        @test lib_policy(cs, "max-spread-percentage") ≈ 0.42   # NOT the file's 0.3
    end

    @testset "reads the NEW store (MORK trie), not the old interpreter store" begin
        # MEASURED 2026-08-05: `load_core_lib!` writes the trie, but `&self` in a match resolves to
        # the OLD Vector{Atom} store, so `mc_run(cs,"","!(match &self (= (name) $v) $v)")` returned
        # EMPTY for all 30 constants while `core_atoms` showed them present. Empty-from-the-wrong-
        # store looks exactly like a missing atom — which is the premise that ends in a hardcoded
        # Julia constant. Pinned: every declared constant is reachable.
        cs = new_core_space()
        load_core_lib!(cs, :ecan)
        names = lib_policy_names(:ecan)
        @test length(names) >= 30
        unreadable = [n for n in names if (
            try
                lib_policy(cs, n)
                false
            catch
                true
            end
        )]
        @test isempty(unreadable)
    end

    @testset "fails LOUDLY rather than defaulting" begin
        cs = new_core_space()
        load_core_lib!(cs, :ecan)
        # A silent fallback would be the "second hidden policy engine" v5 §7.7 warns against.
        @test_throws ErrorException lib_policy(cs, "no-such-policy-atom")
        # ...and a space with nothing loaded must not answer either.
        @test_throws ErrorException lib_policy(new_core_space(), "max-spread-percentage")
    end

    @testset "the private default space is separate from a caller's space" begin
        # `lib_policy(:ecan, …)` is the DECLARED default; it must not observe another space's edits,
        # or callers would silently share mutable state through a cache.
        cs = new_core_space()
        load_core_lib!(cs, :ecan)
        core_remove!(cs, "(= (max-spread-percentage) 0.3)")
        core_add!(cs, "(= (max-spread-percentage) 0.99)")
        @test lib_policy(cs, "max-spread-percentage") ≈ 0.99
        @test lib_policy(:ecan, "max-spread-percentage") ≈ 0.3     # unaffected
        reset_policy_space!(:ecan)
        @test lib_policy(:ecan, "max-spread-percentage") ≈ 0.3     # still, after a reset
    end

    @testset "generic across libraries, not ECAN-specific" begin
        # The defect recurred across subsystems (PLN 2026-07-22, ECAN twice), so the fix is at the
        # subsystem-agnostic layer. Every lib/ module is reachable by the same call.
        @test lib_policy_names(:pln) isa Vector{String}
        @test lib_policy_names(:metamo) isa Vector{String}
        @test_throws ErrorException lib_policy_names(:no_such_library)
    end

    @testset "a policy atom must be a LITERAL — computed policies rejected, not silently wrong" begin
        cs = new_core_space()
        core_add!(cs, "(= (computed-policy) (* 2 3))")
        @test_throws ErrorException lib_policy(cs, "computed-policy")
        # an arity-bearing head is a function, not a constant
        core_add!(cs, "(= (takes-args \$x) 1.0)")
        @test_throws ErrorException lib_policy(cs, "takes-args")
    end
end
