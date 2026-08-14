# test_multiset_semantics.jl — MeTTa spaces are MULTISETS; the MORK trie is a SET. Both are pinned
# here, because Core currently runs on BOTH and they disagree.
#
# WHY THIS FILE EXISTS. "Move Core's MeTTa surface onto the MORK trie" has been carried as a
# deferred task with the note "blocked: MORK's trie is a SET, MeTTa spaces are MULTISETS". Measured
# 2026-08-01 against the four reference engines (workflows/metta_xcheck.sh — hyperon-experimental,
# CeTTa, PeTTa, Core) to find out what that would actually cost:
#
#   program                              hyperon      CeTTa        PeTTa        Core
#   add x2 -> collapse match             (a a)        (a a)        (a a)        (a a)        4/4 ✅
#   add x2 -> collapse get-atoms         ((c)(c))     stdlib dump  ((c)(c))     ((c)(c))     3/3 ✅
#   collapse (superpose (q q))  CONTROL  (q q)        (q q)        (q q)        (q q)        4/4 ✅
#   add x2 -> remove-atom -> match       (b)          (b)          ()           ()           2-2 ⚠️
#
# So Core's MeTTa surface is ALREADY multiset-correct on everything except `remove-atom`, and there
# the reference engines split 2-2 — hyperon/CeTTa remove ONE copy, PeTTa/Core remove ALL. When the
# ecosystem disagrees with itself there is no single "match upstream" to implement.
#
# The `superpose` control is load-bearing: it never touches the space, so it proves the harness can
# observe multiplicity at all. Without it, four agreeing "no duplicates" answers would be
# indistinguishable from an oracle that is simply blind to the question.
#
# ── THE TWO STORES, AND WHY THE ANSWER DEPENDS ON WHICH ONE YOU ASK ─────────────────────────────
#
#   MeTTa surface   `Eval.Space`, whose store's `.atoms` is a VECTOR  -> MULTISET, duplicates kept
#   CoreSpace API   `core_add!` etc., backed by the MORK trie        -> SET, duplicates dropped
#
# Measured, same session, same process:
#     interp:    add x2 -> collapse match  =>  (a a)
#     CoreSpace: core_add! x2              =>  length(core_atoms) == 1
#
# 🔴 THAT IS THE REAL SHAPE OF THE DEFERRED TASK. It is not "Core is blocked on a decision" — Core
# works today. It is that migrating the MeTTa surface onto the trie WOULD REGRESS three programs
# that currently agree with every reference engine. Anyone attempting that migration must first
# decide how to carry multiplicity (CeTTa needed a whole `counted_pathmap.rs` for this), and these
# tests are the acceptance criteria for it: they must still pass afterwards.
#
# ⚠️ DO NOT "FIX" THE remove-atom ASSERTION TOWARD hyperon without deciding the semantics first.
# It is recorded as OUR CURRENT BEHAVIOUR plus the divergence, not as a correctness claim.
using Test
using MeTTaCore

const _SM = MeTTaCore.Eval

"Fresh interpreter space with the core stdlib — the shape MettaJam's stateless endpoint uses."
_fresh_interp() = (s = _SM.Space(); _SM.load_core_stdlib!(s); s)

"Run MeTTa source in a fresh space, return the LAST result rendered as a string."
_last(src::String) = string(_SM.load_metta!(_fresh_interp(), src)[end])

@testset "multiset semantics — MeTTa surface vs MORK trie" begin

    @testset "MeTTa surface keeps duplicates (agrees with all reference engines)" begin
        # 4/4 agreement, verified via workflows/metta_xcheck.sh on 2026-08-01.
        @test _last("!(add-atom &self (foo a))\n" *
                    "!(add-atom &self (foo a))\n" *
                    "!(collapse (match &self (foo \$x) \$x))") == "(a a)"

        # 3/3 (CeTTa dumps its stdlib for get-atoms — a CeTTa harness artifact, not a disagreement).
        got = _last("!(add-atom &self (baz c))\n" *
                    "!(add-atom &self (baz c))\n" *
                    "!(collapse (get-atoms &self))")
        @test occursin("(baz c) (baz c)", got)
    end

    @testset "CONTROL — superpose duplicates, which never touch the space" begin
        # If this ever stops showing two `q`s, the harness has lost the ability to SEE multiplicity
        # and the agreements above become meaningless rather than reassuring.
        @test _last("!(collapse (superpose (q q)))") == "(q q)"
    end

    @testset "remove-atom — OUR behaviour, and a 2-2 split among the engines" begin
        # hyperon + CeTTa remove ONE copy -> "(b)".  PeTTa + Core remove ALL -> "()".
        # Pinned as current behaviour so a change is deliberate and visible, NOT as a claim that
        # removing all copies is right.
        @test _last("!(add-atom &self (bar b))\n" *
                    "!(add-atom &self (bar b))\n" *
                    "!(remove-atom &self (bar b))\n" *
                    "!(collapse (match &self (bar \$x) \$x))") == "()"
    end

    @testset "the MORK-trie store dedupes — the two stores really do disagree" begin
        # This is the whole reason the migration is not a mechanical change. Same session, same
        # process, opposite answers to the same question.
        cs = new_core_space()
        core_add!(cs, [:foo, :a])
        core_add!(cs, [:foo, :a])
        @test length(core_atoms(cs)) == 1          # SET: the duplicate was dropped
        @test length(core_match(cs, [:foo, Symbol("\$v")])) == 1

        core_remove!(cs, [:foo, :a])
        @test isempty(core_match(cs, [:foo, :a]))  # and one remove clears it
    end
end
