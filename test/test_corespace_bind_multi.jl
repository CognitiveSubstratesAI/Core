# test_corespace_bind_multi.jl — N-factor conjunctive query WITH BINDINGS (`core_match_bind_multi`).
#
# ─── WHY THIS IS NOT COVERED BY THE UPSTREAM DIFFERENTIAL ────────────────────────────────────────
# The MORK port is differentially gated (285 vendored MM2 probes ratcheted at 274; PathMap's own
# executable differential; workflows/mm2_xcheck.sh against the release binary). None of that reaches
# here: upstream MORK has NO `core_match_bind`, so there is no counterpart to diff against. The
# differential gates the PRIMITIVE underneath (`space_query_multi_at`); this is a Core-side API above
# it, and by our own rule an addition above upstream needs its OWN oracle. Test 4 is that oracle —
# the lane-independence check, which is the internal analogue of a differential.
using MeTTaCore
using Test

const _BM = MeTTaCore

_bm_norm(rs) = Set(sort([(string(k), string(v)) for (k, v) in d]) for d in rs)
_bm_v(n) = Symbol("\$" * n)

@testset "core_match_bind_multi — N-factor conjunction with shared variables" begin
    sp = _BM.new_core_space()
    for a in ([:edge, :a, :b], [:edge, :b, :c], [:edge, :c, :d],
        [:label, :b, "some", "thing"], [:label, :c, "other", "stuff"])
        _BM.core_add!(sp, a)
    end

    @testset "1. chain join over equal-arity factors" begin
        r = _BM.core_match_bind_multi(
            sp, [[:edge, _bm_v("x"), _bm_v("y")], [:edge, _bm_v("y"), _bm_v("z")]])
        @test length(r) == 2
        @test _bm_norm(r) == Set([
            [("\$x", "a"), ("\$y", "b"), ("\$z", "c")],
            [("\$x", "b"), ("\$y", "c"), ("\$z", "d")],
        ])
    end

    # The factors here have DIFFERENT ARITY (3 and 4) on purpose. With two same-shaped factors, a
    # split that mis-computes `expr_span` still lands on an atom boundary BY ACCIDENT and every
    # assertion passes. Unequal arity is what turns an off-by-one into a wrong ANSWER: the second
    # `_bind_walk!` starts mid-atom and binds plausible-looking garbage rather than erroring.
    @testset "2. unequal-arity factors — the span split must be exact" begin
        r = _BM.core_match_bind_multi(
            sp, [[:edge, _bm_v("x"), _bm_v("y")], [:label, _bm_v("y"), _bm_v("p"), _bm_v("q")]])
        @test length(r) == 2
        @test _bm_norm(r) == Set([
            [("\$p", "some"), ("\$q", "thing"), ("\$x", "a"), ("\$y", "b")],
            [("\$p", "other"), ("\$q", "stuff"), ("\$x", "b"), ("\$y", "c")],
        ])
    end

    # The load-bearing inference of the whole design: because every factor binds into ONE dict,
    # `_bind_walk!`'s repeat-must-agree check (CoreSpace.jl:845-847) enforces consistency ACROSS
    # factors, not merely within one. `(, (edge $x $y) (edge $y $x))` asks for a 2-cycle; the data
    # is an acyclic chain, so a correct join returns NOTHING. If the check only fired within a
    # factor, every chain pair would match and this would return 2.
    @testset "3. a shared variable must agree ACROSS factors (rejects)" begin
        r = _BM.core_match_bind_multi(
            sp, [[:edge, _bm_v("x"), _bm_v("y")], [:edge, _bm_v("y"), _bm_v("x")]])
        @test isempty(r)
    end

    # 🔴 ASSERT ON THE RESULT SET, NEVER THE SEQUENCE — and this is why, so nobody "fixes" a flaky
    # test by pinning the order. With the trie-join fast paths ON, P5's cardinality-greedy reorder
    # (`_CARD_REORDER_ENABLED`) visits factors smallest-first, so solutions ARRIVE IN A DIFFERENT
    # ORDER than under the plain ProductZipper. MEASURED: identical multisets, different sequence.
    # A sequence assertion passes with the fast paths off and fails with them on.
    #
    # What is lane-INDEPENDENT is the LAYOUT of `combined` — verified by comparing the bytes the
    # effect RECEIVES with the flag on and off, not the answers it EMITS. Those are different
    # claims: "byte-identical result set" is about emission, and the split depends on reception.
    @testset "4. lane independence — same SET under both join lanes" begin
        pats = [[:edge, _bm_v("x"), _bm_v("y")], [:edge, _bm_v("y"), _bm_v("z")]]
        on = _BM.core_match_bind_multi(sp, pats)
        prev = _BM.MORK._TRIE_JOIN_ENABLED[]
        try
            _BM.MORK._TRIE_JOIN_ENABLED[] = false
            off = _BM.core_match_bind_multi(sp, pats)
            @test _bm_norm(on) == _bm_norm(off)
            @test length(on) == length(off) == 2
        finally
            _BM.MORK._TRIE_JOIN_ENABLED[] = prev   # restore, or every later test runs on one lane
        end
    end

    # The ledger claims its entries are "verified BY EXECUTION, declines included". `conjunction` was
    # NOT: flipping it false→true broke no test, because nothing asserted it. So the flag and the
    # capability could drift apart silently, which is exactly what a capability ledger exists to
    # prevent. This ties them together — if `core_match_bind_multi` regresses, BOTH this and the
    # tests above go red, and if someone flips the flag back the mismatch is named.
    # ⚠️ IF THIS FAILS ON A WARM DAEMON, RESTART BEFORE BELIEVING IT. `_CAPS_MORK` is a `const`, and
    # Revise tracks METHODS, not BINDINGS — a const container strands, so a warm session serves the
    # PRE-EDIT ledger while the source says otherwise. Observed exactly that when flipping this flag:
    # `tools/warm_suite.sh restart` cleared it. A ledger edit needs a restart; a function-body edit
    # does not.
    @testset "0. the ledger flag agrees with the live capability" begin
        caps = _BM.space_caps(:mork)
        @test caps.conjunction == true
        # ...and it is true because the operation WORKS, not because someone typed `true`:
        @test !isempty(_BM.core_match_bind_multi(
            sp, [[:edge, _bm_v("x"), _bm_v("y")], [:edge, _bm_v("y"), _bm_v("z")]]))
    end

    @testset "5. boundary tolerance, matching core_match_bind" begin
        @test isempty(_BM.core_match_bind_multi(sp, []))
        @test isempty(_BM.core_match_bind_multi(sp, [[]]))
        # a single factor through the multi path agrees with the single-pattern entry point
        one = _BM.core_match_bind_multi(sp, [[:edge, _bm_v("x"), _bm_v("y")]])
        @test _bm_norm(one) == _bm_norm(_BM.core_match_bind(sp, [:edge, _bm_v("x"), _bm_v("y")]))
    end
end
