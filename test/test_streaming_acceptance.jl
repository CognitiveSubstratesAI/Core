# test/test_streaming_acceptance.jl
#
# Streaming-`=` acceptance oracles. NOT included in runtests.jl yet — this
# is a standalone probe meant to be ORACLE not MIRROR: every expected value
# below is derived from H-E spec or hand-derivation FIRST, in the test
# body's commentary, BEFORE any implementation is consulted.
#
# Today, on main with the eager single-result rewriter:
#   * Every @test_broken assertion in here fails. That is the correct state.
#   * The testset itself reports green because @test_broken means
#     "expected to fail; warn loudly if it accidentally passes."
#
# When streaming `=` lands (eventually, on top of prototype/stream-eval-and-alpha):
#   * Each @test_broken flips to @test in the same commit that lands streaming.
#   * If all flip green, streaming is correct in the four ways this probe
#     measures.
#   * If any flips green but the corresponding @test_broken passes BEFORE
#     the flip, that means the implementation accidentally satisfies the
#     test without satisfying the spec — investigate which.
#
# Probes are intentionally BEHAVIORAL (result sets and cardinality), not
# STRUCTURAL (no assertions about whether Bindings is a linked-list or
# whether _eval_match returns a stream object). The streaming work may
# choose its internals differently than the prototype branch guessed; the
# probes stay valid regardless because they only check what a MeTTa
# program observes.
#
# Run: julia --project=packages/Core packages/Core/test/test_streaming_acceptance.jl

using Test
using MeTTaCore

# Helper: fresh space with grounded + stdlib loaded so each probe is
# independent and order-insensitive.
function _fresh()
    S = new_core_space()
    register_for_space!(S)
    load_stdlib!(S)
    S
end

@testset "Streaming `=` acceptance oracles" begin

    # ─────────────────────────────────────────────────────────────────────────
    # PROBE 1 — Multi-clause function: fan-out cardinality through `=` rewrite
    # ─────────────────────────────────────────────────────────────────────────
    #
    # SPEC DERIVATION (before any code):
    #   Given:
    #     (= (color) red)
    #     (= (color) green)
    #     (= (color) blue)
    #   Per H-E nondeterminism semantics, `=` is nondeterministic — every
    #   clause whose head unifies with the call fires, producing a stream
    #   of results. Here all three clauses unify with `(color)` (no args
    #   to discriminate), so `(color)` is the stream {red, green, blue}.
    #   `(collapse (color))` materialises that stream as a Vector{Any} of
    #   length 3, with elements equal to the set {red, green, blue} as
    #   atoms (order is not part of the spec — set equality is).
    #
    # WHAT THIS PROBES:
    #   The rewriter must enumerate ALL matching `=` clauses, not stop at
    #   first match. This is the canonical Decision-1 (streaming `=`)
    #   acceptance gate — without it nothing else in this file can pass.
    #
    @testset "PROBE 1 — multi-clause `=` fans out" begin
        S = _fresh()
        run_metta(
            """
  (= (color) red)
  (= (color) green)
  (= (color) blue)
  """,
            S,
        )

        r = run_metta("!(collapse (color))", S)
        @test length(r) == 1                                # one top-level expr
        inner = r[1]
        # Single combined assertion: cardinality AND value must both be right.
        # Don't split into separate length and set checks — main returns
        # accidentally-correct cardinalities (unreduced exprs with the same
        # element count) that would mark the length check "unexpected pass."
        @test_broken inner isa AbstractVector && length(inner) == 3 && Set(inner) == Set([:red, :green, :blue])
    end

    # ─────────────────────────────────────────────────────────────────────────
    # PROBE 2 — `superpose` into arithmetic: stream propagates through grounded
    # ─────────────────────────────────────────────────────────────────────────
    #
    # SPEC DERIVATION (before any code):
    #   `(superpose (10 20 30))` is the H-E primitive for explicitly
    #   constructing a stream {10, 20, 30} from a list. Surrounding
    #   context distributes over the stream: `(+ 1 X)` where X is the
    #   stream {10, 20, 30} produces the stream {11, 21, 31}. Collapse
    #   gathers it as Vector{Any} of length 3, set {11, 21, 31}.
    #
    # WHAT THIS PROBES:
    #   The grounded dispatch path. Today eager `evaled_args` collapses
    #   any non-scalar arg to a single value before calling the grounded
    #   function — `+` sees a Vector and fails to reduce. Under streaming
    #   the dispatch must enumerate all (1, stream_elem) combinations
    #   and call `+` once per pair. This is the eager-vs-lazy boundary
    #   where the eager decision still has to thread nondeterminism
    #   without becoming lazy — it's the load-bearing test for whether
    #   grounded calls participate in the stream.
    #
    @testset "PROBE 2 — superpose distributes into grounded `+`" begin
        S = _fresh()
        r = run_metta("!(collapse (+ 1 (superpose (10 20 30))))", S)
        @test length(r) == 1
        inner = r[1]
        @test_broken inner isa AbstractVector && length(inner) == 3 && Set(inner) == Set([11, 21, 31])
    end

    # ─────────────────────────────────────────────────────────────────────────
    # PROBE 3 — Chained match: deep-thread + binding independence (TOGETHER)
    # ─────────────────────────────────────────────────────────────────────────
    #
    # SPEC DERIVATION (before any code):
    #   Given:
    #     (Parent Bob Ann)
    #     (Parent Pam Ann)
    #     (Parent Cob Bob)
    #     (Parent Pop Pam)
    #   The query asks for grandparents of Ann via two chained match
    #   calls. Outer match binds $x to each direct parent of Ann; for
    #   each binding the inner match resolves $g as $x's parent. The
    #   stream is {Cob (via Bob), Pop (via Pam)}. Collapse: length 2,
    #   set {Cob, Pop}.
    #
    # WHAT THIS PROBES:
    #   This single test exercises BOTH steps 3 and 4 of the corrected
    #   resume sequence simultaneously:
    #     (a) `_eval_match` deep-thread — outer match's RESULTS must
    #         actually be evaluated through to the inner match, not
    #         returned as unevaluated substituted templates (today
    #         _eval_match_all does `_apply_bindings` without `eval_metta`)
    #     (b) immutable Bindings — the outer $x=Bob and $x=Pam branches
    #         must NOT clobber each other while the inner match runs in
    #         each branch; mutable Dict bindings shared across branches
    #         would corrupt this. This is the case where steps 3 and 4's
    #         coupling shows up — if you fix _eval_match's deep-thread
    #         on mutable bindings you'll see the clobber as "wrong
    #         grandparents," and you'll debug it as a match bug when
    #         it's actually the bindings substrate.
    #   Both must be right for this to pass. That makes the test the
    #   regression guard for the corrected step ordering (4 before 3).
    #
    @testset "PROBE 3 — chained match: deep-thread + branch-independent bindings" begin
        S = _fresh()
        run_metta(
            """
  (Parent Bob Ann)
  (Parent Pam Ann)
  (Parent Cob Bob)
  (Parent Pop Pam)
  """,
            S,
        )

        r = run_metta("!(collapse (match &self (Parent \$x Ann) (match &self (Parent \$g \$x) \$g)))", S)
        @test length(r) == 1
        inner = r[1]
        @test_broken inner isa AbstractVector && length(inner) == 2 && Set(inner) == Set([:Cob, :Pop])
    end

    # ─────────────────────────────────────────────────────────────────────────
    # PROBE 4 — Cartesian fan-out: two streams compose through grounded
    # ─────────────────────────────────────────────────────────────────────────
    #
    # SPEC DERIVATION (before any code):
    #   `(* (superpose (1 2)) (superpose (10 20)))` — two independent
    #   streams in arg positions of a binary grounded call. Per H-E,
    #   each stream contributes independently, so the result is the
    #   CARTESIAN product: {1*10, 1*20, 2*10, 2*20} = {10, 20, 20, 40}.
    #   Note 1*20 = 2*10 = 20, so as a multiset there are 4 elements
    #   with 20 appearing twice; as a set the cardinality is 3. The
    #   H-E spec preserves multiplicity in the result list, so the
    #   right assertion is on the LIST (sorted): [10, 20, 20, 40].
    #
    # WHAT THIS PROBES:
    #   The grounded-dispatch path must enumerate the cartesian product
    #   of stream args, not pick one arg's stream and broadcast. This
    #   is a stricter form of probe 2: instead of one scalar arg and
    #   one stream arg, both args are streams. If the implementation
    #   handles probe 2 by special-casing "one stream arg," this test
    #   catches that — both positions are streams, both must distribute.
    #
    @testset "PROBE 4 — cartesian fan-out: two superposes through `*`" begin
        S = _fresh()
        r = run_metta("!(collapse (* (superpose (1 2)) (superpose (10 20))))", S)
        @test length(r) == 1
        inner = r[1]
        @test_broken inner isa AbstractVector && length(inner) == 4 && sort(inner) == [10, 20, 20, 40]
    end
end
