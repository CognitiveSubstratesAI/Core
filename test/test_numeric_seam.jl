# test_numeric_seam.jl — the Int/Float boundary, pinned against the reference.
#
# WHY THIS FILE EXISTS. Three divergences from hyperon-experimental were MEASURED on 2026-08-05 while
# Core was passing 234/234 hyperon conformance, LeaTTa 270/270 with CORE_BUG=0, health 5/5 and the
# full suite. Nothing we run could see them, and the reason is structural, not luck:
#
#   The LeaTTa oracle gate is transitive by design — it runs Hyperon's own UNMODIFIED 270-directive
#   corpus and checks Core passes it. It therefore inherits Hyperon's coverage exactly. Across all
#   270 directives the numeric seam appears TWICE:
#       c1_grounded_basic.metta:12   (- 8 (/ 4 6.4))   ← `/` with a FLOAT operand; never Int ÷ Int
#       c1_grounded_basic.metta:16   (% 21 17)         ← `%` with a NON-ZERO divisor
#   and no integer above 6 digits appears anywhere. LeaTTa PROVES the zero-divisor branch in Lean
#   (MettaHyperonFull/Minimal/Stdlib.lean:86-101) and nothing that gates us ever invokes it.
#
#   That corpus is vendored VERBATIM from upstream, so it cannot be extended. These tests must be
#   Core-side. That is the whole reason for this file.
#
# WHY @test_broken RATHER THAN @test. Asserting the correct values would redden the suite for a
# decision that has not been taken (see docs/NUMERIC_SEAM_DIVERGENCES_2026-08-05.md). Pinning the
# CURRENT values would cement the bug. `@test_broken` does neither: it records the divergence, keeps
# the suite green, and reports "Unexpected Pass" the moment the behaviour is fixed — which forces
# whoever fixes it to come here and turn the line into a real assertion.
#
# Full evidence, the four-way comparison, and the open bignum decision:
#   Core/docs/NUMERIC_SEAM_DIVERGENCES_2026-08-05.md
using Test
using MeTTaCore

const _NS = MeTTaCore.Interpreter
const _NSP = (s = _NS.Space(); _NS.load_core_stdlib!(s); s)
_nsval(a) = a isa _NS.Grounded ? a.value :
            a isa _NS.Sym ? Symbol(a.name) :
            a isa _NS.Expression ? Any[_nsval(c) for c in a.children] : a
nsq(src) = (r = _NS.load_metta!(_NSP, src); isempty(r) ? nothing : _nsval(r[1]))

@testset "numeric seam — Int/Float boundary vs the reference" begin

    @testset "CONFORMANT: i64 wraparound matches hyperon byte-for-byte" begin
        # NOT a bug. hyperon is Number{Integer(i64),Float(f64)} (hyperon-atom/src/gnd/number.rs:7-11)
        # with PLAIN Rust operators — no wrapping_/checked_/saturating_ — shipping release builds with
        # overflow-checks=false. Measured on upstream's OWN prebuilt release binary:
        #     !(* 99999999999 99999999999)  ->  1864711849423024129
        # which is byte-identical to ours. Pinned so that adding bignum promotion (CeTTa's choice —
        # int64 fast path promoting to GMP on __int128-detected overflow) FAILS HERE and forces the
        # decision to be explicit rather than arriving as a side effect.
        @test nsq("!(+ 9223372036854775807 1)") == -9223372036854775808
        @test nsq("!(* 99999999999 99999999999)") == 1864711849423024129
    end

    @testset "CONFORMANT: what the vendored corpus does cover" begin
        # The two seam directives that DO exist upstream — kept here so this file also documents the
        # boundary of the inherited coverage, not just the gaps.
        @test nsq("!(% 21 17)") == 4          # non-zero divisor
        @test nsq("!(/ 4 6.4)") ≈ 0.625       # Float operand ⇒ Float, agreed by everyone
    end

    @testset "DIVERGENCE 1 — Int ÷ Int must yield an Int" begin
        # hyperon `/` is hand-written; its Integer/Integer branch returns Number::Integer(a / b)
        #   (lib/src/metta/runner/stdlib/arithmetics.rs:154-155) — Rust truncating division.
        # LeaTTa PROVES the same: divOp → Ground.int (a / b) (MettaHyperonFull/Minimal/Stdlib.lean:91).
        # CeTTa likewise returns an int.
        # Core: Interpreter.jl:403 `_num_binop("/", /)` uses Julia's `/`, which promotes to Float64.
        @test_broken nsq("!(/ 7 2)") == 3
        @test_broken nsq("!(/ -7 2)") == -3

        # The TYPE differs even when the value is exact — this is the sharper half. hyperon's Number
        # equality is loose so 2.0 == 2 may hold, but `get-type` and any type-directed dispatch see
        # a Float where the reference has an Integer.
        @test_broken nsq("!(/ 4 2)") isa Integer
    end

    @testset "DIVERGENCE 2 — division by zero must not escape as a host exception" begin
        # Under MeTTa's partial semantics a bad argument reduces to inert or to an error atom so
        # nondeterministic evaluation continues on other branches. Core throws a raw Julia
        # DivideError straight through the evaluator.
        #
        # ALREADY HALF-HANDLED, and the two lanes disagree: Primitives.jl:44-46 DECLINES on the MORK
        # lane rather than throwing, with the comment "The interpreter's own `%` DOES currently throw
        # here; tracked separately, since changing it needs the hyperon oracle to say what (% 7 0)
        # should produce." THE ORACLE HAS ANSWERED: hyperon guards DivisionByZero (arithmetics.rs:154)
        # and LeaTTa's modOp returns `Error (% a b) DivisionByZero`
        # (MettaHyperonFull/Minimal/Stdlib.lean:95-101, docstring citing "Hyperon's checked_div").
        # `%` by zero THROWS. Must reduce instead.
        @test_broken (try nsq("!(% 7 0)"); true catch; false end)

        # `/` by zero does NOT throw — it returns Inf, because Core has no Int÷Int path at all and
        # promotes to Float first. (Caught by @test_broken reporting "Unexpected Pass" on an earlier
        # version of this test that only asserted "must not throw" — which passed trivially. The
        # mechanism found a wrong assumption in the test itself on its first run.)
        #
        # LeaTTa's divOp docstring draws the line exactly: "Integer division by zero raises a
        # DivisionByZero error (Hyperon's checked_div); float division follows IEEE (x/0.0 = ±inf)".
        # So Inf is CORRECT for floats and WRONG for ints — the same root cause as divergence 1.
        @test nsq("!(/ 7 0)") == Inf              # current behaviour, pinned
        @test_broken nsq("!(/ 7 0)") != Inf       # should be a DivisionByZero error atom
        # ⚠️ `!== NaN` would be VACUOUS — NaN is never === itself, so that comparison is true for
        # every value. @test_broken caught it as a second "Unexpected Pass". Use isnan.
        @test_broken !isnan(nsq("!(/ 0 0)"))      # currently NaN; should be a DivisionByZero error
    end

    @testset "CONFORMANT: float division by zero IS IEEE" begin
        # Explicitly the correct half of the above, so a future fix to the Int path does not
        # over-reach and turn float division into an error too.
        @test nsq("!(/ 7.0 0.0)") == Inf
    end

    @testset "DIVERGENCE 3 — an out-of-range literal must not silently become a Float" begin
        # Parser.jl:108-112 does tryparse(Int, token) and, on failure, FALLS THROUGH to
        # tryparse(Float64, token) — so the literal parses with its precision gone and no diagnostic.
        # hyperon registers the integer literal as a FALLIBLE token precisely so this can fail
        # (arithmetics.rs:163-164), erroring with "Could not parse integer: … number too large to fit
        # in target type".
        #
        # Note this is INDEPENDENT of the bignum decision: whether Core wraps (hyperon today) or
        # promotes (CeTTa), silently reinterpreting an integer literal as a Float is wrong under both.
        @test_broken !(nsq("!(+ 9223372036854775808 0)") isa AbstractFloat)
        @test_broken !(nsq("!(+ 99999999999999999999999 1)") isa AbstractFloat)
    end

    @testset "the two lowerings of + - * / % are not co-located and disagree" begin
        # Interpreter.jl:403 `_num_binop` and Primitives.jl:32 `_register_arithmetic!` implement the
        # same five operators in different files. They already differ on (% 7 0). Recorded here so the
        # count is visible; the fix is one module owning the seam, not a patch to either lane.
        # Agreement on the ordinary cases is real and worth keeping green while that is designed.
        @test nsq("!(+ 2 3)") == 5
        @test nsq("!(- 8 3)") == 5
        @test nsq("!(* 6 7)") == 42
        @test nsq("!(% 21 17)") == 4
    end
end
