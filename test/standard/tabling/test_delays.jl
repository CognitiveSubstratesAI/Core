# test_delays.jl — DELAY LISTS / CONDITIONAL ANSWERS. SWI §7.6, roadmap 7.A–7.D.
#
# Under WFS an answer is TRUE, FALSE or UNDEFINED. SWI records the third case CONSTRUCTIVELY: the
# answer is stored with the literals whose truth is unknown — its DELAY LIST — so "undefined" carries
# a reason. We had the third truth value already (the alternating fixpoint computes the same model);
# what we did not have is the REASON, which is what `answer_residual/2` exists to report.
#
# 🔴 THE ADAPTATION THIS FILE PINS: the condition RIDES ON THE VALUE. SWI keeps it in a trail-scoped
# thread-global and scrapes it at insertion time, correct there because the engine runs exactly ONE
# derivation and the trail erases abandoned ones. We map over a COLLECTION of values, so there is no
# "current branch" at insertion and a literal port would leak value #1's condition onto value #2 with
# no trail to unwind it. `WFSBottom` carrying its own DNF is what replaces the register.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _DL = Eval

_dl_key(n::Symbol) = Sym(n)

@testset "SWI §7.6 — delay lists / conditional answers" begin

    @testset "the DNF algebra: empty is the UNIT, and conjunction DISTRIBUTES" begin
        # 🔴 EMPTY IS THE UNIT, NOT THE ZERO. An unconditional answer conjoined with a conditional one
        # is the conditional one. Reading empty as "false" inverts the lattice and makes every
        # combination unconditional — the mistake is easy because "no delays" reads like "nothing".
        p, q = _dl_key(:p), _dl_key(:q)
        dp = _DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(p)])])
        dq = _DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(q)])])
        empty = _DL.DelayDNF()

        @test _DL.dnf_and(empty, dp) == dp
        @test _DL.dnf_and(dp, empty) == dp
        @test length(_DL.dnf_and(dp, dq)) == 1          # one conjunction…
        @test length(_DL.dnf_and(dp, dq)[1]) == 2       # …of two literals

        # A ∧ A = A, and C ∨ C = C — a fixpoint re-deriving an answer must not grow the condition
        @test _DL.dnf_and(dp, dp) == dp
        @test length(_DL.dnf_or(dp, dp)) == 1
        @test length(_DL.dnf_or(dp, dq)) == 2

        # DISTRIBUTION: (A∨B) ∧ (C∨D) = AC ∨ AD ∨ BC ∨ BD. This is the operation upstream does NOT
        # need — it conjoins by pushing onto the ambient register, so the other conjunct is whatever
        # the current derivation already put there. With no current derivation, it must be written.
        r, s2 = _dl_key(:r), _dl_key(:s)
        ab = _DL.dnf_or(dp, dq)
        cd = _DL.dnf_or(_DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(r)])]),
                        _DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(s2)])]))
        @test length(_DL.dnf_and(ab, cd)) == 4
    end

    @testset "7.B — the THIRD kind exists, and NOTHING produces it yet" begin
        # Upstream has exactly two kinds, encoded by `answer == NULL`. In a value language the natural
        # negations are `(not (f a))` AND `(not (== (f a) 3))`, and upstream's struct has nowhere to
        # put the 3. The kind exists because 7.B settles a STRUCT FIELD and the struct is being
        # written now — adding it later means rewriting every consumer.
        #
        # ⚠️ AND ASSERTING THAT NO SITE PRODUCES IT is the honest half. Our `tnot` is table-level (it
        # requires a ground goal and asks whether the table is EMPTY), so only two kinds are
        # reachable. Without this assertion the enum would read as implemented.
        v, a = _dl_key(:v), Grounded(3)
        @test _DL.delay_negative(v).answer === nothing
        @test _DL.delay_positive(v, a).answer == a
        @test _DL.delay_negative_answer(v, a).kind == _DL.DELAY_NEGATIVE_ANSWER

        @test string(_DL.delay_negative(v))            == "(not v)"
        @test string(_DL.delay_negative_answer(v, a))  == "(not (== v 3))"
    end

    @testset "the residual RENDERS, and the unit cases collapse" begin
        p, q = _dl_key(:p), _dl_key(:q)
        @test _DL.dnf_residual(_DL.DelayDNF()) == Sym("True")     # unconditional
        one = _DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(p)])])
        @test string(_DL.dnf_residual(one)) == "(not p)"          # no needless (and …)
        two = _DL.dnf_and(one, _DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(q)])]))
        @test string(_DL.dnf_residual(two)) == "(and (not p) (not q))"
        @test occursin("or", string(_DL.dnf_residual(_DL.dnf_or(one,
                       _DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(q)])])))))
    end

    @testset "🔴 is_undefined IS A TYPE TEST — `== UNDEFINED` is now WRONG" begin
        # The whole sweep that preceded this feature. ~34 sites asked `x == UNDEFINED`, which worked
        # only while the bottom was a singleton. A residuated bottom is NOT `==` to the bare constant,
        # so every one of those sites would have quietly answered FALSE and treated it as an ordinary
        # value — a silent soundness bug in the strict-op layer. This asserts the new contract.
        r = _DL.undefined_with(_DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(_dl_key(:p))])]))
        @test _DL.is_undefined(r)
        @test _DL.is_undefined(_DL.UNDEFINED)
        @test r != _DL.UNDEFINED                       # …and THIS is why the predicate had to land
        @test !_DL.is_undefined(Sym("True"))
        @test !_DL.is_undefined(Grounded(1))
    end

    @testset "CONTAGION CONJOINS — an incomplete residual is worse than none" begin
        # `(+ ⊥{p} ⊥{q})` is undefined because of p AND q. Returning whichever was scanned first is
        # sound (still undefined) but reports a condition that is INCOMPLETE while reading as
        # authoritative. `propagated_undefined` conjoins instead.
        p, q = _dl_key(:p), _dl_key(:q)
        up = _DL.undefined_with(_DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(p)])]))
        uq = _DL.undefined_with(_DL.DelayDNF([_DL.DelaySet([_DL.delay_negative(q)])]))
        both = _DL.propagated_undefined(Atom[up, Grounded(1), uq])
        @test both !== nothing
        @test _DL.is_undefined(both::Atom)
        @test length(_DL.delays_of(both::Atom)) == 1          # one conjunction…
        @test length(_DL.delays_of(both::Atom)[1]) == 2       # …naming BOTH reasons
        @test _DL.propagated_undefined(Atom[Grounded(1), Sym(:a)]) === nothing
    end

    @testset "🔴🔴 END TO END — a real paradox produces a real RESIDUAL" begin
        # ANTI-VACUITY IS THE POINT. Every structural test above passes on an implementation whose
        # residual is always `True`, because `True` IS the correct answer for an unconditional value.
        # So this drives the canonical WFS paradox and asserts the residual is NOT True, and NAMES the
        # goal it is stuck on. `[[feedback_parses_is_not_fires]]`
        _DL.untable_all!(); _DL.abolish_all_tables!()
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, raw"(= (p) (tnot (q)))" * "\n" * raw"(= (q) (tnot (p)))" * "\n")
            _DL.table!(:p); _DL.table!(:q)
            out = load_metta!(s, "!(p)\n")
            vals = Atom[x for y in out for x in (y isa AbstractVector ? y : [y])]

            @test length(vals) == 1
            u = vals[1]
            @test _DL.is_undefined(u)                       # the paradox IS undefined — as before…
            @test string(u) == "undefined"                  # …and PRINTS the same, so oracles hold

            # …but it now carries WHY, and that is the new capability
            res = _DL.answer_residual(u)
            @test res != Sym("True")                        # ANTI-VACUITY: a reason was recorded
            @test occursin("not", string(res))              # …a NEGATIVE delay…
            @test occursin("q", string(res))                # …naming the goal it is stuck on
        finally
            _DL.untable_all!(); _DL.abolish_all_tables!()
        end
    end

    @testset "an UNCONDITIONAL answer has residual True — and so does an unrecorded bottom" begin
        # The two are indistinguishable from `answer_residual`, deliberately: empty means NO
        # INFORMATION, never "unsatisfiable". A consumer that reads empty as false would call a real
        # answer impossible, which is the inverted-lattice failure again, one layer up.
        @test _DL.answer_residual(Grounded(42)) == Sym("True")
        @test _DL.answer_residual(_DL.UNDEFINED) == Sym("True")
        @test isempty(_DL.delays_of(Grounded(42)))
    end
end
