# SWI §7.7 — scenarios ported from UPSTREAM's own `tests/tabling/test_reeval.pl`.
#
# ─── WHY THESE AND NOT MORE OF OURS ──────────────────────────────────────────────────────────────
# Every other tabling test in this tree was written by us, from the same reading of `pl-tabling.c`
# that produced the code it grades. That is a closed loop: a misreading becomes both the
# implementation and the assertion, and the suite goes green.
# (`[[feedback_oracle_must_observe_the_defect_class]]`.)
#
# `swipl-devel/tests/tabling/test_reeval.pl` has four groups — `dynamic_tabled` (L147),
# `dynamic_tabled2` (L169), `dynamic_tabled3` (L211), `dynamic_tabled4` (L238) — every one named
# `test(wfs, ...)`, because they all sit on the hardest interaction in the chapter: §7.7's
# incremental invalidation crossed with §7.6's conditional answers. All 18 upstream tabling files
# (165 tests) pass against the live `swipl` 10.1.12 — run
# `workflows/swipl_tabling_oracle.sh` — so these are behaviours with a known-good reference.
#
# ⚠️ WHAT IS PORTED IS THE PROPERTY, NOT THE PROGRAM. Upstream's programs are Prolog with dynamic
# predicates, `assert/retract`, and clause-body conjunction; ours is a MeTTa store with `add-atom`
# and rule reduction. Transliterating would be `[[feedback_native_julia_not_transliteration]]` in
# the other direction. What transfers is the CLAIM each test makes, and the claims are exact.
#
# ⚠️ AND THESE NEED THE IDG SWITCHED ON. `_IDG_RECORD[]` gates the whole graph, including the
# invalidation entry, so each testset sets it and restores it. A version of this file that forgot
# would pass vacuously — nothing would ever be invalidated and every "not invalidated" assertion
# would hold for the wrong reason. Hence the anti-vacuity assertions on `_IDG` below.

using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _UR = Eval

"Run `body` with the IDG recording on and every tabling registry cleared before AND after."
function _ur_isolated(body::Function)
    _UR.untable_all!(); _UR.abolish_all_tables!(); _UR.clear_idg!(); _UR.clear_dyn_deps!()
    _UR._IDG_RECORD[] = true
    try
        body()
    finally
        _UR._IDG_RECORD[] = false
        _UR.untable_all!(); _UR.abolish_all_tables!(); _UR.clear_idg!(); _UR.clear_dyn_deps!()
    end
end

"Keys of tables that went from valid to invalid across `mutate`."
function _ur_newly_invalid(mutate::Function)::Vector{Atom}
    before = Dict{Atom,Bool}(t => _UR.idg_is_invalid(t) for t in keys(_UR._IDG))
    mutate()
    Atom[t for t in keys(_UR._IDG) if _UR.idg_is_invalid(t) && !get(before, t, false)]
end

_ur_names(ts::Vector{Atom})::Vector{String} = String[string(t) for t in ts]

@testset "SWI §7.7 — upstream test_reeval.pl scenarios" begin

    # ── dynamic_tabled3 (test_reeval.pl:211-236): "Test that tnot creates a dependency" ──────────
    #
    # Upstream:
    #     p(X) :- tnot(qs(X)), tnot(p(X)).
    #     qs(X) :- q(X).                        % q/1 is `dynamic ... as incremental`
    # then `retract(q(1))` must reach p(1) — the residual becomes `p(1) :- tnot(p(1))`.
    #
    # 🔴 THE CLAIM: a NEGATIVE literal registers an IDG edge just as a positive one does. If `tnot`
    # only consulted the callee's table without recording that it did, the callee would be
    # invalidated on a store change and the NEGATING table would not — a stale answer that no
    # mutation can ever clear. Silent under-invalidation is the one failure an IDG must not have.
    @testset "tnot registers an IDG edge, so invalidation propagates through negation" begin
        _ur_isolated() do
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, "(fact a)\n")
            load_metta!(s, raw"(= (q) (match &self (fact a) True))" * "\n")
            load_metta!(s, raw"(= (p) (tnot (q)))" * "\n")
            _UR.table!(:q); _UR.table!(:p)

            # `q` succeeds (the fact is there), so `tnot(q)` fails and `p` has no answers.
            @test load_metta!(s, "!(q)\n") == Atom[Sym("True")]
            @test isempty(load_metta!(s, "!(p)\n"))

            # ANTI-VACUITY: with the IDG off this dict is empty and every claim below is free.
            @test length(_UR._IDG) == 2

            # THE EDGE ITSELF, asserted directly rather than only through its effect — a propagation
            # that works for some other reason would still satisfy the invalidation test alone.
            qn = only(k for k in keys(_UR._IDG) if string(k) == "(q)")
            pn = only(k for k in keys(_UR._IDG) if string(k) == "(p)")
            @test pn in _UR._IDG[qn].affected        # q's change reaches p …
            @test qn in _UR._IDG[pn].dependent       # … and p knows it consulted q

            # and it FIRES: touching the bucket `q` read invalidates BOTH tables.
            newly = _ur_names(_ur_newly_invalid() do
                load_metta!(s, "!(add-atom &self (fact b))\n")
            end)
            @test "(q)" in newly
            @test "(p)" in newly                     # ← the whole point of dynamic_tabled3
        end
    end

    # ── §7.7's invalidation ENTRY: per-table, not the revision stamp's all-or-nothing ─────────────
    #
    # Upstream reaches this through `dyn_changed_pattern/1` unifying the changed term against the
    # variant trie (`boot/tabling.pl:1807-1813`). We have one mutable space and no predicate
    # objects, so the graph's leaf is the store's own discriminant. The property to hold is the
    # same either way, and it is the property that distinguishes an IDG from a revision counter:
    # a mutation reaches the tables that READ that bucket and no others.
    @testset "an add-atom invalidates the table that read that bucket, and not its neighbour" begin
        _ur_isolated() do
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, "(edge a b)\n(edge b c)\n(color a)\n")
            load_metta!(s, raw"(= (reach $x $y) (match &self (edge $x $y) ($x $y)))" * "\n")
            load_metta!(s, raw"(= (hue $x) (match &self (color $x) $x))" * "\n")
            _UR.table!(:reach); _UR.table!(:hue)

            @test length(load_metta!(s, raw"!(reach $x $y)" * "\n")) == 2
            @test length(load_metta!(s, raw"!(hue $x)" * "\n")) == 1
            @test length(_UR._IDG) == 2                       # anti-vacuity, as above

            newly = _ur_names(_ur_newly_invalid() do
                load_metta!(s, "!(add-atom &self (edge c d))\n")
            end)
            @test any(occursin("reach", n) for n in newly)
            # 🔴 THE HALF THAT ACTUALLY DISCRIMINATES. The revision stamp evicts everything, so
            # "reach was invalidated" is true under both designs; only "hue was NOT" separates them.
            @test !any(occursin("hue", n) for n in newly)
        end
    end

    # ── the entry obeys the IDG's own switch ──────────────────────────────────────────────────────
    #
    # 🔴 THIS EXISTS BECAUSE THE FIRST VERSION DID NOT. `dyn_read!`/`dyn_changed!` ran on every
    # tabled read and every `add-atom` regardless of `_IDG_RECORD[]`, and `test_abstract.jl` — which
    # builds many abstracted variants, hence many nodes — went from 7.3 s to spinning at 98% CPU for
    # over five minutes without finishing. Unconditional bookkeeping for a feature nobody switched
    # on. A perf regression that large is a correctness statement about scope, so it gets an
    # assertion rather than a comment.
    @testset "with the IDG off, the invalidation entry records nothing" begin
        _UR.untable_all!(); _UR.abolish_all_tables!(); _UR.clear_idg!(); _UR.clear_dyn_deps!()
        _UR._IDG_RECORD[] = false
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, "(fact a)\n")
            load_metta!(s, raw"(= (q) (match &self (fact a) True))" * "\n")
            _UR.table!(:q)
            @test load_metta!(s, "!(q)\n") == Atom[Sym("True")]      # still answers correctly …
            @test isempty(_UR._DYN_DEPS)                             # … and records nothing
            @test isempty(_UR._DYN_ALL)
            @test isempty(_UR._IDG)
        finally
            _UR.untable_all!(); _UR.abolish_all_tables!(); _UR.clear_idg!(); _UR.clear_dyn_deps!()
        end
    end
end
