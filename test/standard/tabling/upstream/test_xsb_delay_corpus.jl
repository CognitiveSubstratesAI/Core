# XSB's delay_tests conformance corpus, run against OUR engine.
#
# ─── WHY THIS EXISTS ALONGSIDE test_xsb_wfs_corpus.jl ────────────────────────────────────────────
# `upstream/README.md` names the blindness this closes: our own `test_delays.jl` is mostly DNF
# ALGEBRA — `dnf_and` distributes, `dnf_or` dedups — and "algebra assertions cannot see a wrong
# FIXPOINT". The wfs corpus closed that for well-founded truth values generally. THESE programs are
# the ones upstream wrote specifically to exercise DELAY: dynamically-stratified programs that are
# not stratified left-to-right, where "delay is necessary for the correct evaluation ... the negation
# suspension transformation is not enough" (dynstrat2.P's own header).
#
# ─── THE GOLD IS STRONGER HERE THAN IN wfs_tests ─────────────────────────────────────────────────
# wfs_tests ships TRUE and UNDEFINED, with FALSE implied by omission from the subgoal list.
# delay_tests records upstream's actual STDOUT, which states each literal explicitly:
#     p. p is false (OK)          s. s is true (OK)
# so `delay_programs.tsv` carries TRUE, FALSE **and** UNDEF as three separate sets, and this file
# asserts all three. An engine that silently drops a literal from consideration entirely — neither
# proving nor refuting it — fails here and would have passed the wfs shape.
#
# ─── §7.6.1: WE PASS ALL NINE PROGRAMS UPSTREAM LABELS AS NEEDING IT ─────────────────────────────
#
# 🟢 MEASURED 2026-08-27, and it is the most interesting thing this corpus has said so far. All 49
# translatable programs produce the CORRECT well-founded model on all three sets — including the 9
# that `xsb_test_delay.pl` labels "Needs n simplification" / "Needs p+n simplification". They were
# first wired as `@test_broken`; the suite reported NINE Unexpected Passes (27 assertions), which is
# exactly the signal `@test_broken` exists to give.
#
# ⇒ THE LABEL DESCRIBES XSB's EVALUATION STRATEGY, NOT THE SEMANTICS. "Needs n simplification" means
# XSB's delay-and-simplify pipeline requires that step to reach the right answer; it does not mean the
# well-founded model is unreachable without it. Our engine gets there by a different route.
# ⚠️ WHICH ROUTE IS **NOT ESTABLISHED HERE**. The obvious hypothesis is that we compute the
# alternating fixpoint directly rather than via delay+simplify, but grepping Eval.jl for
# alternating/Van-Gelder/fixpoint found nothing, so that is UNVERIFIED and deliberately not asserted.
# What is verified is the observation: 9 of 9 pass without §7.6.1.
#
# ⇒ SO THE LABEL IS KEPT IN THE TSV AS INFORMATION AND DRIVES NOTHING. A `@test_broken` that never
# breaks is worse than no exemption: it trains the reader to expect failure where there is none.
# `gfp` — the one needing CASCADING simplification — is refused at the gold stage (its output is not
# truth-values), so it is NOT evidence either way and remains the open question for §7.6.1.
#
# ─── (historical) THE CLASSIFICATION THIS REPLACED ───────────────────────────────────────────────
# We deliberately did not build §7.6.1 answer simplification. Upstream pre-labels which programs need
# it, in `xsb_test_delay.pl`:
#     xsb_test(dynstrat1).        % Needs n simplification
#     xsb_test(gfp).              % Needs cascading simplifications
# `translate_delay_corpus.sh` carries that label into column 7, and those cases run as `@test_broken`.
# 🔑 THAT IS THE POINT OF `@test_broken` RATHER THAN A SKIP: it reports a FIX AS AN ERROR, so when
# §7.6.1 lands these flip loudly instead of sitting exempt forever. The same mechanism retired eight
# entries from the wfs corpus's known-wrong list.
# ⚠️ The label must be read as "Needs …", NOT as a substring match on "simplification" — upstream
# writes "No simplification" too, and a substring test mislabels six programs. See the generator.
#
# ─── ANTI-VACUITY ────────────────────────────────────────────────────────────────────────────────
# A regenerated TSV that came out empty (missing swipl, renamed upstream path) would make every
# assertion below hold over nothing. The counts are pinned, as in the wfs file.

using Test
using MeTTaCore
using MeTTaCore.Eval
const _XD = MeTTaCore.Eval
using MeTTaCore.Eval: Space, load_core_stdlib!, load_metta!, Atom

struct DelayCase
    name::String
    program::String
    tabled::Vector{Symbol}
    true_set::Vector{String}
    false_set::Vector{String}
    undef_set::Vector{String}
    needs_simplification::String
end

_xd_split(s::AbstractString)::Vector{String} =
    isempty(strip(s)) ? String[] : String[String(strip(x)) for x in split(s, ",")]

"Read `delay_programs.tsv`. Comment lines carry the refusals and are skipped."
function _xd_load(path::AbstractString)::Vector{DelayCase}
    out = DelayCase[]
    for line in eachline(path)
        startswith(line, "#") && continue
        f = split(line, '\t')
        length(f) == 7 || continue
        push!(out, DelayCase(String(f[1]),
                             replace(String(f[3]), "\\n" => "\n") * "\n",
                             Symbol[Symbol(t) for t in _xd_split(f[2])],
                             _xd_split(f[4]), _xd_split(f[5]), _xd_split(f[6]),
                             String(f[7])))
    end
    out
end

"Flatten what `load_metta!` returns — a query may yield a vector of vectors."
function _xd_answers(s::Space, goal::AbstractString)::Vector{Atom}
    out = Atom[]
    for y in load_metta!(s, "!$goal\n")
        y isa AbstractVector ? append!(out, y) : push!(out, y)
    end
    out
end

"""
Classify every goal the gold mentions as TRUE / FALSE / UNDEFINED.

Unlike the wfs harness this returns the FALSE set explicitly rather than leaving it implied, because
the gold states it. `no answer at all` is false; `every answer undefined` is undefined; anything else
is true — the same three-way reading the wfs file uses, just with the third bucket kept.
"""
function _xd_run(c::DelayCase)::NTuple{3, Vector{String}}
    _XD.untable_all!()
    _XD.abolish_all_tables!()
    s = Space()
    load_core_stdlib!(s)
    isempty(strip(c.program)) || load_metta!(s, c.program)
    for t in c.tabled
        _XD.table!(t)
    end
    got_true, got_false, got_undef = String[], String[], String[]
    for g in sort(vcat(c.true_set, c.false_set, c.undef_set))
        a = _xd_answers(s, g)
        if isempty(a)
            push!(got_false, g)
        elseif all(_XD.is_undefined, a)
            push!(got_undef, g)
        else
            push!(got_true, g)
        end
    end
    (sort(got_true), sort(got_false), sort(got_undef))
end

@testset "XSB delay_tests corpus — our engine vs upstream's recorded output" begin
    cases = _xd_load(joinpath(@__DIR__, "delay_programs.tsv"))

    # ANTI-VACUITY — see the header.
    @test length(cases) == 49
    @test count(c -> !isempty(c.needs_simplification), cases) == 9
    @test any(!isempty(c.false_set) for c in cases)      # FALSE is genuinely asserted, not vacuous
    @test any(!isempty(c.true_set) for c in cases)

    for c in cases
        @testset "$(c.name)" begin
            try
                (got_true, got_false, got_undef) = _xd_run(c)
                # NO EXEMPTIONS. Every program is asserted plainly — see the §7.6.1 note in the header.
                @test got_true == sort(c.true_set)
                @test got_false == sort(c.false_set)
                @test got_undef == sort(c.undef_set)
            finally
                _XD.untable_all!()
                _XD.abolish_all_tables!()
            end
        end
    end
end
