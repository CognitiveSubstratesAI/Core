# XSB's Well-Founded Semantics conformance corpus, run against OUR engine.
#
# ─── WHAT THIS IS ────────────────────────────────────────────────────────────────────────────────
# `swipl-devel/tests/xsb/wfs_tests/` holds 72 tiny programs, each opening with a machine-readable
# gold row written by the people who defined the semantics:
#
#     query(p10, p, [p,q,r], [], [p,q,r]).
#     %     name  goal  all-subgoals  TRUE-set  UNDEFINED-set
#
# A subgoal in neither set is FALSE. `verify_corpus.sh` checks all 72 against the live `swipl`
# 10.1.12 — 72 agree, 0 differ — so the table is safe to grade ourselves against.
#
# 🔴 WHY THIS FILE EXISTS AND `test_delays.jl` IS NOT ENOUGH. That file is mostly DNF ALGEBRA:
# `dnf_and` distributes, `dnf_or` dedups. Algebra assertions cannot see a wrong FIXPOINT — an engine
# with a perfect delay algebra over a broken alternating fixpoint passes every one of them. These
# programs state, per atom, which are true, which are undefined, and by omission which are false.
# That is the defect class our own tests could not observe
# (`[[feedback_oracle_must_observe_the_defect_class]]`) — and on its first full run it found one.
#
# ─── HOW THE PROGRAMS GET HERE ───────────────────────────────────────────────────────────────────
# `translate_corpus.sh` -> `wfs_programs.tsv`, one row per program: MeTTa source, the predicates to
# table, and the gold sets IN THE SAME NOTATION, all emitted from a single Prolog pass so a program
# and its expectation cannot drift apart. The translator REFUSES what it cannot handle (15 of 72,
# mostly the `win/1` graphs whose bodies read DATA and need a binding `match`) rather than guessing:
# a wrong translator produces confident wrong conformance, the worst artifact available here. The
# refusals are recorded as `# REFUSED` lines in the TSV, so the count that ran is the count we quote.
#
# The three `win/1` graphs are hand-translated below — the highest-value refusals, because they
# exercise the second translation path entirely and p12/p13 differ by ONE edge.

using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _XW = Eval

"""FIXED 2026-08-18 — kept as the record of what was wrong and how it was found.

p15/p17/p26/p27 reported every atom UNDEFINED where upstream says some are TRUE and the rest FALSE.
All 57 translated programs now match; this dict is empty and the loop below has no exemption branch.

⚠️ THE FIRST TWO EXPLANATIONS WERE WRONG, and both were plausible. Recorded because the wrong ones
survived review and only instrumentation killed them.
  1. "we fail to take the greatest unfounded set inside an SCC with negative edges" — refuted by
     tracing the fixpoint: K and U came back holding ⊥ for EVERY member including `s`, so the
     alternating fixpoint never had a chance. It was handed the wrong component.
  2. "§7.6.1 simplification is missing" — the neighbouring explanation. Simplification recovers an
     answer that BECAME unconditional; here no conditional answer was ever justified.

THE ACTUAL CAUSE was two absorbing sites in the INTERPRETER, not in the SLG engine at all:
  · `cons_atom` ran `propagated_undefined` on its arguments. The minimal-MeTTa interpreter REBUILDS
    a reduced expression with `cons-atom`, so ONE undefined argument collapsed the whole rebuilt
    expression before the rule could be applied — `(= (ignore1 \$x) (marker))` returned `undefined`
    even though it never uses `\$x`. `cons-atom` is a CONSTRUCTOR: `(f ⊥)` is a good term.
  · `unify_op` propagated ⊥ BEFORE attempting the match. Unifying ⊥ against a BARE VARIABLE succeeds
    — and `let` is defined as exactly that (`stdlib.metta:153`) — so every `let` over an undefined
    value collapsed. Narrowed to fire only when nothing matched, which preserves the anti-laundering
    property the audit added it for: ⊥ against a CONCRETE pattern still returns ⊥ rather than
    silently concluding the `else` branch.

Consequence, and why the SLG engine looked guilty: a truncated body never calls the literals after
the undefined one, so the tables they would have reached are never DISCOVERED, the component splits
(`_wfs_complete!` ran twice, on {p,s} then {q,r}, for four mutually-dependent atoms), and `tnot` on a
member of the other half fell through and returned ⊥. The fixpoint was correct throughout.
"""
const _XW_KNOWN_WRONG = Dict{String,String}()

"""One row of the corpus: the program, what to table, the goals asked, and the gold verdict.

`goals` are STRINGS because half the corpus asks about compound goals (`win(a)`), which a `Symbol`
cannot carry; `tabled` is separate because the `win/1` programs table ONE predicate and ask four
goals of it.
"""
struct XsbCase
    name::String
    program::String
    tabled::Vector{Symbol}
    goals::Vector{String}
    true_set::Vector{String}
    undef_set::Vector{String}
end

_xw_split(s::AbstractString)::Vector{String} =
    isempty(strip(s)) ? String[] : String[String(strip(x)) for x in split(s, ",")]

"Read `wfs_programs.tsv`. Comment lines carry the refusals and are skipped."
function _xw_load(path::AbstractString)::Vector{XsbCase}
    out = XsbCase[]
    for line in eachline(path)
        startswith(line, "#") && continue
        f = split(line, '\t')
        length(f) == 6 || continue
        push!(out, XsbCase(String(f[1]),
                           replace(String(f[3]), "\\n" => "\n") * "\n",
                           Symbol[Symbol(t) for t in _xw_split(f[2])],
                           _xw_split(f[4]), _xw_split(f[5]), _xw_split(f[6])))
    end
    out
end

"Flatten what `load_metta!` returns — a query may yield a vector of vectors."
function _xw_answers(s::Space, goal::AbstractString)::Vector{Atom}
    out = Atom[]
    for y in load_metta!(s, "!$goal\n")
        y isa AbstractVector ? append!(out, y) : push!(out, y)
    end
    out
end

"Classify each goal as TRUE / UNDEFINED / FALSE and return the first two as sorted sets."
function _xw_run(c::XsbCase)::Tuple{Vector{String},Vector{String}}
    _XW.untable_all!(); _XW.abolish_all_tables!()
    s = Space(); load_core_stdlib!(s)
    isempty(strip(c.program)) || load_metta!(s, c.program)
    for t in c.tabled
        _XW.table!(t)
    end
    got_true = String[]; got_undef = String[]
    for g in c.goals
        a = _xw_answers(s, g)
        if isempty(a)
            # FALSE — no answer at all. Recorded by omission, exactly as the gold rows do.
        elseif all(_XW.is_undefined, a)
            push!(got_undef, g)
        else
            push!(got_true, g)
        end
    end
    (sort(got_true), sort(got_undef))
end

# ─── THE HAND-TRANSLATED win/1 GRAPHS ────────────────────────────────────────────────────────────
# One rule, three graphs: `win(A) :- m(A,B), tnot(win(B)).` — a position is winning iff it has a move
# to a LOSING one. The translator refuses these because `m(A,B)` is DATA, not a call: it becomes a
# BINDING `match` whose `let` binder carries the successor rather than being discarded.
# Goals are asked GROUND because our `tnot` raises instantiation_error otherwise; the gold sets are
# per-position, so nothing is lost.
const _XW_WIN_RULE = raw"(= (win $a) (let $b (match &self (m $a $b) $b) (tnot (win $b))))" * "\n"

const _XW_HAND = XsbCase[
    # p11: m(a,b). m(b,c). m(c,d). m(b,d).  — a DAG, so everything is decided.
    #      d has no move -> lost; c->d -> won; b->d -> won; a->b(won) only -> lost.
    XsbCase("p11", "(m a b)\n(m b c)\n(m c d)\n(m b d)\n" * _XW_WIN_RULE,
            [:win], ["(win a)", "(win b)", "(win c)", "(win d)"], ["(win b)", "(win c)"], String[]),

    # p12: m(a,b). m(b,a). m(b,c).  — a 2-cycle a<->b PLUS an escape b->c. c is lost, so b is WON via
    #      c, and a's only move is to b (won), so a is lost. The cycle does NOT make these undefined:
    #      the escape decides them, which is the point of the case.
    XsbCase("p12", "(m a b)\n(m b a)\n(m b c)\n" * _XW_WIN_RULE,
            [:win], ["(win a)", "(win b)", "(win c)"], ["(win b)"], String[]),

    # p13: m(a,b). m(b,a). m(b,c). m(c,d).  — the SAME 2-cycle, but the escape now leads to a WON
    #      position. d lost -> c won; b's moves are a (undecided) and c (won); the a<->b cycle no
    #      longer has an escape that settles it, so BOTH are UNDEFINED while c stays TRUE.
    #      One extra edge flips two atoms from decided to undefined — the tightest discriminator here.
    XsbCase("p13", "(m a b)\n(m b a)\n(m b c)\n(m c d)\n" * _XW_WIN_RULE,
            [:win], ["(win a)", "(win b)", "(win c)", "(win d)"], ["(win c)"], ["(win a)", "(win b)"]),
]

@testset "XSB wfs_tests corpus — our engine vs upstream's gold rows" begin
    generated = _xw_load(joinpath(@__DIR__, "wfs_programs.tsv"))
    cases = vcat(generated, _XW_HAND)

    # ANTI-VACUITY. A regenerated TSV that came out empty — missing swipl, a renamed upstream path —
    # would otherwise make every claim below hold over nothing at all.
    @test length(generated) == 57
    @test length(cases) == 60
    @test any(!isempty(c.undef_set) for c in cases)      # …and UNDEFINED is genuinely exercised

    for c in cases
        @testset "$(c.name)" begin
            try
                (got_true, got_undef) = _xw_run(c)
                # No exemptions. `_XW_KNOWN_WRONG` is empty and kept as documentation; when it held
                # four entries the `@test_broken` reported the FIX as an error (`test_unbroken` ×8),
                # which is exactly how an exemption should end.
                @test got_true  == sort(c.true_set)
                @test got_undef == sort(c.undef_set)
            finally
                _XW.untable_all!(); _XW.abolish_all_tables!()
            end
        end
    end
end
