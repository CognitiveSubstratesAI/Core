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
# and its expectation cannot drift apart. The translator REFUSES what it cannot handle (2 of 72, down
# from 15 once it learned the binding-`match` form) rather than guessing:
# a wrong translator produces confident wrong conformance, the worst artifact available here. The
# refusals are recorded as `# REFUSED` lines in the TSV, so the count that ran is the count we quote.
#
# 🔴 2026-08-27 — 69 TRANSLATED / 3 REFUSED, AND BOTH NUMBERS MOVED FOR REASONS WORTH READING.
# FIRST, the two old "refusals" were a BUG, NOT A
# SHAPE IT COULD NOT HANDLE. `term_metta/2` had no clause for NUMBERS (`atom/1` and `compound/1` are
# both false for an integer), so `term_metta(a(0), _)` FAILED. Worse, that failure sat in the ACTION
# of an if-then-else, where a failure does not fall through to the `refused` branch — the clause was
# dropped from `findall/3` with no row, no REFUSED line and no error. Consequences, all measured:
#   * p29, p36 reported as "clause shape not handled" — they translate fine.
#   * p37 lost all four of its data facts, and p60 likewise.
#   * BOTH had EMPTY gold sets (`goals_metta` calls the same `term_metta`), so they compared empty
#     against empty and PASSED VACUOUSLY. Two rows of this corpus were asserting nothing at all.
# Found while building the delay_tests corpus, from `nonstrat2`'s missing `a(0).`.
#
# SECOND — and this is why the count went DOWN, not up to 72. Un-refusing p29 exposed a defect that
# had been in the corpus all along: `binder_of/3` gives a CALL the throwaway binder `$cN`, i.e. it
# DISCARDS the call's result. Correct for a ground test; WRONG for a generative call:
#     p29:  w(A) :- e(B,A), tnot(w(B)).      % e(B,A) BINDS B; we emitted `$v1` free inside tnot
# p29 then did not terminate (>420s; every other program finishes under 8s). p60 and p80 carried the
# same defect while TRANSLATED — and p60 also had the empty gold above, so it passed vacuously.
# All three are now REFUSED with a precise reason. p46 is deliberately NOT refused: its call-bound
# variable is a SINGLETON (`r :- p(_A).` is an existence test), so discarding it is harmless.
# ⇒ 69 sound rows is worth more than 72 rows of which three are wrong. Threading a call's answers
# into the continuation is a real translation mode (the DATA literal already has one, via `match`) —
# it is the next increment here, not a tweak.
#
# 🔑 THE THREE `win/1` GRAPHS ARE NOW A TRANSLATOR CROSS-CHECK, NOT A GAP-FILLER. They were
# hand-translated on 2026-08-18 because the translator refused them; on 2026-08-19 it learned the
# binding-`match` form and generates them itself — producing, for p13, EXACTLY the hand-written form:
#     (= (win $v0) (let $v1 (match &self (m $v0 $v1) $v1) (tnot (win $v1))))
# So they are deliberately kept and run TWICE: once as the translator emits them, once as a human
# wrote and verified them. A translator that silently drifts is the failure mode this corpus cannot
# otherwise see — its output would still look like conformance evidence.

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
const _XW_KNOWN_WRONG = Dict{String, String}()   # ✅ EMPTY — p31 FIXED 2026-08-19 (roadmap 7.B)

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
        push!(
            out,
            XsbCase(String(f[1]),
                replace(String(f[3]), "\\n" => "\n") * "\n",
                Symbol[Symbol(t) for t in _xw_split(f[2])],
                _xw_split(f[4]), _xw_split(f[5]), _xw_split(f[6]))
        )
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
function _xw_run(c::XsbCase)::Tuple{Vector{String}, Vector{String}}
    _XW.untable_all!()
    _XW.abolish_all_tables!()
    s = Space()
    load_core_stdlib!(s)
    isempty(strip(c.program)) || load_metta!(s, c.program)
    for t in c.tabled
        _XW.table!(t)
    end
    got_true = String[]
    got_undef = String[]
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
const _XW_WIN_RULE =
    raw"(= (win $a) (let $b (match &self (m $a $b) $b) (tnot (win $b))))" * "\n"

const _XW_HAND = XsbCase[
    # p11: m(a,b). m(b,c). m(c,d). m(b,d).  — a DAG, so everything is decided.
    #      d has no move -> lost; c->d -> won; b->d -> won; a->b(won) only -> lost.
    XsbCase("p11", "(m a b)\n(m b c)\n(m c d)\n(m b d)\n" * _XW_WIN_RULE,
        [:win], ["(win a)", "(win b)", "(win c)", "(win d)"], ["(win b)", "(win c)"],
        String[]),

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
        [:win], ["(win a)", "(win b)", "(win c)", "(win d)"], ["(win c)"],
        ["(win a)", "(win b)"])
]

@testset "XSB wfs_tests corpus — our engine vs upstream's gold rows" begin
    generated = _xw_load(joinpath(@__DIR__, "wfs_programs.tsv"))
    cases = vcat(generated, _XW_HAND)

    # ANTI-VACUITY. A regenerated TSV that came out empty — missing swipl, a renamed upstream path —
    # would otherwise make every claim below hold over nothing at all.
    # 72/0 since 2026-08-27: the two "refusals" were never a clause-shape limit — `term_metta/2`
    # had no clause for NUMBERS, so `a(0)` failed and the clause vanished. Fixing that also filled
    # in p37's and p60's gold sets, which had been EMPTY — i.e. those two were passing VACUOUSLY.
    @test length(generated) == 69
    @test length(cases) == 72
    # …and no row may carry an empty gold on BOTH sides again. That is what hid p37/p60.
    @test all(!(isempty(c.true_set) && isempty(c.undef_set)) for c in generated)
    @test any(!isempty(c.undef_set) for c in cases)      # …and UNDEFINED is genuinely exercised

    for c in cases
        @testset "$(c.name)" begin
            try
                (got_true, got_undef) = _xw_run(c)
                if haskey(_XW_KNOWN_WRONG, c.name)
                    # `@test_broken` reports a FIX as an error, so the exemption cannot outlive the
                    # bug — that is how the previous four entries ended (`test_unbroken` ×8).
                    @test_broken got_true == sort(c.true_set)
                    @test_broken got_undef == sort(c.undef_set)
                else
                    @test got_true == sort(c.true_set)
                    @test got_undef == sort(c.undef_set)
                end
            finally
                _XW.untable_all!()
                _XW.abolish_all_tables!()
            end
        end
    end
end
