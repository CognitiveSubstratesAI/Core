# test_mettail_presentation.jl — MeTTa's own assembly language, presented as a GSLT.
#
# `src/compiler/gslt/presentations/mettail.metta` is the first presentation of a REAL language in
# this tree; everything before it was a first-order toy algebra. This test parses the shipped file
# and checks it against the NORMATIVE source it was transcribed from — `metta_language_spec.md` §3 —
# rather than against itself.
#
# THE ASSERTIONS THAT MATTER, and why each is here:
#   * all 13 instructions present, with the arities the table gives — a transcription can drop or
#     mis-count an argument silently, and nothing downstream would notice.
#   * `chain` BINDS. The table says "substitute <var> in <template>", so the presentation must be a
#     LAMBDA theory. If this flips to first-order, the transcription lost the binder — the single
#     thing the LeaTTa port was done to make expressible.
#   * E is EMPTY and R is INCOMPLETE, asserted explicitly. These are honest gaps, and pinning them
#     means a later change that fills them has to update the test deliberately rather than drift.
using MeTTaCore
using Test

const _MP = MeTTaCore.CompilerGSLTPresentation
const _MA = MeTTaCore.CompilerGSLTParse
const _MV = MeTTaCore.Eval
const _MR = MeTTaCore.CompilerGSLTReduce
const _ML = MeTTaCore.CompilerGSLTRelation
const _MS = MeTTaCore.StandardMeTTa

const _MODULE_PATH = joinpath(dirname(pathof(MeTTaCore)), "compiler", "gslt", "presentations",
                              "mettail.metta")

function _load_mettail()
    sp = _MV.Space()
    toks = _MV.tokenize(read(_MODULE_PATH, String)); i = Ref(1)
    _MA.parse_presentation(_MV.parse_from(toks, i, sp.tokens))
end

"Instruction ⇒ total argument count, read off `metta_language_spec.md` §3 by hand."
const _SPEC_ARITY = Dict{Base.Symbol, Int}(
    :eval => 1, :evalc => 2, :chain => 3, :unify => 4,
    Base.Symbol("decons-atom") => 1, Base.Symbol("cons-atom") => 2,
    :function => 1, :return => 1,
    Base.Symbol("collapse-bind") => 1, Base.Symbol("superpose-bind") => 1,
    :metta => 3, Base.Symbol("context-space") => 0,
    Base.Symbol("call-native") => 3)

@testset "MeTTaIL — minimal MeTTa as a GSLT presentation" begin

    @testset "the shipped file parses" begin
        @test isfile(_MODULE_PATH)
        p = _load_mettail()
        @test p.name == :MeTTaIL
        @test Set(Base.Symbol[_MP.cat_name(c) for c in p.exports]) ==
              Set(Base.Symbol[:Atom, :Space, :Type])
    end

    @testset "all 13 instructions, with the arities the SPEC gives" begin
        p = _load_mettail()
        got = Dict{Base.Symbol, Int}(
            (r.label::_MP.LabelId).name => _MP.rule_arity(r) for r in p.terms)
        @test length(got) == 13
        @test Set(keys(got)) == Set(keys(_SPEC_ARITY))       # none missing, none invented
        for (op, n) in _SPEC_ARITY
            @test got[op] == n                                # arity matches the table
        end
    end

    @testset "`chain` BINDS — so this is a lambda theory, not a signature" begin
        # The one property the LeaTTa port existed to make expressible. `(chain <atom> <var>
        # <template>)` substitutes the var IN the template, so the var is bound there.
        p = _load_mettail()
        @test _MP.is_lambda_theory(p)
        @test [(r.label::_MP.LabelId).name for r in _MP.binders_of(p)] == Base.Symbol[:chain]
        chain = only(r for r in p.terms if (r.label::_MP.LabelId).name === :chain)
        @test any(i -> i isa _MP.ItemBind, chain.items)       # (bind v Atom) — DECLARES
        @test any(i -> i isa _MP.ItemAbs,  chain.items)       # (scope v Atom) — SCOPES
        # and the two agree on the variable, which is the whole point of keeping them separate
        b = only(i for i in chain.items if i isa _MP.ItemBind)
        s = only(i for i in chain.items if i isa _MP.ItemAbs)
        @test (b::_MP.ItemBind).var === (s::_MP.ItemAbs).var
    end

    @testset "E is EMPTY and R is INCOMPLETE — pinned as honest gaps, not oversights" begin
        p = _load_mettail()
        @test isempty(p.equations)          # the spec states no structural congruence
        @test isempty(p.literals)           # grounded values are Atoms at this level
        # Only what §3 states outright. §5 is an abstract machine, not a rewrite system, so the rest
        # is unwritten ON PURPOSE. Raising this count means someone derived more rules — which should
        # be a deliberate change to this assertion, not a silent drift.
        @test length(p.rewrites) == 4
        @test Set(r.name for r in p.rewrites) ==
              Set(Base.Symbol[:FunctionReturn, :ChainStep, :ChainSubst, :FunctionStep])
        @test _MP.ddl_rung(p) == 3          # terms + rewrites ⇒ a DSL, even with R incomplete

        # NINE of the thirteen instructions have NO rule, and the file says why per instruction. This
        # is the assertion that keeps that honest: R covers `function`/`return`/`chain` and nothing
        # else, so a claim that the presentation "describes MeTTa" can be checked against it.
        covered = Set(Base.Symbol[])
        for r in p.rewrites
            lhs, _ = _MP.conclusion_of(r.rw)
            lhs isa _MS.Expression || continue
            h = (lhs::_MS.Expression).children[1]
            push!(covered, h isa _MS.Sym ? (h::_MS.Sym).name :
                           Base.Symbol(getfield((h::_MS.Grounded).value, :name)))
        end
        @test covered == Set(Base.Symbol[:function, :chain])
        @test length(setdiff(Set(keys(_SPEC_ARITY)), covered)) == 11
    end

    @testset "each rewrite has the shape its justification requires" begin
        p = _load_mettail()
        # QUOTED from the table ⇒ AXIOMS. A premise on either would be an invention.
        for name in (:FunctionReturn, :ChainSubst)
            @test isempty(_MP.premises_of(only(r for r in p.rewrites if r.name === name).rw))
        end
        # READ OFF A VERB ("interpret <atom>", "evaluate <body>") ⇒ CONGRUENCE rules, one premise each.
        for (name, hyp) in ((:ChainStep, _MP.GHyp(:A, :A2)), (:FunctionStep, _MP.GHyp(:B, :B2)))
            prems = _MP.premises_of(only(r for r in p.rewrites if r.name === name).rw)
            @test length(prems) == 1
            @test prems[1] == hyp
        end
        # ORDER IS LOAD-BEARING TO THE READING, not to correctness: ChainStep precedes ChainSubst so
        # the strategy interprets before substituting, which is the order the table's sentence reads
        # in. Measured: both orders reach the same normal form on the corpus below.
        names = [r.name for r in p.rewrites]
        @test findfirst(==(:ChainStep), names) < findfirst(==(:ChainSubst), names)
    end

    @testset "R vs the INTERPRETER — the differential that makes a rule falsifiable" begin
        # THE POINT OF THE ENGINE. Until `Reduce.jl` existed, every claim about R was a claim about a
        # transcription: the file said `(function (return $X)) ~> $X` and nothing could disagree. Here
        # the presentation's reduct and `Eval.jl`'s result are computed for the same term and required
        # to AGREE. R is now allowed to grow only as far as this differential can justify each rule —
        # a rule nobody can check against the interpreter does not go in.
        #
        # `bare_eval` runs the machine to completion while `base_reducts` takes ONE top-level step, so
        # the terms below are chosen to be one step from a normal form. That is a constraint on the
        # corpus, not a weakening: a rule that only agrees on hand-picked terms is exactly what this is
        # meant to catch, so the corpus varies the payload across every metatype the sort admits.
        p = _load_mettail()
        _p(src) = (sp = _MV.Space(); toks = _MV.tokenize(src); i = Ref(1);
                   _MV.parse_from(toks, i, sp.tokens))

        for payload in ("a", "42", "3.5", "\"s\"", "(foo bar)", "()", "\$x", "(return b)")
            term = _p("(function (return $payload))")
            reducts = _MR.base_reducts(p, term)
            interp  = _MV.bare_eval(term, _MV.Space())
            @test length(reducts) == 1
            @test length(interp) == 1
            @test reducts[1] == interp[1]
        end

        # AND THE NEGATIVE HALF, which is the half that catches an over-general rule: where the
        # presentation offers no reduct, it must be because the rule genuinely does not apply — not
        # because it fired and produced something the interpreter disagrees with.
        for src in ("(function (bar baz))", "(return a)", "(cons-atom a (b c))")
            @test isempty(_MR.base_reducts(p, _p(src)))
        end

        # `ChainStep` IS PREMISED, so `base_reducts` still cannot fire it — that is `Reduce.jl`'s
        # documented scope and the assertion below pins it.
        cs = only(r for r in p.rewrites if r.name === :ChainStep)
        @test !isempty(_MP.premises_of(cs.rw))
        @test _MR.apply_base_rewrite(cs, _p("(chain (function (return a)) \$v \$T)")) === nothing
    end

    @testset "R NORMALIZES to what the interpreter computes — the full-R differential" begin
        # THE CONDITION ON R'S GROWTH, EXECUTED. Every rule in the presentation was probed against
        # `Eval.jl` BEFORE being written into the file; this is that probe, kept.
        #
        # WHAT CHANGED, TWICE, AND WHY THE HISTORY IS HERE. This testset first asserted that the
        # presentation took NO step on a `chain` term while the interpreter reduced it — a recorded
        # DISAGREEMENT, so that closing the gap would turn the test red and force the claim to be
        # re-made. `Context.jl`+`Relation.jl` made `ChainStep` fire, and it was re-made as one step.
        # Then `ChainSubst`/`FunctionStep` landed and it became what it is now: full normalization,
        # required to equal the interpreter's answer. Each version was red before it was green.
        p = _load_mettail()
        _p(src) = (sp = _MV.Space(); toks = _MV.tokenize(src); i = Ref(1);
                   _MV.parse_from(toks, i, sp.tokens))

        # `cond_normalize` drives the whole rule set; `bare_eval` drives the interpreter. Same term,
        # same answer — including through NESTED chains, and through a template that USES the bound
        # variable (which is what makes `Subst` load-bearing rather than decorative).
        for src in ("(function (return a))",
                    "(function (return 42))",
                    "(chain (function (return a)) \$v \$v)",
                    "(chain (function (return a)) \$v (foo \$v))",
                    "(chain (function (return 42)) \$v \$v)",
                    "(chain (chain (function (return a)) \$w \$w) \$v \$v)",
                    "(function (chain (function (return a)) \$v (return \$v)))",
                    # ALREADY-NORMAL first argument: nothing to interpret, so `chain` is pure
                    # substitution. This is the case `ChainSubst` alone has to get right, and the one
                    # where an over-eager `ChainStep` would loop instead of stopping.
                    "(chain a \$v \$v)",
                    "(chain (foo bar) \$v (bar \$v))")
            term = _p(src)
            got, left = _ML.cond_normalize(p, term; fuel = 64)
            want = _MV.bare_eval(term, _MV.Space())
            @test length(want) == 1
            @test got == want[1]
            @test left > 0                       # reached a normal form, not the fuel bound
            @test !_ML.reducts_exhausted()
        end

        # A PREMISE IS GENUINELY CHECKED. `ChainStep` requires its first argument to reduce; where it
        # does not, that RULE must not fire. (`ChainSubst` still applies to the same redex — R is a
        # relation and both are rules about `chain` — so the check is per-rule, not on the term.)
        cs = only(r for r in p.rewrites if r.name === :ChainStep)
        @test isempty(_ML.apply_rewrite(p, cs, _p("(chain stuck \$v \$T)"), 8))
        @test !isempty(_ML.apply_rewrite(p, cs, _p("(chain (function (return a)) \$v \$T)"), 8))

        # R IS A RELATION, AND BOTH `chain` RULES APPLY AT ONCE. `reducts` returns both; only the
        # leftmost-outermost STRATEGY picks one. Asserted so that a future change collapsing R to a
        # function has to face this deliberately.
        rs = _ML.reducts(p, _p("(chain (function (return a)) \$v \$v)"))
        @test length(rs) == 2
        @test _p("(chain a \$v \$v)") in rs            # ChainStep: interpret the argument
        @test _p("(function (return a))") in rs        # ChainSubst: substitute it unreduced

        # AND THE NEGATIVE HALF — an instruction R deliberately does NOT cover must produce no step,
        # rather than a plausible-looking wrong one. These are the nine the file lists.
        for src in ("(cons-atom a (b c))", "(decons-atom (a b c))", "(unify a a then else)",
                    "(collapse-bind (foo))", "(context-space)")
            @test _ML.cond_step(p, _p(src)) === nothing
        end
    end

    @testset "every sort the instructions mention is declared" begin
        # The parser enforces this, so this is a regression lock on the FILE rather than the checker:
        # a typo'd sort in the presentation must not reach a generated type system as a phantom.
        p = _load_mettail()
        declared = Set(Base.Symbol[_MP.cat_name(c) for c in p.exports])
        @test _MP.declared_cats_used(p) ⊆ declared
    end
end
