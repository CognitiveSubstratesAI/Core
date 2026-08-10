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
        @test length(p.rewrites) == 2
        @test Set(r.name for r in p.rewrites) == Set(Base.Symbol[:FunctionReturn, :ChainStep])
        @test _MP.ddl_rung(p) == 3          # terms + rewrites ⇒ a DSL, even with R incomplete
    end

    @testset "the two rewrites have the shapes their justification requires" begin
        p = _load_mettail()
        fr = only(r for r in p.rewrites if r.name === :FunctionReturn)
        @test isempty(_MP.premises_of(fr.rw))                 # QUOTED from the table — an axiom
        cs = only(r for r in p.rewrites if r.name === :ChainStep)
        @test length(_MP.premises_of(cs.rw)) == 1             # INFERRED — a congruence rule
        @test _MP.premises_of(cs.rw)[1] == _MP.GHyp(:A, :A2)
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

    @testset "ChainStep FIRES — the gap this differential recorded, now closed" begin
        # UNTIL 2026-08-10 THIS TESTSET WAS ITS OWN OPPOSITE: it asserted that the presentation took
        # NO step on a `chain` term while the interpreter reduced it, so that porting the closure
        # would turn the test red and force the claim to be re-made. `Context.jl` + `Relation.jl`
        # landed; this is the re-made claim.
        #
        # WHAT HAD TO EXIST FOR IT. `ChainStep`'s premise `$A ~> $A2` says the first argument
        # reduces; discharging it needs `Relation.jl`'s executable reading of `PremisesHold`, which is
        # an ADDITION above upstream's executable layer (Lean leaves conditional rewriting a Prop).
        # An addition inherits no proof, so THIS is its oracle.
        p = _load_mettail()
        _p(src) = (sp = _MV.Space(); toks = _MV.tokenize(src); i = Ref(1);
                   _MV.parse_from(toks, i, sp.tokens))

        # ONE step: the interpreter reduces `chain`'s first argument, and so does the presentation.
        # `(function (return a))` ⇝ `a` by FunctionReturn, discharging the premise.
        @test _ML.cond_step(p, _p("(chain (function (return a)) \$v \$T)")) ==
              _p("(chain a \$v \$T)")
        @test !_ML.reducts_exhausted()

        # The premise must actually be CHECKED, not assumed: a first argument that does not reduce
        # blocks the rule. Without this, `ChainStep` would be an unconditional rule with extra syntax.
        @test isempty(_ML.reducts(p, _p("(chain stuck \$v \$T)")))

        # AND THE DIFFERENTIAL. `chain` substitutes its reduced first argument into the template, so
        # with the template being the bound variable itself the whole term reduces to that argument's
        # value. The presentation reaches `(chain a $v $v)` and stops — R has no substitution rule,
        # which is a REAL remaining gap and is stated as one rather than papered over.
        for inner in ("(function (return a))", "(function (return 42))")
            term = _p("(chain $inner \$v \$v)")
            stepped = _ML.cond_step(p, term)
            @test stepped !== nothing
            # what the presentation got to, and what the interpreter says the whole thing is
            reduced_arg = _MV.bare_eval(_p(inner), _MV.Space())
            @test length(reduced_arg) == 1
            @test (stepped::_MS.Expression).children[2] == reduced_arg[1]   # the ARGUMENT reduced
            # the interpreter finishes the job; the presentation cannot yet, and says so
            @test _MV.bare_eval(term, _MV.Space()) == reduced_arg
            @test _ML.cond_normalize(p, term)[1] != reduced_arg[1]
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
