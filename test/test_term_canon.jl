# test_term_canon.jl — the ONE canonicalising walker reproduces BOTH callers BYTE-EXACTLY.
#
# WHY THIS FILE IS THE GATE, AND WHY PARTITION EQUALITY IS NOT. `_variant_rename` and `_alpha_canon`
# were measured to induce the SAME equivalence relation while producing DIFFERENT representatives.
# That justified MERGING THE WALKER; it does NOT license changing what either caller returns:
#   * `_v` names are live TABLE KEYS (Tabling, Subsumptive, IDG, Inspect all compare them);
#   * `_v#1` and `$α#1` are deliberately UNEQUAL, and §5o of the BLOCKER 2 note depends on it.
# So the gate here is stricter than the measurement that motivated the merge: byte-exact OUTPUT per
# caller over a corpus, against the pre-merge implementations carried below verbatim as oracles.
#
# 🔴 THE ORACLES ARE THE OLD CODE, COPIED UNCHANGED. An oracle written fresh from the same
# understanding that wrote the new code tests nothing — it would reproduce a misreading on both
# sides. These two functions are the bodies that were deleted, character for character.

using Test
using MeTTaCore
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
const MC = MeTTaCore
const EV = MeTTaCore.Eval
const AT = MeTTaCore.StandardMeTTa
P(s) = EV.parse_program(s)[1][2]

# ── the PRE-MERGE implementations, verbatim ──────────────────────────────────────────────────────
function _old_variant_rename(a::AT.Atom)::AT.Atom
    seen = Dict{AT.Var, AT.Var}()
    n = Ref(0)
    rn(x::AT.Atom) =
        if x isa AT.Var
            get!(() -> (n[] += 1; AT.Var("_v", UInt64(n[]))), seen, x)
        else
            (x isa AT.Expression ? AT.Expression(AT.Atom[rn(c) for c in x.children]) : x)
        end
    rn(a)
end
function _old_alpha_canon(a::AT.Atom, m::Dict{AT.Var, Int})
    if a isa AT.Var
        return AT.Var("\$α", UInt64(get!(m, a, length(m))))
    elseif a isa AT.Expression
        return AT.Expression(AT.Atom[_old_alpha_canon(c, m) for c in a.children])
    else
        return a
    end
end
_old_alpha1(a::AT.Atom) = _old_alpha_canon(a, Dict{AT.Var, Int}())

@testset "TermCanon — one walker, a policy, byte-exact per caller" begin

    @testset "the ORACLES themselves behave as the deleted code did" begin
        # Without this the whole file could pass against two broken copies.
        # ⚠️ the RENDERING prefixes `\$` — measured, not guessed. A first draft asserted
        # "(f _v#1 _v#2)" from memory and failed on the prefix alone, which would have read as a
        # semantic failure of the merge rather than as a wrong string literal.
        @test string(_old_variant_rename(P("(f \$x \$y)"))) == "(f \$_v#1 \$_v#2)"
        @test occursin("α", string(_old_alpha1(P("(f \$x \$y)"))))
        # 1-based vs 0-based, the ONLY thing the two ever disagreed about
        vs = AT.Var[]; walk(a) = a isa AT.Var ? push!(vs, a) :
             (a isa AT.Expression && foreach(walk, a.children))
        walk(_old_variant_rename(P("(f \$x \$y)")))
        @test [v.id for v in vs] == [UInt64(1), UInt64(2)]
        empty!(vs); walk(_old_alpha1(P("(f \$x \$y)")))
        @test [v.id for v in vs] == [UInt64(0), UInt64(1)]
    end

    # ── the corpus: constructed shapes chosen to break it, PLUS real data ─────────────────────────
    shapes = AT.Atom[
        P("(f \$x \$y)"),                      # two distinct
        P("(f \$x \$x)"),                      # co-reference
        P("(f \$y \$x)"),                      # ORDER — first-encounter, so this differs from above
        P("(f \$x (g \$y \$x))"),              # nested, re-encounter below
        P("(h (k \$a) (k \$a))"),              # repeated subterm
        P("(f a b)"),                          # NO variables — the empty case
        P("(f)"),                              # empty expression
        P("\$x"),                              # a bare variable at the root
        P("(= (f \$x) (g \$x \$y))"),          # a rule
        P("(f \$x (g \$y (h \$z (k \$x))))"),  # deep, with a re-encounter at the bottom
    ]
    stdlib = let s = Space(); EV.load_core_stdlib!(s); EV.all_atoms(s) end
    corpus = vcat(shapes, stdlib)

    @testset "the corpus contains what it claims to" begin
        @test length(stdlib) > 50
        @test any(a -> !isempty(MC.collect_vars(a)), stdlib)   # real data with variables
        @test any(a -> isempty(MC.collect_vars(a)), corpus)    # and the ground case
    end

    @testset "🔴 VARIANT policy reproduces `_variant_rename` byte-exactly" begin
        for a in corpus
            @test MC.Eval._variant_rename(a) == _old_variant_rename(a)
            @test string(MC.Eval._variant_rename(a)) == string(_old_variant_rename(a))
        end
    end

    @testset "🔴 ALPHA policy reproduces `_alpha1` byte-exactly" begin
        for a in corpus
            @test MC.Eval._alpha1(a) == _old_alpha1(a)
            @test string(MC.Eval._alpha1(a)) == string(_old_alpha1(a))
        end
    end

    @testset "🔴 THE TWO POLICIES MUST STAY DISTINCT — the merge must not merge the OUTPUTS" begin
        # `_v#1` and `$α#1` are unequal today; a shared spelling would make a variant key and an
        # alpha-canonical form compare EQUAL, which nothing asks for and §5o depends on not happening.
        @test AT.CANON_VARIANT.spelling != AT.CANON_ALPHA.spelling
        @test AT.CANON_VARIANT.first_ordinal != AT.CANON_ALPHA.first_ordinal
        for a in corpus
            isempty(MC.collect_vars(a)) && continue        # ground terms canonicalise identically
            @test MC.Eval._variant_rename(a) != MC.Eval._alpha1(a)
        end
    end

    @testset "the relation is preserved — alpha-equivalent in, equal out" begin
        @test MC.Eval._alpha1(P("(f \$x \$y)")) == MC.Eval._alpha1(P("(f \$a \$b)"))
        @test MC.Eval._variant_rename(P("(f \$x \$y)")) == MC.Eval._variant_rename(P("(f \$a \$b)"))
        # 🔴 NEGATIVE CONTROL — non-equivalent terms must NOT collapse, or the two above are vacuous
        @test MC.Eval._alpha1(P("(f \$x \$x)")) != MC.Eval._alpha1(P("(f \$a \$b)"))
        @test MC.Eval._variant_rename(P("(f \$x \$x)")) != MC.Eval._variant_rename(P("(f \$a \$b)"))
    end

    @testset "a shared `seen` canonicalises several terms in ONE namespace" begin
        # Exposed but unused by the current callers (both pass a fresh map, censused before merging).
        # Pinned so the capability is not silently lost, and so its semantics are stated.
        seen = Dict{AT.Var, AT.Var}()
        a = AT.canon_rename(P("(f \$x)"), AT.CANON_VARIANT, seen)
        b = AT.canon_rename(P("(g \$x)"), AT.CANON_VARIANT, seen)
        @test string(a) == "(f \$_v#1)" && string(b) == "(g \$_v#1)"      # SAME variable across both
        @test MC.collect_vars(a)[1] == MC.collect_vars(b)[1]              # and it IS one variable
        fresh = AT.canon_rename(P("(g \$x)"), AT.CANON_VARIANT)
        @test fresh == MC.Eval._variant_rename(P("(g \$x)"))        # independent, as the callers do
    end
end
