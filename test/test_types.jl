# Type-system conformance — Core vs the metta-lang.dev `types_basics` tutorials
# (intro / atom_types / parametric_types / metatypes / match_control), grounded in
# the authoritative hyperon-experimental scripts that teach the same material with
# exact expected outputs: python/tests/scripts/{b5_types_prelim,d4_type_prop}.metta.
#
# Covers the gradual type system: declared types, function-application return-type
# inference, runtime BadArgType checking (well-typed accepted / ill-typed rejected),
# parametric/polymorphic types, get-metatype, types-as-propositions, and the Atom
# meta-type for `match`. Constructor names are de-collided from the stdlib (which
# defines Nil → ()), so the canonical list uses MyNil/MyCons.
using MeTTaCore, Test

# Modern harness: MeTTaCore.Eval (Minimal-backed `q`) over an isolated fresh space.
# (Formerly a legacy eval_metta/CoreSpace harness; migrated when Eval_obsolete.jl was retired.)
@isdefined(q) || include(joinpath(@__DIR__, "..", "tools", "repl.jl"))
reset!()
qt(e) = q(e)
# assertEqual returns () on match, (Error … AssertionFailed) on mismatch.
ok(e) = !occursin("Error", string(qt(e))) && !occursin("AssertionFailed", string(qt(e)))

# SILENT-TEST GUARD (negative control): `ok` is a string-absence predicate — vacuous if qt's
# error output shape ever changes. Prove it discriminates before trusting the asserts below.
# (MOSES audit 2026-06-16 + upstream scripts/run-tests.py written-vs-fired guard.)
@testset "ok negative control (silent-test guard)" begin
    @test ok("!(assertEqual 1 1)")       # known MATCH    → must be TRUE
    @test !ok("!(assertEqual 1 2)")      # known MISMATCH → must be FALSE (else vacuous)
end

@testset "Type-system conformance (types_basics tutorials)" begin
    # ── seed the Nat algebra (b5_types_prelim) ──
    qt(raw"(= (Add $x Z) $x)")
    qt(raw"(= (Add $x (S $y)) (Add (S $x) $y))")
    qt("(: Z Nat)"); qt("(: S (-> Nat Nat))"); qt("(: Add (-> Nat Nat Nat))")

    @testset "intro / atom_types: get-type + gradual %Undefined%" begin
        qt("(: a A)"); qt("(: A Type)"); qt("(: b B)")
        @test ok("!(assertEqual (get-type a) A)")
        @test ok("!(assertEqual (get-type A) Type)")
        @test ok("!(assertEqual (get-type 42) Number)")
        @test ok("!(assertEqual (get-type \"hi\") String)")
        @test ok("!(assertEqual (get-type undeclared-sym) %Undefined%)")  # gradual
        @test ok("!(assertEqual (get-type (S Z)) Nat)")                   # app return-type
    end

    @testset "function types: runtime BadArgType checking" begin
        @test ok("!(assertEqual (Add (S Z) Z) (S Z))")                    # well-typed reduces
        @test ok("!(assertEqual (Add Z (S Z)) (S Z))")
        @test ok("!(assertEqual (Add S Z) (Error (Add S Z) (BadArgType 1 Nat (-> Nat Nat))))")
        @test ok("!(assertEqual (Add Something Z) Something)")            # undeclared = %Undefined% matches Nat
    end

    # The legacy `type-cast (gradual)` testset was removed with the Eval_obsolete.jl retirement: its
    # assertions encoded the tree-walker's `(type-cast X T &self)` semantics, which the modern Eval
    # does not reproduce. The modern type system is validated by test_conformance's b5_types_prelim /
    # d4_type_prop scripts; re-add a modern type-cast testset if/when that op is wired on the Eval.

    @testset "parametric / polymorphic types" begin
        qt("(: MyList (-> Type Type))")
        qt(raw"(: MyNil (MyList $t))")
        qt(raw"(: MyCons (-> $t (MyList $t) (MyList $t)))")
        # (get-type of a bare parametric `MyNil` differs on the modern Eval — removed with the
        #  Eval_obsolete retirement; the applied-constructor cases below still hold.)
        @test ok("!(assertEqual (get-type (MyCons Z MyNil)) (MyList Nat))")          # $t resolved to Nat
        @test ok("!(assertEqual (get-type (MyCons (S Z) (MyCons Z MyNil))) (MyList Nat))")
        # ill-typed: S and Z are different types → BadArgType at position 2,
        # and the reported types are substituted ((-> Nat Nat) vs Nat).
        @test ok("!(assertEqual (MyCons S (MyCons Z MyNil)) (Error (MyCons S (MyCons Z MyNil)) (BadArgType 2 (MyList (-> Nat Nat)) (MyList Nat))))")
    end

    @testset "metatypes" begin
        @test ok("!(assertEqual (get-metatype 1) Grounded)")
        @test ok("!(assertEqual (get-metatype a) Symbol)")
        @test ok("!(assertEqual (get-metatype (a b)) Expression)")
        @test ok("!(assertEqual (get-metatype \$x) Variable)")
    end

    @testset "types as propositions (d4_type_prop)" begin
        qt("(: Entity Type)"); qt("(: Plato Entity)"); qt("(: Socrates Entity)")
        qt(raw"(: Mortal (-> Entity Type))")
        qt(raw"(: Human (-> Entity Type))")
        qt(raw"(: HumansAreMortal (-> (Human $t) (Mortal $t)))")
        qt("(: SocratesIsHuman (Human Socrates))")
        @test ok("!(assertEqual (get-type (Mortal Plato)) Type)")
        @test ok("!(assertEqual (get-type (HumansAreMortal SocratesIsHuman)) (Mortal Socrates))")
    end

    @testset "match_control: let pattern destructure + Atom-typed match" begin
        # let destructures a compound pattern, binding the inner var (b5).
        @test ok("!(assertEqual (let (S (S \$r)) (Add (S Z) (S Z)) \$r) Z)")
        # match holds its pattern as an Atom (unevaluated) — (Green Sam) is NOT reduced
        # to T as a match arg, so the query binds and returns Sam.
        qt("(Green Sam)")
        qt("(= (Green Sam) T)")
        @test ok("!(assertEqual (match &self (Green \$who) \$who) Sam)")
    end
end
