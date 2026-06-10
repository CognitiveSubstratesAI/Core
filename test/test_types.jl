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

println("Types: initialising space...")
const TY = new_core_space()
ef_types = e -> to_sexpr(eval_metta(from_sexpr(e), TY))
register_all_primitives!()
_register_atom_ops!(ef_types)
load_stdlib!(TY)
qt(e) = run_metta(e, TY)
# assertEqual returns () on match, (Error … AssertionFailed) on mismatch.
ok(e) = !occursin("Error", string(qt(e))) && !occursin("AssertionFailed", string(qt(e)))

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

    @testset "type-cast (gradual)" begin
        # declared type: matching cast returns the atom, mismatch → BadType error
        @test ok("!(assertEqual (type-cast Z Nat &self) Z)")
        @test ok("!(assertEqual (type-cast Z Bool &self) (Error Z (BadType Bool Nat)))")
        # grounded literals carry a structural type
        @test ok("!(assertEqual (type-cast 42 Number &self) 42)")
        @test ok("!(assertEqual (type-cast 42 Bool &self) (Error 42 (BadType Bool Number)))")
        # undeclared atom is %Undefined% → universal, so any cast succeeds (gradual)
        @test ok("!(assertEqual (type-cast undeclared-foo Nat &self) undeclared-foo)")
        # Atom is universal on the requested side too
        @test ok("!(assertEqual (type-cast 42 Atom &self) 42)")
    end

    @testset "parametric / polymorphic types" begin
        qt("(: MyList (-> Type Type))")
        qt(raw"(: MyNil (MyList $t))")
        qt(raw"(: MyCons (-> $t (MyList $t) (MyList $t)))")
        @test ok("!(assertEqual (get-type MyNil) (MyList \$t))")
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
