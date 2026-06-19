# GSLT theory front-end (src/standard/GSLT.jl) — the MeTTa-IL theory algebra (F1R3FLY layered track):
# extends / union / replacement → flatten → MeTTa-IL rewrite lane → MM2 → MORK, bisimulation-gated.
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "GSLT theory front-end (theory algebra → MeTTa-IL)" begin
    facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"

    prog = raw"""
    (theory Base ()
      (terms (: edge (-> Node Node Bool)))
      (rewrites (~> (edge $x $y) (reach $x $y))))
    (theory Ext (extends Base)
      (rewrites (~> (, (edge $x $y) (edge $y $z)) (hop2 $x $z))))
    (theory A () (rewrites (~> (edge $x $y) (ra $x $y))))
    (theory B () (rewrites (~> (edge $x $y) (rb $x $y))))
    (theory U (union A B) (rewrites (~> (edge $x $y) (ru $x $y))))
    (theory Q (extends Base) (replacements (=> reach connected)))
    """
    env = load_theories(prog)

    @testset "parse: base / extends / union / replacements" begin
        @test Set(keys(env)) == Set(["Base", "Ext", "A", "B", "U", "Q"])
        @test env["Base"].base == (:none, String[])
        @test env["Ext"].base  == (:extends, ["Base"])
        @test env["U"].base    == (:union, ["A", "B"])
        @test env["Q"].replacements == [("reach", "connected")]
        @test env["Base"].terms == [raw"(: edge (-> Node Node Bool))"]
    end

    @testset "flatten: extension chain (inherits parent rewrites)" begin
        rw = theory_rewrites("Ext", env)
        @test raw"(~> (edge $x $y) (reach $x $y))" in rw                  # inherited from Base
        @test raw"(~> (, (edge $x $y) (edge $y $z)) (hop2 $x $z))" in rw  # own
        @test length(rw) == 2
    end

    @testset "flatten: union (merges all parents)" begin
        @test Set(theory_rewrites("U", env)) == Set([
            raw"(~> (edge $x $y) (ra $x $y))",
            raw"(~> (edge $x $y) (rb $x $y))",
            raw"(~> (edge $x $y) (ru $x $y))"])
    end

    @testset "flatten: replacement (whole-token rename, not substring)" begin
        @test theory_rewrites("Q", env) == [raw"(~> (edge $x $y) (connected $x $y))"]
        # substring guard: renaming `reach` must NOT corrupt `reachable`
        env2 = load_theories(raw"""
            (theory P2 () (rewrites (~> (a $x) (reachable $x)) (~> (b $x) (reach $x))))
            (theory R2 (extends P2) (replacements (=> reach connected)))
        """)
        rw2 = theory_rewrites("R2", env2)
        @test raw"(~> (a $x) (reachable $x))" in rw2     # untouched
        @test raw"(~> (b $x) (connected $x))" in rw2     # renamed
    end

    @testset "theory_run! ≡ MeTTa-IL on flattened rewrites (bisimulation)" begin
        cs1 = MC.new_core_space(); R_theory = theory_run!(cs1, facts, prog, "Ext")
        cs2 = MC.new_core_space(); R_flat = metta_il_run!(cs2, facts, join(theory_rewrites("Ext", env), "\n"))
        @test R_theory == R_flat                                          # theory lane ≡ flattened MeTTa-IL
        @test "(reach 0 1)" in R_theory && "(hop2 0 2)" in R_theory
        # replacement end-to-end: theory Q derives `connected`, never `reach`
        cs3 = MC.new_core_space(); R_q = theory_run!(cs3, facts, prog, "Q")
        @test "(connected 0 1)" in R_q && !any(s -> occursin("reach", s), R_q)
    end
end

# Faithfulness against the CANONICAL upstream example — F1R3FLY/MeTTaIL GSLT/src/test/module/UnivAlg.module
# (EmptySet → Monoid → CommutativeMonoid/Group → Rig), encoded PRIMUS-native (terms as type-sigs).
@testset "GSLT UnivAlg.module faithfulness (the real theory hierarchy)" begin
    univ = raw"""
    (theory EmptySet ())
    (theory Monoid (extends EmptySet)
      (terms (: One Elem) (: Mult (-> Elem Elem Elem)))
      (equations (= (Mult (Mult $x $y) $z) (Mult $x (Mult $y $z)))
                 (= (Mult $x One) $x)
                 (= (Mult One $x) $x)))
    (theory CommutativeMonoid (extends Monoid)
      (replacements (=> One Zero) (=> Mult Plus))
      (equations (= (Plus $x $y) (Plus $y $x))))
    (theory Group (extends Monoid)
      (terms (: Inv (-> Elem Elem)))
      (equations (= (Mult $x (Inv $x)) One) (= (Inv (Inv $x)) $x)))
    (theory Rig (union CommutativeMonoid Monoid)
      (equations (= (Mult $x (Plus $y $z)) (Plus (Mult $x $y) (Mult $x $z)))))
    """
    env = load_theories(univ)

    @testset "Monoid: own terms + equations" begin
        f = theory_flatten("Monoid", env)
        @test Set(f.terms) == Set([raw"(: One Elem)", raw"(: Mult (-> Elem Elem Elem))"])
        @test length(f.equations) == 3
    end

    @testset "CommutativeMonoid: Monoid renamed One→Zero, Mult→Plus + commutativity" begin
        f = theory_flatten("CommutativeMonoid", env)
        @test Set(f.terms) == Set([raw"(: Zero Elem)", raw"(: Plus (-> Elem Elem Elem))"])  # renamed
        @test raw"(= (Plus $x $y) (Plus $y $x))" in f.equations                              # own comm
        @test raw"(= (Mult (Mult $x $y) $z) (Mult $x (Mult $y $z)))" ∉ f.equations           # no stray Mult
        @test raw"(= (Plus (Plus $x $y) $z) (Plus $x (Plus $y $z)))" in f.equations           # assoc renamed
    end

    @testset "Group: extends Monoid + Inv" begin
        @test Set(theory_flatten("Group", env).terms) ==
              Set([raw"(: One Elem)", raw"(: Mult (-> Elem Elem Elem))", raw"(: Inv (-> Elem Elem))"])
    end

    @testset "Rig: union has BOTH additive (Zero/Plus) and multiplicative (One/Mult) structure" begin
        f = theory_flatten("Rig", env)
        @test Set(f.terms) == Set([raw"(: Zero Elem)", raw"(: Plus (-> Elem Elem Elem))",
                                   raw"(: One Elem)",  raw"(: Mult (-> Elem Elem Elem))"])
        @test raw"(= (Mult $x (Plus $y $z)) (Plus (Mult $x $y) (Mult $x $z)))" in f.equations  # distributivity
    end
end

# Theory parameterization — GSLT `Theory T(p: P)`: a theory is generic over its parameter theories,
# bound by default to their declared type and overridable at instantiation.
@testset "GSLT parameterization (Theory T(p: P))" begin
    prog = raw"""
    (theory PA () (rewrites (~> (edge $x $y) (ra $x $y))))
    (theory PB () (rewrites (~> (edge $x $y) (rb $x $y))))
    (theory Generic  (extends p) (params (p PA)))
    (theory Combined (union a b) (params (a PA) (b PB)))
    """
    env = load_theories(prog)

    @testset "param parse: base references the PARAM name" begin
        @test env["Generic"].params  == [("p", "PA")]
        @test env["Combined"].params == [("a", "PA"), ("b", "PB")]
        @test env["Generic"].base    == (:extends, ["p"])
    end

    @testset "default binding: param → its declared type" begin
        @test theory_rewrites("Generic", env) == [raw"(~> (edge $x $y) (ra $x $y))"]      # p defaults PA
        @test Set(theory_flatten("Combined", env).rewrites) ==
              Set([raw"(~> (edge $x $y) (ra $x $y))", raw"(~> (edge $x $y) (rb $x $y))"])
    end

    @testset "instantiation override: bind a param to a different theory" begin
        @test theory_instantiate("Generic", env, Dict("p" => "PB")).rewrites ==
              [raw"(~> (edge $x $y) (rb $x $y))"]                                          # p := PB
        @test theory_instantiate("Combined", env, Dict("a" => "PB")).rewrites ==
              [raw"(~> (edge $x $y) (rb $x $y))"]                                          # a:=PB, b=PB → dedup
    end
end

# Composition + recursive closure end-to-end: a theory inherits a base rule and adds a recursive one;
# theory_run! with saturate=true runs the flattened rewrites to fixpoint.
@testset "GSLT theory_run! recursive closure (saturate=true)" begin
    prog = raw"""
    (theory Graph () (rewrites (~> (edge $x $y) (path $x $y))))
    (theory TransGraph (extends Graph)
      (rewrites (~> (, (path $x $y) (edge $y $z)) (path $x $z))))
    """
    cs = MC.new_core_space()
    R = theory_run!(cs, "(edge 0 1)\n(edge 1 2)\n(edge 2 3)", prog, "TransGraph"; saturate = true)
    @test R == ["(path 0 1)", "(path 0 2)", "(path 0 3)", "(path 1 2)", "(path 1 3)", "(path 2 3)"]
end

# Equation orientation (a-tail): orient the terminating fragment, flag the rest honestly.
@testset "GSLT equation orientation (sound terminating fragment)" begin
    prog = raw"""
    (theory Monoid ()
      (terms (: One Elem) (: Mult (-> Elem Elem Elem)))
      (equations (= (Mult (Mult $x $y) $z) (Mult $x (Mult $y $z)))
                 (= (Mult $x One) $x)
                 (= (Mult One $x) $x)))
    (theory CMonoid (extends Monoid)
      (replacements (=> Mult Plus) (=> One Zero))
      (equations (= (Plus $x $y) (Plus $y $x))))
    """
    env = load_theories(prog)

    @testset "Monoid: unit laws oriented, associativity flagged" begin
        o = theory_orient_equations("Monoid", env)
        @test raw"(~> (Mult $x One) $x)" in o.oriented
        @test raw"(~> (Mult One $x) $x)" in o.oriented
        @test raw"(= (Mult (Mult $x $y) $z) (Mult $x (Mult $y $z)))" in o.flagged   # equal size → not oriented
        @test !any(s -> occursin("Mult (Mult", s), o.oriented)
    end

    @testset "CMonoid: commutativity NON-orientable (flagged), renamed unit law oriented" begin
        oc = theory_orient_equations("CMonoid", env)
        @test raw"(= (Plus $x $y) (Plus $y $x))" in oc.flagged                       # commutativity loops
        @test raw"(~> (Plus $x Zero) $x)" in oc.oriented                             # unit law (renamed)
    end

    @testset "oriented equations REDUCE a term via the normalizer" begin
        o = theory_orient_equations("Monoid", env)
        @test metta_il_normalize(join(o.oriented, "\n"), raw"(Mult a One)") == "a"   # unit simplification
        @test metta_il_normalize(join(o.oriented, "\n"), raw"(f (Mult One b))") == "(f b)"  # + congruence
    end
end
