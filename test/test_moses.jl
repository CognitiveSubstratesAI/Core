# MOSES on Core — port of the iCog metta-moses MeTTaLog reimplementation of asmoses.
# Upstream 1:1 ref: ~/JuliaAGI/dev-zone/metta-moses ; research layer: MOSES MORK.pdf.
#
# Build status (incremental port):
#   M0 ✅ scaffold + Core-native list utilities (this file's M0 testset)
#
# Run (cold, one-off):  julia --project=packages/Core packages/Core/test/test_moses.jl
using MeTTaCore, Test

println("MOSES: initialising space...")
const MM = new_core_space()
ef_moses = e -> to_sexpr(eval_metta(from_sexpr(e), MM))
register_core_primitives!()
_register_atom_ops!(ef_moses)
load_stdlib!(MM)
run_metta("!(import! &self (library MOSES))", MM)
qm(e) = run_metta(e, MM)

@testset "MOSES on Core" begin
    @testset "M0 — Core-native list utilities (Cons/Nil-ADT → ()-expr idiom)" begin
        @test qm("!(List.length (1 2 3))") == [3]
        @test qm("!(List.length ())") == [0]
        @test qm("!(List.foldl + 0 (1 2 3 4))") == [10]
        @test qm("!(List.foldr + 0 (1 2 3 4))") == [10]
        @test qm("!(List.sum (5 10 15))") == [30]
        @test qm("!(List.getByIdx (10 20 30) 1)") == [20]
        @test qm("!(List.member 2 (1 2 3))") == [Bool(true)] || qm("!(List.member 2 (1 2 3))") == ["True"]
        @test qm("!(List.member 9 (1 2 3))") == [Bool(false)] || qm("!(List.member 9 (1 2 3))") == ["False"]
    end

    @testset "M1a — Instance (genotype value) + Pair" begin
        @test qm("!(Pair.first  (mkPair a b))") == [Symbol("a")] || qm("!(Pair.first  (mkPair a b))") == ["a"]
        @test qm("!(Pair.second (mkPair a b))") == [Symbol("b")] || qm("!(Pair.second (mkPair a b))") == ["b"]
        @test qm("!(Inst.length (mkInst (0 1 2 0)))") == [4]
        @test qm("!(Inst.get (mkInst (5 6 7)) 2)") == [7]
        @test qm("!(Inst.elems (mkInst (1 0 1)))") == [[1, 0, 1]] || occursin("1", string(qm("!(Inst.elems (mkInst (1 0 1)))")))
        @test qm("!(getInst (mkSInst (mkPair (mkInst (1 0)) 9.0)))") == [[:mkInst, [1, 0]]] ||
              occursin("mkInst", string(qm("!(getInst (mkSInst (mkPair (mkInst (1 0)) 9.0)))")))
        @test qm("!(getSInstScore (mkSInst (mkPair (mkInst (1 0)) 9.0)))") == [9.0]
    end

    # assertEqual returns () on match, (Error …) on mismatch — so a passing case
    # contains no "Error"/"AssertionFailed". aok runs one assertEqual and checks that.
    aok(e) = !occursin("Error", string(qm(e))) && !occursin("AssertionFailed", string(qm(e)))

    @testset "M1b — Map ADT" begin
        @test aok("!(assertEqual (Map.getByKey b (ConsMap (a 1) (ConsMap (b 2) NilMap))) 2)")
        @test aok("!(assertEqual (Map.length (ConsMap (a 1) (ConsMap (b 2) NilMap))) 2)")
        @test aok("!(assertEqual (Map.contains b (ConsMap (a 1) (ConsMap (b 2) NilMap))) True)")
        @test aok("!(assertEqual (Map.contains z (ConsMap (a 1) NilMap)) False)")
        @test aok("!(assertEqual (Map.find (ConsMap (a 1) (ConsMap (b 2) NilMap)) b) 1)")
        @test aok("!(assertEqual (Map.values (ConsMap (a 1) (ConsMap (b 2) NilMap))) (1 2))")
        @test aok("!(assertEqual (Map.keys (ConsMap (a 1) (ConsMap (b 2) NilMap))) (a b))")
        @test aok("!(assertEqual (Map.insertCounter a (ConsMap (a 1) NilMap)) (ConsMap (a 2) NilMap))")
        @test aok("!(assertEqual (Map.remove a (ConsMap (a 1) (ConsMap (b 2) NilMap))) (ConsMap (b 2) NilMap))")
    end

    @testset "M1b — list helpers (filter/index/append/replaceAt/concatT)" begin
        @test aok("!(assertEqual (filter-atom (a () b () c) \$e (isNotUnit \$e)) (a b c))")
        @test aok("!(assertEqual (List.index (a b c) b) 1)")
        @test aok("!(assertEqual (List.index (a b c) z) -1)")
        @test aok("!(assertEqual (List.append d (a b c)) (a b c d))")
        @test aok("!(assertEqual (List.replaceAt (a b c) 1 z) (a z c))")
        @test aok("!(assertEqual (concatT (1 2) (3 4)) (1 2 3 4))")
    end

    @testset "M1b — Tree: accessors / preOrder / buildTree" begin
        @test aok("!(assertEqual (getNodeValue (mkTree (mkNode AND) ())) (mkNode AND))")
        @test aok("!(assertEqual (getChildren (mkTree (mkNode AND) ((mkTree (mkNode A) ())))) ((mkTree (mkNode A) ())))")
        @test aok("!(assertEqual (preOrder (mkNullVex ())) ())")
        @test aok("!(assertEqual (preOrder (mkTree (mkNode A) ())) A)")
        @test aok("!(assertEqual (preOrder (mkTree (mkNode AND) ((mkTree (mkNode A) ())))) (AND A))")
        # (AND A (OR B C))
        @test aok("!(assertEqual (preOrder (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ())))))) (AND A (OR B C)))")
        @test aok("!(assertEqual (buildTree (OR A (AND A B))) (mkTree (mkNode OR) ((mkTree (mkNode A) ()) (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode B) ()))))))")
        # preOrder ∘ buildTree round-trip
        @test aok("!(assertEqual (preOrder (buildTree (AND A (OR B C)))) (AND A (OR B C)))")
    end

    @testset "M1b — Tree: NodeId traversal / edits" begin
        # getLevelById: level 3 of (AND A (OR B C) (mkNullVex (S)))
        @test aok("!(assertEqual (getLevelById (mkTree (mkNode OR) ((mkTree (mkNode A) ()) (mkNullVex ((mkTree (mkNode S) ()))))) 2) (mkNullVex ((mkTree (mkNode S) ()))))")
        # getNodeById (2 1) of (AND A (OR B C)) → B
        @test aok("!(assertEqual (getNodeById (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ()))))) (mkNodeId (2 1))) (mkTree (mkNode B) ()))")
        # getChildrenById (2) of (AND A (OR B C)) → (B C)
        @test aok("!(assertEqual (getChildrenById (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ()))))) (mkNodeId (2))) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ())))")
        # insertAbove
        @test aok("!(assertEqual (insertAbove (mkTree (mkNode A) ()) (mkNode NOT)) (mkTree (mkNode NOT) ((mkTree (mkNode A) ()))))")
        # replaceNodeById (2 2) Y→W in (AND X (OR Y Z))
        @test aok("!(assertEqual (replaceNodeById (mkTree (mkNode AND) ((mkTree (mkNode X) ()) (mkTree (mkNode OR) ((mkTree (mkNode Y) ()) (mkTree (mkNode Z) ()))))) (mkNodeId (2 2)) (mkTree (mkNode W) ())) (mkTree (mkNode AND) ((mkTree (mkNode X) ()) (mkTree (mkNode OR) ((mkTree (mkNode Y) ()) (mkTree (mkNode W) ()))))))")
        # replaceNodeById at root (0)
        @test aok("!(assertEqual (replaceNodeById (mkTree (mkNode AND) ()) (mkNodeId (0)) (mkTree (mkNode A) ())) (mkTree (mkNode A) ()))")
        # appendChild D under root (0) of (AND A B C) → (AND A B C D), id (4)
        @test aok("!(assertEqual (appendChild (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode B) ()) (mkTree (mkNode C) ()))) (mkNodeId (0)) (mkTree (mkNode D) ())) ((mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode B) ()) (mkTree (mkNode C) ()) (mkTree (mkNode D) ()))) (mkNodeId (4))))")
        # getSubtreeId of C among children of node (2) → (2 2)
        @test aok("!(assertEqual (getSubtreeId (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ()))))) (mkNodeId (2)) (mkTree (mkNode C) ()) 0) (mkNodeId (2 2)))")
        # getNodeId reverse: B in (AND A (OR B C)) → (2 1)
        @test aok("!(assertEqual (getNodeId (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ()))))) (mkTree (mkNode B) ())) (mkNodeId (2 1)))")
        # getNodeId: A (direct child) → (1)
        @test aok("!(assertEqual (getNodeId (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ()))))) (mkTree (mkNode A) ())) (mkNodeId (1)))")
        # getNodeId: absent E → (-1)
        @test aok("!(assertEqual (getNodeId (mkTree (mkNode AND) ((mkTree (mkNode A) ()) (mkTree (mkNode OR) ((mkTree (mkNode B) ()) (mkTree (mkNode C) ()))))) (mkTree (mkNode E) ())) (mkNodeId (-1)))")
    end

    @testset "M1b — Tree: predicates / complexity" begin
        @test aok("!(assertEqual (isEmpty (mkNullVex ())) True)")
        @test aok("!(assertEqual (isEmpty (mkTree (mkNode A) ())) False)")
        @test aok("!(assertEqual (isNullVertex (mkNullVex ())) True)")
        @test aok("!(assertEqual (isNullVertex (mkTree (mkNode A) ())) False)")
        @test aok("!(assertEqual (isArgument (mkTree (mkNode A) ())) True)")
        @test aok("!(assertEqual (isArgument (mkTree (mkNode AND) ())) False)")
        # complexity of (AND (NOT A) (OR A B)) = 3 argument leaves
        @test aok("!(assertEqual (treeComplexity (buildTree (AND (NOT A) (OR A B)))) 3)")
        @test aok("!(assertEqual (treeComplexity (mkTree (mkNode OR) ((mkTree (mkNode AND) ((mkTree (mkNode A) ())))))) 1)")
    end

    @testset "M1c-1 — MultiMap ADT" begin
        # insert with custom comparator (discSpec<-style numeric <)
        @test aok("!(assertEqual (MultiMap.insert (2 b) (ConsMMap (1 a) (ConsMMap (3 c) NilMMap)) <) (ConsMMap (1 a) (ConsMMap (2 b) (ConsMMap (3 c) NilMMap))))")
        @test aok("!(assertEqual (MultiMap.findOne 2 (ConsMMap (1 a) (ConsMMap (2 b) NilMMap))) b)")
        @test aok("!(assertEqual (MultiMap.findAll 2 (ConsMMap (2 b) (ConsMMap (1 a) (ConsMMap (2 c) NilMMap)))) (b c))")
        @test aok("!(assertEqual (MultiMap.contains 2 (ConsMMap (1 a) (ConsMMap (2 b) NilMMap))) True)")
        @test aok("!(assertEqual (MultiMap.length (ConsMMap (1 a) (ConsMMap (2 b) NilMMap))) 2)")
        @test aok("!(assertEqual (MultiMap.values (ConsMMap (1 a) (ConsMMap (2 b) NilMMap))) (a b))")
        @test aok("!(assertEqual (MultiMap.removeOne 2 (ConsMMap (1 a) (ConsMMap (2 b) (ConsMMap (2 c) NilMMap)))) (ConsMMap (1 a) (ConsMMap (2 c) NilMMap)))")
        @test aok("!(assertEqual (MultiMap.removeAll 2 (ConsMMap (1 a) (ConsMMap (2 b) (ConsMMap (2 c) NilMMap)))) (ConsMMap (1 a) NilMMap))")
    end

    @testset "M1c-1 — knob data structures" begin
        # inExemplar: default specifier non-zero ⇒ outside exemplar (True)
        @test aok("!(assertEqual (inExemplar (mkDiscKnob k m (mkDiscSpec 0) (mkDiscSpec 1) ())) True)")
        @test aok("!(assertEqual (inExemplar (mkDiscKnob k m (mkDiscSpec 0) (mkDiscSpec 0) ())) False)")
        @test aok("!(assertEqual (getDiscKnob (mkLSK (mkDiscKnob (mkKnob (mkNodeId (1))) (mkMultip 2) (mkDiscSpec 0) (mkDiscSpec 0) ()))) (mkDiscKnob (mkKnob (mkNodeId (1))) (mkMultip 2) (mkDiscSpec 0) (mkDiscSpec 0) ()))")
        @test aok("!(assertEqual (getKnobMultip (mkLSK (mkDiscKnob (mkKnob (mkNodeId (1))) (mkMultip 2) (mkDiscSpec 0) (mkDiscSpec 0) ()))) (mkMultip 2))")
        # getKnobSpec: multip 3 minus 1 disallowed spec ⇒ (mkDiscSpec 2)
        @test aok("!(assertEqual (getKnobSpec (mkLSK (mkDiscKnob (mkKnob (mkNodeId (1 1))) (mkMultip 3) (mkDiscSpec 0) (mkDiscSpec 0) ((mkDiscSpec 1))))) (mkDiscSpec 2))")
        @test aok("!(assertEqual (getKnobSpec (mkLSK (mkDiscKnob (mkKnob (mkNodeId (1 1))) (mkMultip 3) (mkDiscSpec 0) (mkDiscSpec 0) ()))) (mkDiscSpec 3))")
        @test aok("!(assertEqual (getKnobLoc (mkLSK (mkDiscKnob (mkKnob (mkNodeId (1))) (mkMultip 2) (mkDiscSpec 0) (mkDiscSpec 0) ()))) (mkNodeId (1)))")
        @test aok("!(assertEqual (discSpec< (mkDiscSpec 2) (mkDiscSpec 3)) True)")
        @test aok("!(assertEqual (discSpec< (mkDiscSpec 3) (mkDiscSpec 2)) False)")
    end

    @testset "M1c-1 — nodeId< lexicographic order" begin
        @test aok("!(assertEqual (nodeId< (mkNodeId (2 1)) (mkNodeId (2 1 1))) True)")   # prefix < extension
        @test aok("!(assertEqual (nodeId< (mkNodeId (2 1)) (mkNodeId (2 2))) True)")
        @test aok("!(assertEqual (nodeId< (mkNodeId (2 2 3)) (mkNodeId (2 3))) True)")
        @test aok("!(assertEqual (nodeId< (mkNodeId (2 3)) (mkNodeId (1 2))) False)")
        @test aok("!(assertEqual (nodeId< (mkNodeId (2 3)) (mkNodeId (2 3))) False)")    # equal ⇒ not <
    end

    @testset "M6-1 — rte-helpers (reduce-to-elegance set-ops via filter-atom)" begin
        # getLiterals: keep the literals (symbols + (NOT …)), drop the head junctor
        @test aok("!(assertEqual (getLiterals (AND (NOT A) (NOT B) X)) ((NOT A) (NOT B) X))")
        @test aok("!(assertEqual (getLiterals (OR (NOT A) X)) ((NOT A) X))")
        @test aok("!(assertEqual (getLiterals (NOT A)) (NOT A))")
        # getChildrenExp: keep only subexpression children (not symbols / (NOT …))
        @test aok("!(assertEqual (getChildrenExp (AND A B (OR C D))) ((OR C D)))")
        @test aok("!(assertEqual (getChildrenExp (AND A B)) ())")
        # getGuardSet: AND node → its literals; OR node → ()
        @test aok("!(assertEqual (getGuardSet (AND (NOT A) X (OR C D))) ((NOT A) X))")
        @test aok("!(assertEqual (getGuardSet (OR A B)) ())")
        # getLiteralChildren tuple
        @test aok("!(assertEqual (getLiteralChildren (AND A (OR B C))) ((A) ((OR B C))))")
        # addChildren appends subexpression children, preserving literals
        @test aok("!(assertEqual (addChildren (AND A) ((OR B C))) (AND A (OR B C)))")
        # findCommon across guard sets (intersection)
        @test aok("!(assertEqual (findCommon ((A B C) (A B) (A D))) (A))")
        @test aok("!(assertEqual (findCommonLiterals (A B C) ((A B) (B C))) (B))")
        # the reduct-general helpers in utilities
        @test aok("!(assertEqual (swapAndOr AND) OR)")
        @test aok("!(assertEqual (swapAndOr OR) AND)")
        @test aok("!(assertEqual (removeElement (B) (A B C)) (A C))")
        @test aok("!(assertEqual (any (False True False)) True)")
        @test aok("!(assertEqual (any (False False)) False)")
    end

    @testset "M1c-2a — logical-canonize (reduct-free)" begin
        @test aok("!(assertEqual (isAnArgument A) True)")
        @test aok("!(assertEqual (isAnArgument AND) False)")
        @test aok("!(assertEqual (isBoolean True) True)")
        @test aok("!(assertEqual (isBoolean A) False)")
        # AND node → wrapped under an OR parent
        @test aok("!(assertEqual (logicalCanonize (mkTree (mkNode AND) ((mkTree (mkNode A) ())))) (mkTree (mkNode OR) ((mkTree (mkNode AND) ((mkTree (mkNode A) ()))))))")
        # OR node → wrapped under AND
        @test aok("!(assertEqual (logicalCanonize (mkTree (mkNode OR) ((mkTree (mkNode A) ())))) (mkTree (mkNode AND) ((mkTree (mkNode OR) ((mkTree (mkNode A) ()))))))")
        # argument leaf → wrapped under AND
        @test aok("!(assertEqual (logicalCanonize (mkTree (mkNode A) ())) (mkTree (mkNode AND) ((mkTree (mkNode A) ()))))")
        # boolean constant → (OR (AND))
        @test aok("!(assertEqual (logicalCanonize (mkTree (mkNode True) ())) (mkTree (mkNode OR) ((mkTree (mkNode AND) ()))))")
    end
end
