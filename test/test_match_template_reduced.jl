# test_match_template_reduced.jl — `match`'s instantiated template IS REDUCED.
#
# 🔴 PINNED BEFORE THE `match` EMITTER EXISTS, because an emitter built on the opposite reading
# returns unreduced templates — a SILENT wrong-answer class.
#
# THE CONFLATION THIS GUARDS AGAINST. `match : (-> spaceType Atom Atom %Undefined%)` answers two
# different questions that are easy to merge by mistake:
#   * the `Atom`-typed TEMPLATE is passed in UNREDUCED (§7.2) — what happens BEFORE the call;
#   * the `%Undefined%` RETURN type sends the instantiated result back to the interpreter — what
#     happens AFTER. The result is reduced.
# The tutorial's `(quote $x)` example shows only that a BARE template WOULD be reduced; the
# unreduced STORAGE it demonstrates comes from `add-atom`'s Atom-typed argument, not from `match`.
# `ANormal.jl:533` says it plainly — the template "is evaluated by `match` itself AFTER binding" —
# and keeping the node whole exists to stop A-normalization HOISTING that evaluation out of the
# binder's scope, not because it never happens. I asserted the opposite while quoting that comment.
#
# MEASURED (workflows/metta_xcheck.sh), with two controls that behave in every engine:
#     hyperon-experimental   (quote $x) -> [(quote (+ 1 2)), (quote (+ 3 4))]   $x -> [3, 7]
#     CeTTa                             -> same                                 $x -> [3, 7]
#     Core                              -> same                                 $x -> [7] [3]
#     PeTTa                                                                      $x -> (+ 1 2) (+ 3 4)   ⚠️ outlier
# Core already AGREES with the reference. This file exists so the EMITTER has to.

using Test
using MeTTaCore
using MeTTaCore.Eval
const EV = MeTTaCore.Eval

@testset "match's instantiated template is REDUCED" begin
    function fresh()
        s = Space(); EV.load_core_stdlib!(s)
        EV.load_metta!(s, "(: add-foo-eq (-> Atom (->)))\n(= (add-foo-eq \$x) (add-atom &self (= (foo) \$x)))\n")
        EV.load_metta!(s, "!(add-foo-eq (+ 1 2))\n")
        EV.load_metta!(s, "!(add-foo-eq (+ 3 4))\n")
        s
    end

    @testset "CONTROL — the stored atoms really ARE unreduced (add-atom's Atom arg)" begin
        # Without this, the main assertion could pass because nothing was stored unreduced at all.
        s = fresh()
        q = string(EV.load_metta!(s, "!(match &self (= (foo) \$x) (quote \$x))\n"))
        @test occursin("+ 1 2", q) && occursin("+ 3 4", q)
    end

    @testset "🔴 THE CASE — a BARE template comes back REDUCED" begin
        s = fresh()
        r = string(EV.load_metta!(s, "!(match &self (= (foo) \$x) \$x)\n"))
        @test occursin("3", r) && occursin("7", r)
        @test !occursin("+ 1 2", r) && !occursin("+ 3 4", r)
    end

    @testset "CONTROL — a template that COMPUTES over the binding reduces too" begin
        s = fresh()
        r = string(EV.load_metta!(s, "!(match &self (= (foo) \$x) (+ 1 1))\n"))
        @test occursin("2", r)
        @test !occursin("+ 1 1", r)
    end
end
