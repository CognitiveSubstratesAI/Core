# test_atom_encoding_correspondence.jl — SEAM 1 step 1: the encoder RETURNS its correspondence.
#
# INVARIANT I2 (docs/specs/term_model_boundary.md): identity is opaque in Core, positional at the
# boundary, and the correspondence is COMPUTED ONCE BY THE ENCODER AND RETURNED — never re-derived,
# never carried by a name. `atom_to_expr` always computed it (`seen`: Core identity -> de Bruijn
# level) and discarded it; `AtomEncoding` now carries the inverse.
#
# WHAT THIS FILE IS FOR. Two things, and the second is the one with teeth:
#   (a) the addition is INERT — `expr`/`declined` are byte-for-byte what they were;
#   (b) the new data is CORRECT — levels map to the right `Var`s, offsets are node boundaries in
#       increasing order, and a subterm recovered BY POSITION is the ORIGINAL Core atom.
#
# 🔴 (b) EXISTS BECAUSE DECODING IS LOSSY AND CANNOT BE FIXED. MEASURED 2026-09-18: of 7 Grounded
# value types, only Int and Float survive a byte round trip; `true`, `false`, `"hello"` and `:sym`
# all come back as `Sym`. The loss is on the ENCODE side — AtomExprBridge.jl states "No grounded TAG
# exists; a grounded atom encodes as its WORD" — so `Grounded("hello")` and `Sym("hello")` are the
# SAME BYTES and no decoder can distinguish them. Translating bindings by decoding would therefore
# silently downgrade bound values. Recovering them by POSITION is loss-free by construction, and the
# last testset here is that claim rather than a description of it.

using Test
using MeTTaCore
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
# ⚠️ `import`, NOT `using`. The suite shares ONE `Main` namespace, and `using MORK` exports a `Space`
# that collides with Core's — every LATER file referring to a bare `Space` then dies with
# "UndefVarError: Space not defined in Main … two or more modules export different bindings with this
# name". MEASURED 2026-09-18: a `using MORK` here took out test_quantale.jl and test_subrep.jl, two
# files that have nothing to do with this one. No neighbouring test file uses `using MORK`.
import MORK
const MC = MeTTaCore
const EV = MeTTaCore.Eval
const AT = MeTTaCore.StandardMeTTa

enc(src) = MC.atom_to_expr(EV.parse_program(src)[1][2])

@testset "AtomEncoding carries the correspondence (seam 1 step 1)" begin

    @testset "INERT — expr/declined are unchanged by the addition" begin
        for src in ("(f a b)", "(f \$x \$x)", "(= (f \$x) (g \$x \$y))", "(f (g \$x) h)")
            e = enc(src)
            @test e.declined === nothing
            @test e.expr isa MORK.Expr
            @test !isempty(e.expr.buf)
        end
        # a decline still declines, with a REASON and not a flag
        big = EV.parse_program("(f " * join(["a" for _ in 1:70], " ") * ")")[1][2]
        d = MC.atom_to_expr(big)
        @test d.expr === nothing
        @test d.declined isa String
        @test occursin("Rule of 64", d.declined)
    end

    @testset "a DECLINE returns EMPTY maps, never partial ones" begin
        # A half-filled correspondence describes bytes no caller receives, and is worse than none
        # because it looks usable.
        big = EV.parse_program("(f " * join(["a" for _ in 1:70], " ") * ")")[1][2]
        d = MC.atom_to_expr(big)
        @test isempty(d.vars) && isempty(d.offsets) && isempty(d.nodes)
    end

    @testset "offsets are STRICTLY INCREASING node boundaries — pinned, not assumed" begin
        for src in ("(f a b)", "(f \$x \$x)", "(f (g \$x) (h \$x \$y))", "(f \$x (g \$y (h \$x \$y)))")
            e = enc(src)
            @test length(e.offsets) == length(e.nodes)
            @test issorted(e.offsets)
            @test length(unique(e.offsets)) == length(e.offsets)   # strict, not merely sorted
            @test e.offsets[1] == 0                                # the root starts at byte 0
            @test e.nodes[1] === EV.parse_program(src)[1][2] || e.nodes[1] == EV.parse_program(src)[1][2]
            @test all(o -> o < length(e.expr.buf), e.offsets)      # every offset is INSIDE the buffer
        end
    end

    @testset "`vars` is the inverse of `seen` — level k ⇒ the Var that got it" begin
        # `(f $x $y $x)`: $x takes level 0, $y level 1, and the third occurrence is a VarRef(0).
        a = EV.parse_program("(f \$x \$y \$x)")[1][2]
        e = MC.atom_to_expr(a)
        @test length(e.vars) == 2                       # TWO distinct variables, three occurrences
        @test e.vars[1] == AT.Var("x", UInt64(0))
        @test e.vars[2] == AT.Var("y", UInt64(0))
        @test MC.encoding_var(e, 0) == e.vars[1]
        @test MC.encoding_var(e, 1) == e.vars[2]
        @test MC.encoding_var(e, 2) === nothing         # out of range, not an error
        @test MC.encoding_var(e, -1) === nothing

        # and it agrees with the BYTES. ⚠️ COUNT AT NODE BOUNDARIES, NOT OVER EVERY BYTE: a symbol's
        # PAYLOAD bytes are not tags, and `byte_item` on one throws ("reserved byte: 0x66" — `'f'`).
        # A first draft of this line scanned `e.expr.buf` whole and did exactly that; it is the same
        # defect a probe in this arc hit on 2026-09-18. `offsets` is the boundary list, so use it.
        newvars = count(o -> MORK.byte_item(e.expr.buf[Int(o) + 1]) isa MORK.ExprNewVar, e.offsets)
        @test newvars == length(e.vars)
    end

    @testset "a variable repeated is ONE entry; two distinct are TWO" begin
        @test length(enc("(f \$x \$x)").vars) == 1
        @test length(enc("(f \$x \$y)").vars) == 2
        @test length(enc("(f a b)").vars) == 0           # the zero case
    end

    @testset "encoding_subterm recovers the SOURCE subterm at a node boundary" begin
        a = EV.parse_program("(f (g \$x) h)")[1][2]
        e = MC.atom_to_expr(a)
        @test MC.encoding_subterm(e, 0) === a || MC.encoding_subterm(e, 0) == a
        # every recorded offset resolves to the node recorded with it
        for (o, n) in zip(e.offsets, e.nodes)
            @test MC.encoding_subterm(e, o) === n || MC.encoding_subterm(e, o) == n
        end
    end

    @testset "🔴 NEGATIVE CONTROL — a non-boundary offset must return nothing" begin
        # Without this, `encoding_subterm` returning something for every input would pass everything
        # above. A symbol's PAYLOAD bytes are inside a node but are not a node boundary.
        e = enc("(f hello)")
        boundaries = Set(Int.(e.offsets))
        inside = [i for i in 0:(length(e.expr.buf) - 1) if !(i in boundaries)]
        @test !isempty(inside)                                   # the case is REACHED
        @test all(i -> MC.encoding_subterm(e, i) === nothing, inside)
        @test MC.encoding_subterm(e, length(e.expr.buf) + 99) === nothing
    end

    @testset "🔴 THE PAYOFF — position recovers a Grounded that BYTES cannot" begin
        for v in (true, false, "hello", :sym, 7, 3.5)
            a = AT.Expression(AT.Atom[AT.Sym("f"), AT.Grounded(v)])
            e = MC.atom_to_expr(a)
            @test e.declined === nothing
            # the byte round trip: lossy for 4 of these 6
            decoded = (MC.expr_to_atom(e.expr)::AT.Expression).children[2]
            # position recovery: EXACT, for all of them
            off = e.offsets[findfirst(n -> n === a.children[2], e.nodes)]
            recovered = MC.encoding_subterm(e, off)
            @test recovered isa AT.Grounded
            @test recovered.value == v
            @test recovered === a.children[2]        # the ORIGINAL object, not a reconstruction
            # and for the lossy ones, prove the two DISAGREE — otherwise this testset proves nothing
            if v isa Bool || v isa AbstractString || v isa Symbol
                @test !(decoded isa AT.Grounded)     # the measured loss, pinned
            end
        end
    end
end
