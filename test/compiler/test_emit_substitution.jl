# test_emit_substitution.jl — variable substitution must not corrupt variables it does not own.
#
# ─── THE BUG THIS PINS ───────────────────────────────────────────────────────────────────────────
# `_apply_subst` rewrote RENDERED TEXT with a plain `replace`, so substituting `$x` also rewrote every
# variable whose name merely STARTS WITH `x`. Its docstring claimed a protection the body did not
# provide — "longest names first so `$x1` is not clobbered by `$x`" — which only helps when `x1` is
# itself a key. With the substitution `x → pinned`, `$x1` was corrupted anyway. MEASURED 2026-08-07:
#
#     (= (bug $x1) (let $x pinned (pair $x $x1)))
#       ⟹ (exec 0 (, (bug pinned1)) (O (+ (pair pinned pinned1))))
#
# `$x1` is a DIFFERENT variable AND the head argument. Rewriting it to the literal `pinned1` turned a
# rule that matches any `(bug …)` into one that matches a single atom which never occurs. The clause
# still counted as EMITTED, so no coverage number moved and no gate went red — a rule that cannot fire,
# which this compiler's standing rule calls worse than an absent one.
#
# Found by asking what the emitter does that the typed IR was built to make unnecessary: it does string
# surgery. The durable fix is to substitute on the IR by `NodeId` — variable IDENTITY, which the
# frontend already resolves — rather than on rendered text. Until then the text path matches whole
# `$name` tokens in one pass, and these tests keep it honest.
using MeTTaCore
using Test

const _UF = MeTTaCore.CompilerFrontend
const _UA = MeTTaCore.CompilerANormal
const _UE = MeTTaCore.CompilerEmit
const _UI = MeTTaCore.Eval

function _sub_parse(sp, text::AbstractString)
    toks = _UI.tokenize(text)
    i = Ref(1)
    out = MeTTaCore.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _UI.parse_from(toks, i, sp.tokens))
    end
    out
end

@testset "emitter substitution — whole names only" begin

    @testset "a substituted name must not rewrite a longer name sharing its prefix" begin
        sub = Dict{Base.Symbol, String}(:x => "red")
        @test _UE._apply_subst("(f \$x)", sub) == "(f red)"
        @test _UE._apply_subst("(f \$x1 \$x)", sub) == "(f \$x1 red)"     # digit suffix
        @test _UE._apply_subst("(g \$xs \$x)", sub) == "(g \$xs red)"     # letter suffix
        @test _UE._apply_subst("(h \$x_2)", sub) == "(h \$x_2)"        # underscore suffix
        @test _UE._apply_subst("(h \$x-2)", sub) == "(h \$x-2)"        # hyphen is a name char here
    end

    @testset "order-insensitivity: no key may partially rewrite another" begin
        # The old implementation depended on iteration order and sorted by length to compensate. One
        # pass over whole tokens removes the dependence entirely, so BOTH keys resolve independently.
        sub = Dict{Base.Symbol, String}(:x => "A", :x1 => "B")
        @test _UE._apply_subst("(f \$x \$x1)", sub) == "(f A B)"
        @test _UE._apply_subst("(f \$x1 \$x)", sub) == "(f B A)"
    end

    @testset "END-TO-END: the head variable survives a let over a prefix-sharing name" begin
        sp = _UI.Space()
        _UI.load_core_stdlib!(sp)
        src = "(= (bug \$x1) (let \$x pinned (pair \$x \$x1)))\n"
        cls = _UA.translate_program(_UF.lower_program(_sub_parse(sp, src)))
        r = _UE.emit_program(cls)
        @test r.emitted == 1
        joined = join(r.rules, "\n")
        @test occursin("(bug \$x1)", joined)     # the redex still matches ANY (bug …)
        @test occursin("pinned", joined)         # the let binding did apply
        @test !occursin("pinned1", joined)       # and did NOT leak into the neighbouring name
    end

    @testset "a variable with no binding is left alone" begin
        @test _UE._apply_subst("(f \$y)", Dict{Base.Symbol, String}(:x => "red")) ==
            "(f \$y)"
        @test _UE._apply_subst("(f \$y)", Dict{Base.Symbol, String}()) == "(f \$y)"
    end
end
