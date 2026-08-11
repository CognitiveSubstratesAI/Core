# test_il_roundtrip.jl — THE COMPILE LANE SERIALIZES IL TO TEXT, SO `show` IS A WIRE FORMAT.
#
# ─── THE DEFECT CLASS, AND HOW IT WAS FOUND ──────────────────────────────────────────────────────
# `CompileLane.compile_definition` returns `Vector{String}`; `_compile_run_inner` re-loads each with
# `Eval.load_metta!`. So a compiled clause is faithful only where `parse(show(v)) ≡ v`. Several
# `Grounded` values print in a form that is perfectly good for DISPLAY and lossy as SERIALIZATION —
# and nothing in the pipeline notices, because the round-tripped clause is still well-formed MeTTa.
#
# Found 2026-08-11 while chasing two corpus scripts whose cause had been unidentified for a day.
# ⚠️ AND THE FIRST READING OF IT WAS WRONG, WHICH IS THE REASON THIS FILE TESTS IDENTITY AND NOT TEXT.
# `e1_kb_write`'s compiled error text says `(add-atom &self …)` where the source says `&kb`, and the
# obvious conclusion — "the compiler rewrites the space" — is FALSE. Comparing object identity showed
# `&kb` and `&self` are distinct `Space`s and writes land in the right one; `Grounded{Space}` merely
# PRINTS as `&self` whatever it holds (`Eval.jl:549`). The bug is one layer down: that text is then
# re-parsed, and `&self` resolves through `space.tokens["&self"]` (`Eval.jl:2579`) to whatever space
# is being loaded into. A differential that compared rendered strings would have "confirmed" the
# wrong diagnosis.
#
# ─── WHAT IS ASSERTED HERE ───────────────────────────────────────────────────────────────────────
#   1. the round-trip property itself, per value kind — the PROPERTY, not the two instances we hit;
#   2. the guard DECLINES a definition carrying such a value (correct answers via fallback);
#   3. the guard does NOT decline `&self`, which round-trips by construction — over-guarding here
#      would give back real coverage to close a bug plain `&self` does not have. That direction has
#      bitten this repo before (an arity guard derived from a regex broke 36 tests and `bin/health`),
#      so the negative case is asserted, not assumed.
using MeTTaCore
using Test

const _RT_V = MeTTaCore.Eval
const _RT_S = MeTTaCore.StandardMeTTa

"Interpreter answers for `program`, form by form — the oracle, under the same budget as the lane."
function _rt_interp(program::AbstractString)
    prev = _RT_V._INTERPRET_MAX[]
    _RT_V.interpret_max_steps!(4_000)
    try
        sp = _RT_V.Space(); _RT_V.load_core_stdlib!(sp)
        out = String[]
        for (bang, f) in MeTTaCore.mm2_split_forms(program)
            rs = try _RT_V.load_metta!(sp, bang ? "!" * f : f) catch; continue end
            bang && append!(out, sort(String[string(x) for y in rs
                                             for x in (y isa AbstractVector ? y : [y])]))
        end
        out
    finally
        _RT_V._INTERPRET_MAX[] = prev
    end
end

@testset "IL text round-trip — `show` is a wire format, and some values do not survive it" begin

    @testset "the PROPERTY: which Grounded values survive parse(show(v))" begin
        sp = _RT_V.Space(); _RT_V.load_core_stdlib!(sp)
        reparse(txt) = (toks = _RT_V.tokenize(txt); i = Ref(1);
                        _RT_V.parse_from(toks, i, sp.tokens))

        # A STATE CELL LOSES ITS TYPE. `(State (A B))` is a display convenience; re-parsed it is an
        # ordinary Expression, and a state cell is MUTABLE IDENTITY, so no textual form could be
        # faithful. There is nothing to fix in its `show` — such a clause must not be compiled.
        cell = first(_RT_V.load_metta!(sp, "!(new-state (A B))"))
        cell isa AbstractVector && (cell = cell[1])
        @test cell isa _RT_S.Grounded
        @test string(cell) == "(State (A B))"
        @test !(reparse(string(cell)) isa _RT_S.Grounded)      # ← the loss, stated as an assertion

        # A NAMED SPACE PRINTS AS `&self`. The two spaces are genuinely distinct objects — this is a
        # printing collapse, not a parsing one, and the distinction is the whole diagnosis above.
        _RT_V.load_metta!(sp, "!(bind! &kb (new-space))")
        kb = sp.tokens["&kb"]
        @test kb isa _RT_S.Grounded && kb.value isa _RT_V.Space
        @test kb.value !== sp                                   # a DIFFERENT space…
        @test string(kb) == "&self"                             # …that prints as the current one
    end

    @testset "a definition carrying such a value is DECLINED, and answers correctly" begin
        # The witness is four lines and the compiler used to produce it (`compiled=1 fell_back=0`):
        # the write went to the space the re-parsed `&self` named, so the later match found nothing.
        prog = "!(bind! &kb (new-space))\n" *
               "(= (put \$x) (add-atom &kb (Green \$x)))\n" *
               "!(put Fritz)\n" *
               "!(match &kb (Green \$y) \$y)\n"
        r = MeTTaCore.compile_run(prog; max_steps = 4_000)
        got = sort(vcat([a for (_, a) in r.answers]...))
        @test got == _rt_interp(prog)          # agrees with the interpreter…
        @test "Fritz" in got                   # …and specifically FINDS the atom it wrote
        @test r.fell_back >= 1                 # by DECLINING, which is the guard's whole mechanism

        # The corpus case, reduced: a definition whose entire body is a bound state cell.
        prog2 = "!(bind! &tok (new-state (A B)))\n" *
                "(= (get-token) &tok)\n" *
                "!(get-state (get-token))\n"
        r2 = MeTTaCore.compile_run(prog2; max_steps = 4_000)
        got2 = sort(vcat([a for (_, a) in r2.answers]...))
        @test got2 == _rt_interp(prog2)
        @test "(A B)" in got2
    end

    @testset "`&self` is NOT declined — the guard must not over-reach" begin
        # `&self` round-trips by construction: the text re-parses to the space being loaded into,
        # which is exactly what the source meant. Rejecting `Grounded{Space}` wholesale would close
        # the bug by giving back coverage that was never broken.
        prog = "(= (put2 \$x) (add-atom &self (Green \$x)))\n" *
               "!(put2 Fritz)\n" *
               "!(match &self (Green \$y) \$y)\n"
        r = MeTTaCore.compile_run(prog; max_steps = 4_000)
        @test r.compiled >= 1                                  # it STILL compiles
        got = sort(vcat([a for (_, a) in r.answers]...))
        @test got == _rt_interp(prog)
        @test "Fritz" in got
    end
end
