# test_decompile.jl — MeTTa-IL → surface MeTTa, and the round-trip ORACLE built on it.
#
# ─── WHAT THIS IS FOR, AND WHAT IT IS NOT ────────────────────────────────────────────────────────
# NOT a homoiconicity fix. That was the original motivation and MEASURING IT REFUTED IT: a compiled
# clause keeps its head (`(= (f $x) (function (return (g $x))))`), so `!(match &self (= (f $x) $b) $b)`
# answers `(g $x)` — IDENTICAL to the source form — because `(function (return X))` evaluates
# transparently to `X`. Only a STRUCTURAL body match (`(= (f $x) (g $y))`) fails. The negative case is
# asserted below so that premise cannot quietly come back.
#
# The real value is as a COMPILER ORACLE. `decompile ∘ compile ≡ id` compares SHAPE, so it observes a
# defect class the corpus differential cannot: a lowering that changes a clause's MEANING while still
# producing the right answers on the corpus's inputs. `EmitIL.jl`'s own comments record the
# `eval`→`metta` bug as having "survived a coverage ratchet, a corpus differential AND a fuzz
# differential" because "the shape is right, the values are wrong only in composition".
#
# ─── WHY DECLINES ARE ASSERTED AS DECLINES ───────────────────────────────────────────────────────
# `unify` carries THREE surface forms (`let`, `if` via `True`, `case`), and a decompiler that guessed
# among them would emit plausible, wrong MeTTa. So the contract under test is DECLINE-WITH-A-REASON,
# not silence and not a best effort — the same contract `Emit.jl`'s `decline_reason` holds. A future
# change that starts inverting `unify` should flip these assertions deliberately, which is the point.
using MeTTaCore
using Test

const _DC = MeTTaCore.CompilerDecompile

"""Parse ONE s-expression from text.

⚠️ NOT `Eval.parse_atom` — that parses a single TOKEN (a leaf: var / number / string / symbol) and
returns `Sym("(= …)")` for a whole form, which then declines for the WRONG reason. Caught by this
file's own negative case on first run."""
function _dc_parse1(text::String)
    forms = MeTTaCore.Eval.parse_program(text)
    @assert length(forms) == 1
    last(forms[1])
end

"Compile one source form and return its single emitted clause, or `nothing` if the lane declined."
function _dc_compile1(sp, src::String)
    r = try MeTTaCore.compile_definition(sp, src) catch; nothing end
    (r === nothing || length(r.atoms) != 1) && return nothing
    r.atoms[1]
end

@testset "decompile: the unambiguous inverse" begin
    sp = MeTTaCore.Eval.Space()

    # (function (return X)) → X. The trivial body, and the base case of the recursion.
    c = _dc_compile1(sp, "(= (dc1 \$x) (g \$x))")
    @test c !== nothing
    d = _DC.decompile_clause(c)
    @test !_DC.declined(d)
    @test string(d.atom) == "(= (dc1 \$x) (g \$x))"

    # A-NORMAL INLINING — the one that actually proves something. `ANormal` names the intermediate and
    # `EmitIL` binds it with `chain`; inverting means UNDOING that naming, not just unwrapping.
    #   (= (dc2 $x) (fact (- $x 1)))
    #     ⟶ (function (chain (metta (- $x 1) %Undefined% &self) $__t1 (return (fact $__t1))))
    c = _dc_compile1(sp, "(= (dc2 \$x) (fact (- \$x 1)))")
    @test c !== nothing
    @test occursin("chain", string(c))            # the lowering really did name an intermediate
    d = _DC.decompile_clause(c)
    @test !_DC.declined(d)
    @test string(d.atom) == "(= (dc2 \$x) (fact (- \$x 1)))"

    # GResidual — `_instr(::GResidual)` lowers the node VERBATIM (`nd = _il_atom(n)`), so `(eval X)`
    # inverts exactly. Added 2026-08-29 after the round-trip histogram named it the largest decline
    # bucket (15 of 32); coverage 84.8% → 91.9%, still zero mismatches.
    c = _dc_compile1(sp, "(= (dc5 \$x \$y) (match &self (edge \$x \$y) f))")
    @test c !== nothing
    @test occursin("eval", string(c))
    d = _DC.decompile_clause(c)
    @test !_DC.declined(d)
    @test string(d.atom) == "(= (dc5 \$x \$y) (match &self (edge \$x \$y) f))"

    # ⚠️ THE GUARD ON THE SECOND `eval` EMITTER. `_instr(::GFindall)` also builds `(chain (eval
    # (foldl-atom …)) …)`; that is the collapse FOLD, not a residual, and inverting it would return
    # the fold in place of the source `collapse`. Unreachable today (its outer `collapse-bind`
    # declines first) — asserted directly so it stays refused if that ever changes.
    fold = _dc_parse1("(chain (eval (foldl-atom \$c () \$r \$i (f \$r \$i))) \$o (return \$o))")
    @test _DC.declined(_DC.decompile_body(fold))
    @test occursin("foldl-atom", _DC.decompile_body(fold).reason)
end

@testset "decompile: declines name the form, never guess" begin
    sp = MeTTaCore.Eval.Space()
    for (src, want) in [
            "(= (dc3 \$x) (let \$y (h \$x) (k \$y)))"          => "unify",
            "(= (dc4 \$x) (if (> \$x 0) pos neg))"             => "unify",
        ]
        c = _dc_compile1(sp, src)
        c === nothing && continue                  # lane declined first; nothing to invert
        d = _DC.decompile_clause(c)
        @test _DC.declined(d)
        @test !isempty(d.reason)
        @test occursin(want, d.reason)
    end
end

@testset "decompile: a SOURCE clause is declined, not echoed" begin
    # Echoing an uncompiled clause would make the round-trip oracle pass on inputs it never inverted —
    # the oracle would then be measuring nothing, greenly.
    a = _dc_parse1("(= (dc6 \$x) (g \$x))")
    d = _DC.decompile_clause(a)
    @test _DC.declined(d)
    @test occursin("not a compiled clause", d.reason)

    # And a non-clause is declined rather than throwing.
    @test _DC.declined(_DC.decompile_clause(_dc_parse1("(foo bar)")))
end

@testset "decompile: the premise that motivated this is FALSE — head stays matchable" begin
    # Pinned because the wrong premise ("compiled rules are invisible to `match`") drove the design
    # for an afternoon. If a future lowering DOES start rewriting heads, this fails loudly.
    sp = MeTTaCore.Eval.Space()
    c = _dc_compile1(sp, "(= (dc7 \$x) (g \$x))")
    @test c !== nothing
    ch = (c::MeTTaCore.StandardMeTTa.Expression).children
    @test length(ch) == 3
    @test string(ch[1]) == "="                       # still an equality clause
    @test string(ch[2]) == "(dc7 \$x)"               # head IDENTICAL to source
    @test occursin("function", string(ch[3]))        # only the body was lowered
end

@testset "decompile: corpus round-trip has ZERO mismatches" begin
    # THE LOAD-BEARING ASSERTION. Coverage may move; a MISMATCH is a defect in EmitIL or Decompile and
    # must never be tolerated. Measured 2026-08-29: 219 definitions, 211 compiled, 179 round-tripped
    # (84.8%), 0 mismatches. The count is NOT asserted — that would fail on every corpus edit — but the
    # mismatch count is, and a floor is kept so silent coverage COLLAPSE is caught.
    sp = MeTTaCore.Eval.Space()
    roots = filter(isdir, ["test/oracle/leatta/corpus", "test/standard/conformance"])
    rt = 0; cand = 0; mism = String[]
    for dir in roots, f in sort(readdir(dir))
        endswith(f, ".metta") || continue
        text = try read(joinpath(dir, f), String) catch; continue end
        forms = try MeTTaCore.Eval.parse_program(text) catch; continue end
        for (is_exec, a) in forms
            is_exec && continue
            a isa MeTTaCore.StandardMeTTa.Expression || continue
            ch = (a::MeTTaCore.StandardMeTTa.Expression).children
            (length(ch) == 3 && ch[1] isa MeTTaCore.StandardMeTTa.Sym &&
             (ch[1]::MeTTaCore.StandardMeTTa.Sym).name === :(=)) || continue
            src = string(a)
            c = _dc_compile1(sp, src)
            c === nothing && continue
            cand += 1
            d = _DC.decompile_clause(c)
            _DC.declined(d) && continue
            string(d.atom) == src ? (rt += 1) : push!(mism, src * "  ⟶  " * string(d.atom))
        end
    end
    @test isempty(mism)
    isempty(mism) || foreach(m -> println("  MISMATCH: ", m), mism)
    @test cand > 100                                  # the corpus is actually being exercised
    @test rt >= div(cand, 2)                          # coverage floor: never silently collapse
end
