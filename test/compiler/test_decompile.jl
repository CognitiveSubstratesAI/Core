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

@testset "decompile: if / let / case invert to the CANONICAL form" begin
    # UPSTREAM'S CONTRACT, adopted 2026-08-29 after reading SWI's own decompiler tests. `clause/2`
    # returns the clause AS COMPILED, not as written — `decomp8` asserts `s7(X) :- X = f(A), q(A)`
    # comes back as `s7(f(A)) :- q(A)`. And SWI makes an un-decompilable instruction a `sysError`
    # (`pl-comp.c:6895`), i.e. TOTALITY is required and partiality is a bug. These three previously
    # declined as "ambiguous"; declining was the wrong answer to a real ambiguity.
    sp = MeTTaCore.Eval.Space()

    c = _dc_compile1(sp, "(= (dc8 \$x) (if (< \$x 1) A B))")
    @test c !== nothing
    d = _DC.decompile_clause(c)
    @test !_DC.declined(d)
    @test string(d.atom) == "(= (dc8 \$x) (if (< \$x 1) A B))"

    c = _dc_compile1(sp, "(= (dc9 \$x) (let \$y (h \$x) (k \$y)))")
    @test c !== nothing
    d = _DC.decompile_clause(c)
    @test !_DC.declined(d)
    @test string(d.atom) == "(= (dc9 \$x) (let \$y (h \$x) (k \$y)))"
end

@testset "decompile: the lowering is NOT injective — case ⟶ if, and that is CORRECT" begin
    # MEASURED: `(if C A B)` and `(case C ((True A) (False B)))` compile to BYTE-IDENTICAL IL, so the
    # information distinguishing them is destroyed at emission and NO decompiler can recover it.
    # Pinned here because the temptation is to read the resulting difference as a decompiler bug.
    sp = MeTTaCore.Eval.Space()
    a = _dc_compile1(sp, "(= (dcA \$x) (if (< \$x 1) A B))")
    b = _dc_compile1(sp, "(= (dcA \$x) (case (< \$x 1) ((True A) (False B))))")
    @test a !== nothing && b !== nothing
    @test string(a) == string(b)                       # ← the erasure itself

    # So a `case` source decompiles to `if`. The FIXPOINT is what proves that is sound: re-compiling
    # the decompiled form yields identical IL. This is the check the corpus oracle uses instead of an
    # allowlist, because an allowlist of canonical rewrites goes stale and this cannot.
    d = _DC.decompile_clause(b::MeTTaCore.StandardMeTTa.Atom)
    @test !_DC.declined(d)
    @test occursin("(if ", string(d.atom))
    again = _dc_compile1(sp, string(d.atom))
    @test again !== nothing
    @test string(again) == string(b)                   # compile(decompile(compile(P))) == compile(P)
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
    # THE LOAD-BEARING ASSERTION. Coverage may move; a structural MISMATCH must never be tolerated.
    # Measured 2026-08-29: 219 definitions, 211 compiled, 194 round-tripped (91.9%), 0 mismatches —
    # and all 194 EXACT, 0 variant-only. The count is NOT asserted (that would fail on every corpus
    # edit); the mismatch count is, with a floor so silent coverage COLLAPSE is caught.
    #
    # ⚠️ COMPARED WITH `=@=` (`Eval.variant_eq`), NOT `==`, BECAUSE THAT IS UPSTREAM'S CONTRACT.
    # SWI-Prolog's own decompiler tests (`tests/core/test_moved_ubody.pl`, testset `moved_decompile`)
    # compare every case with `=@=`: a decompiler recovers STRUCTURE, never variable names. Ours is
    # exact today — the A-normal inverse substitutes producers back, so source names survive — but
    # asserting exactness would make a legitimate renaming look like a defect.
    #
    # 🔴 AND A MISMATCH IS NARROWER THAN "A DEFECT", WHICH THIS COMMENT PREVIOUSLY OVERCLAIMED. SWI's
    # `decomp8` asserts `s7(X) :- X = f(A), q(A).` decompiles to `s7(f(A)) :- q(A).` — the compiler
    # MOVED the unification into the head, so `clause/2` legitimately returns a non-source clause.
    # `decompile ∘ compile ≡ id` holds only for a STRUCTURE-PRESERVING lowering. EmitIL is one today,
    # which is what makes this assertion valid; an optimization that moves work would make a mismatch
    # EXPECTED, and this gate would then need re-reading, not silencing.
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
            if string(d.atom) == src || MeTTaCore.Eval.variant_eq(d.atom::MeTTaCore.StandardMeTTa.Atom, a)
                rt += 1
            else
                # FIXPOINT — canonical, not wrong, iff re-compiling yields identical IL.
                got = string(d.atom)
                r2 = try MeTTaCore.compile_definition(sp, got) catch; nothing end
                if r2 !== nothing && length(r2.atoms) == 1 && string(r2.atoms[1]) == string(c)
                    rt += 1
                else
                    push!(mism, src * "  ⟶  " * got)
                end
            end
        end
    end
    @test isempty(mism)
    isempty(mism) || foreach(m -> println("  MISMATCH: ", m), mism)
    @test cand > 100                                  # the corpus is actually being exercised
    @test rt >= div(cand, 2)                          # coverage floor: never silently collapse
end
