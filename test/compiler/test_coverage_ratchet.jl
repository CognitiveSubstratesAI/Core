# test_coverage_ratchet.jl — the compiler's coverage may not go DOWN.
#
# ─── WHY THIS EXISTS ─────────────────────────────────────────────────────────────────────────────
# The compiled lane emits 27.5% of the corpus and EVERY GATE IS GREEN, because the other 72.5%
# silently falls back to the interpreter and nothing records that it happened. A compiler whose
# incompleteness costs nothing stays incomplete — `MM2Router` sat behind the same free fallback for
# months and never passed 34.8%.
#
# This is the forcing function. The emitted count is pinned; a change that lowers it FAILS. A number
# that can only go up is a ratchet, a number in a report is a wish. The same pattern already runs in
# MORK (the port-inventory ratchet is what reported `ifnz` absent when a dead entry was removed).
#
# ⚠️ RAISING THE FLOOR IS THE POINT. When you make the compiler handle more, update the constants
# below IN THE SAME COMMIT and say what you unlocked. Lowering one is a deliberate act that needs a
# reason in the commit message — most legitimately "clauses that were emitting DEAD rules are now
# declined", which is how this floor got lower than the number reported earlier today:
#
#     51.2%  emitted, of which ~183 clauses produced rules that could never fire
#     27.5%  emitted, all of which actually execute
#
# Coverage went DOWN because correctness went UP. That is a legitimate lowering; a silent one is not.
#
# ─── WHAT IS COUNTED ─────────────────────────────────────────────────────────────────────────────
# ABSOLUTE emitted clause counts, not percentages. A percentage moves when the corpus grows, which
# would make an unrelated `.metta` file fail this test. Absolute counts only fall when the compiler
# regresses or a file is deleted.
#
# Compiled with the CORPUS-WIDE function set (`extra_funs`), which is how a real multi-file program
# is compiled. Scoping per file understates coverage by ~20 points — measured 2026-08-06, 31.5% vs
# 51.2% — because every cross-file call then looks unexecutable.
using MeTTaCore
using Test

const _RF = MeTTaCore.CompilerFrontend
const _RA = MeTTaCore.CompilerANormal
const _RE = MeTTaCore.CompilerEmit
const _RS = MeTTaCore.StandardMeTTa
const _RI = MeTTaCore.Eval

# ── THE FLOOR — 275 -> 366 (staging) -> 351 (control-flow expansion). ────────────────────────────
# Every number is MEASURED from the run that set it, never apportioned by guess.
#
# ⚠️ THIS FLOOR WENT DOWN, DELIBERATELY, AND THE RATCHET IS WHAT CAUGHT IT. Control-flow expansion
# turns `if`/`case`/`superpose` into one clause per execution path, and it must run BEFORE the call
# graph is built — otherwise a call inside a branch arm is invisible to `_call_graph`, which walks
# only the top-level goal list. Making those calls visible is the point, and it had a consequence:
#
#     call-graph edges   717 -> 960   (+243)
#     cyclic heads        32 -> 219   (+187)
#
# 184 heads are newly RECOGNISED as recursive — `List.append`, `List.foldl`, `List.length`,
# `List.member`, `Map.find` — because their recursive call sits inside a `case` arm. Before, the graph
# could not see it, so `List.length` looked acyclic, was assigned a FINITE stage, and emitted rules
# that fire once and stop. Those 15 clauses were never working; they were counted.
#
# Coverage went DOWN because correctness went UP — the same trade as 51.2% -> 27.5%. A silent lowering
# would not be acceptable; this one is measured, attributed, and stated.
#
# WHAT THIS MEASURES FOR THE NEXT FRAGMENT: recursion is now the dominant blocker (219 cyclic heads),
# not `:residual`. It has a verified upstream idiom — exec-chaining with a Peano counter
# (`MM2_Structuring_Code/structuring_code_04_Control.md:157-202`, all primitives confirmed working on
# our kernel 2026-08-07) — which needs no finite stage at all.
# RAISED 2026-08-07 by allowing ARITHMETIC AND CALLS in one body: 351 -> 374 (+23, all in `lib`).
# ⚠️ PREDICTED 65, GOT 23. The sizing probe inspected goal SHAPES without running the real emitters,
# so it counted clauses that then hit other guards. Recorded because the estimate drove the choice of
# this fragment over recursion, and a 2.8x over-estimate is worth distrusting next time.
# Comparison ops are NOT yet wired — `is_arith` covers only `+ - * % /`, so `==` (385 call sites),
# `<`/`>`/`<=`/`>=` remain declined even though MORK has `eq_i64`/`lt_i64`/`gt_i64`/`ne_i64`.
# RAISED 2026-08-10 by lowering PATTERNS AS DATA (`translate_pattern`): MM2 374 -> 376 (+2, lib),
# MeTTa-IL 687 -> 726 (+39). Both pattern sites — `let` bindings and `case`/`if` arms — ran the
# EXPRESSION translator over a pattern, so an all-variable tuple like `($h $t)` fell to the catch-all
# and became a `GResidual`, declining the whole clause. A pattern computes nothing; it lowers to
# itself and emits no goals.
# ⚠️ PREDICTED 111, GOT 39 — the SECOND 2.8x over-estimate from a shape-counting probe, and this time
# the reason is identifiable rather than mysterious: the probe counted clauses whose only residual was
# a variable-headed expression, but only those in PATTERN position are fixed by this. 74 clauses still
# carry one in VALUE position (`(let $_ ($func $head) …)` in `for-each-in-atom`) — a DYNAMIC CALL, and
# emitting it as data would be a wrong answer. Position decides, not node type.
# ⚠️ NEXT FRAGMENT IS `match` — 104 clauses, the single largest remaining, and 109 contain one. Note
# for whoever takes it: `match` searches a SPACE, and `presentations/mettail.metta` records that the
# atomspace is exactly what a term rewrite CANNOT express. Check that before assuming it lowers.
# MM2 ALSO ROSE, 376 -> 377 (src/standard 8 -> 9), from the same narrowing: `chain`'s arguments are
# no longer hoisted, and one clause that the hoisted goals had been blocking now emits. Small, but
# raised in the same commit because a floor left below the measurement is a floor that cannot catch
# the next regression.
const FLOOR_STDLIB = 11     # of 61  clauses (10 -> 11, the `()` unit-atom fix, 2026-08-12:
# a stdlib clause containing `()` used to lower to `(Nil)` and fail)
const FLOOR_STANDARD = 9     # of 51
const FLOOR_LIB = 376    # of 888   (358 -> 360, arity-aware `is_fun`, 2026-08-11;
                         #            360 -> 376 measured 2026-09-03 — DRIFT since 08-11, not one
                         #            change; the ratchet asked for the raise, so it is banked here)
const FLOOR_TOTAL = 396    # of 1000  (380 -> 396 measured 2026-09-03, banking pre-existing drift;
                           #            stdlib + src/standard sum to exactly their floors, so the whole
                           #            rise is `lib`. 377 -> 379 arity-aware `is_fun` 2026-08-11;
#           379 -> 380 the `()` unit-atom fix 2026-08-12)

# ── THE MeTTa-IL STAGE (EmitIL.jl, 2026-08-09) — its own floor, on the SAME corpus ───────────────
# MEASURED, not predicted: 687 of 1000, against MM2's 374. The design doc argued minimal MeTTa should
# cover more because `unify` is 4-ary (branches are native), `collapse-bind` is findall, and
# disjunction is just several `(=)` clauses — where an MM2 exec atom has none of those. Emit.jl:30-31
# emits only all-GCall/GUnify clauses; the IL handles 5 of 6 goal types. Predicted direction, and this
# time the magnitude was measured BEFORE being written down: 1.84x.
#
#     stdlib        10 -> 57    src/standard   8 -> 28    lib   356 -> 602
#
# Remaining declines account exactly: 687 emitted + 163 GResidual + 149 nested-goal + 1 zero-branch
# GDisj = 1000. The zero-branch case was found BY this measurement — it reported "expanded = -1",
# which is impossible, and turned out to be a clause counted as emitted while producing no clauses.
# RAISED AGAIN 2026-08-10 by lowering `match`: 726 -> 830 (+104), the largest single fragment so far.
# `match` searches a SPACE, so A-normalization has no lowering for it and never will — but THIS target
# does: minimal MeTTa's `eval` is the instruction that reaches into the atomspace, and `(eval (match
# …))` is no less minimal than the `(eval (f args))` every GCall already emits. Verified on our engine
# before being written, then by differential through `compile_run`.
# ⚠️ IT IS GUARDED, AND THE GUARD IS THE DESIGN. A COMPILED program's `&self` holds the emitted IL
# clauses in place of the source rules, so a `match` that can bind a RULE reads a space the source
# never had. Measured: 180 of 182 patterns are data-shaped. Only a SYMBOL head other than `=`/`:` is
# lowered — a bare variable or a variable head is declined, because either can bind a rule.
# ⚠️ THE FIRST VERSION OF THIS CHANGE EMITTED `<unrenderable:IRSpecial>` AS A SYMBOL and still counted
# 832. It parsed, it ran, and it answered
#   `(function (chain (eval <unrenderable:IRSpecial>) NotReducible (return NotReducible)))`.
# `CompilerEmit.render` had no `IRSpecial` method. The coverage number was IDENTICAL before and after
# the fix — so THIS RATCHET CANNOT SEE THE DIFFERENCE between 106 clauses that work and 106 that emit
# garbage. Only `test_compile_lane.jl`'s differential caught it. Raise a floor on the strength of an
# execution differential, never on this count alone.
# ⚠️ AND 832 WAS GIVEN BACK TO 830, DELIBERATELY. Fixing it by adding the method to the SHARED
# `CompilerEmit.render` also widened MM2 (376 -> 378), whose decline test is literally
# `startswith(render(a), "<unrenderable")` and which has no `match` instruction to run. Two clauses
# emitting a form their target cannot execute is the same defect in a different lane, and neither the
# suite nor this ratchet could distinguish it from a gain. The renderer now lives in `EmitIL.jl`, MM2
# is back to 376, and the 2 IL clauses that only emitted via the shared widening are declined again.
# RAISED 2026-08-10 by MINIMAL-MeTTa INSTRUCTION PASS-THROUGH: 830 -> 847 (+17). `chain`/`eval`/
# `function`/`return` written directly in source (`stdlib.metta`'s `car-atom` is
# `(chain (decons-atom $atom) $ht (unify ($head $_) $ht …))`) are not forms to lower — they ARE the
# target language, 4 of the 13 instructions in the §3 table, and the lowering is the identity. No
# `eval` wrapper, unlike `match`: `chain` interprets its first argument by definition. A-normalization
# keeps these nodes WHOLE for the same reason it keeps `match` whole — `chain`'s third argument is a
# TEMPLATE with a variable bound in it, and hoisting a computation out of a binder's scope is a wrong
# answer, not an optimisation.
# 🛡️ A RENDER GUARD NOW COVERS EVERY VERBATIM LOWERING, not just the one that needed it. Any residual
# lowered whole is rejected if its rendering contains `<unrenderable` — the exact failure that scored
# 832 while emitting garbage. New verbatim lowerings inherit the check by construction.
# ⚠️ 848 WAS AVAILABLE AND WAS NOT TAKEN. Keeping all four instructions whole in the SHARED
# `ANormal._KEEP_WHOLE` cost MM2 four `lib` clauses (358 -> 354, total 376 -> 373) — THIS RATCHET
# caught it and the rest of the suite did not. `eval`/`function`/`return` have no binder, so
# A-normalizing their arguments is sound and MM2 uses the goals; only `chain` must be kept whole.
# Narrowed: MM2 377, IL 847. One IL clause is the price of not regressing the other lane.
# RAISED 2026-08-11 by ARITY-AWARE `is_fun`: 847 -> 864 (+17), MM2 377 -> 379. `funs` became a set of
# (head, ARITY) pairs instead of names, and `constrain_args` now GATES its hoist on it the way PeTTa
# does (`translator.pl:9-12`). Previously ANY symbol-headed expression in a pattern argument was run
# through `translate_expr`; the pattern survived only because `funs` was near-empty per form. Gating
# it means constructor patterns are kept, more clauses A-normalize cleanly, and coverage rises as a
# SIDE EFFECT of a correctness fix — the direction this ratchet is supposed to reward.
# The counterexample that forced it: `b1_equal_chain.metta` defines `S` at arity 3 (SKI) and uses it
# at arity 1 (Peano), so name-keying hoisted `(S $y)` out of a rule head and broke the clause.
# RAISED 2026-08-11 by LOWERING VARIABLE-HEADED BODIES: 864 -> 930 (+66), MM2 unchanged at 379.
# `(= (apply2 $f $x $y) ($f $x $y))` — the largest single decline class (CODEMAP: 97 of 153 residuals,
# and every higher-order shape in `d2_higherfunc`) — now emits
# `(chain (metta ($f $x $y) %Undefined% &self) $out …)`. `metta` IS runtime dispatch, so nothing is
# invented: it is PeTTa's `reduce/2` expressed in one of the thirteen instructions, which is exactly
# the objection `ANormal.jl:208` raised against inventing a closure representation.
#
# ⚠️ THIS EXACT CHANGE WAS TRIED AND REVERTED EARLIER THE SAME DAY (`d052bcb`), when it took
# d2_higherfunc from 3 extra errors to 13. It was never the defect: diagnosing those 13 showed #1 was
# `((curry +) 2)`, a PARTIAL APPLICATION that must stay unreduced — which a body lowering cannot
# affect. The cause was the NESTED HEAD being rebuilt lossily as `(name head_args…)` (`896cdc3`).
# With that declined, this lands clean: both corpora green, fuzz green, and the eval-one-step gate
# still 0 violations over all 930 clauses. Reverting it was right; so was going back for it.
const FLOOR_IL_TOTAL = 930   # of 1000
# ── IL's RESIDUAL-FREE floor — how much of that 930 is actually COMPILED ────────────────────────
# MEASURED 2026-09-03: 742 of 1000. ⇒ **20.2% of IL's EMITTED clauses carry a `GResidual` escape**,
# i.e. `_instr(::GResidual)` renders the node VERBATIM into IL for the MINIMAL INTERPRETER to run.
# A real deferral at a different layer — exactly what a closure calling `interpret` would be.
#
# 🔴 SO `FLOOR_IL_TOTAL = 930` OVERSTATES NATIVE COMPILATION BY ~188 CLAUSES, and nothing said so
# until this floor existed. "Emitted" and "compiled" are DIFFERENT NUMBERS for any emitter with a
# deferral path — IL, and the coming closure emitter — but NOT for MM2, whose exec atoms cannot
# express an interpreter call, so there the two coincide.
#
# ⚠️ THIS IS THE HONEST BASELINE FOR A CLOSURE EMITTER'S THIRD NUMBER: comparing "closure
# residual-free" against 930 would flatter it. 742 is the number to beat.
const FLOOR_IL_RESIDUAL_FREE = 742   # of 1000

"Parens balance, ignoring anything inside a MeTTa string literal."
function _rt_balanced(s::AbstractString)::Bool
    depth = 0
    instr = false
    esc = false
    for c in s
        if esc
            esc = false
        elseif instr
            c == '\\' ? (esc = true) : (c == '"' && (instr = false))
        elseif c == '"'
            instr = true
        elseif c == '('
            depth += 1
        elseif c == ')'
            depth -= 1
            depth < 0 && return false
        end
    end
    depth == 0 && !instr
end

"""Is this emitted IL a well-formed clause at all?

🔴 THE RATCHET COUNTED GARBAGE AND SCORED IT IDENTICALLY. MEASURED 2026-08-10: the `match` lowering
shipped without an `IRSpecial` renderer, so every one of 106 clauses embedded the marker string AS A
SYMBOL —

    (= (f) (function (chain (eval <unrenderable:IRSpecial>) \$t (return \$t))))

— which PARSES, RUNS, and answers `(function (chain (eval <unrenderable:IRSpecial>) NotReducible
(return NotReducible)))`. The count was 832 before the fix and 832 after. A number that cannot
distinguish working output from garbage is not a gate, and this file's whole purpose is to be one.

⚠️ THIS IS A CHEAP STRUCTURAL CHECK, NOT AN EXECUTION ORACLE, and the difference is the point of
keeping both. It catches output that is not a clause; `test_compile_lane_corpus.jl` catches a clause
that computes the WRONG ANSWER. Neither subsumes the other — the 832 defect was invisible to the
corpus differential too, because `emit_il_program` is not what that runs.

Four properties, each the cheapest form of its class:
  * no `<unrenderable` marker — the exact failure above
  * PARENS BALANCE — see below; parsing does NOT imply this
  * parses as a SINGLE atom — trailing junk means two clauses ran together
  * is a `(= lhs rhs)` — the only shape this stage is allowed to produce

⚠️ THE BALANCE CHECK IS SEPARATE BECAUSE "IT PARSES" DOES NOT MEAN "IT IS BALANCED". Found by this
gate's own self-test on its first run: `_rt_wellformed("(= (f) (chain")` returned TRUE. `parse_from`
SILENTLY CLOSES unterminated input at EOF, so a truncated emission comes back as the well-formed atom
`(= (f) (chain))` and every parser-based property passes. A test of the checker is why that is known;
without it the gate would have shipped believing it caught truncation.
"""
function _rt_wellformed(clause::AbstractString)::Bool
    occursin("<unrenderable", clause) && return false
    _rt_balanced(clause) || return false
    a = try
        toks = _RI.tokenize(clause)
        i = Ref(1)
        v = _RI.parse_from(toks, i, _RI.Space().tokens)
        i[] > length(toks) || return false          # trailing junk ⇒ not ONE atom
        v
    catch
        return false
    end
    a isa _RS.Expression || return false
    ch = (a::_RS.Expression).children
    length(ch) == 3 && ch[1] isa _RS.Sym && (ch[1]::_RS.Sym).name === :(=)
end

"Parse MeTTa text to surface atoms WITHOUT evaluating — a compiler frontend must not run the program."
function _ratchet_parse(sp, text::AbstractString)::Vector{_RS.Atom}
    toks = _RI.tokenize(text)
    i = Ref(1)
    out = _RS.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _RI.parse_from(toks, i, sp.tokens))
    end
    out
end

@testset "compiler coverage RATCHET — emitted clauses may not decrease" begin
    sp = _RI.Space()
    _RI.load_core_stdlib!(sp)
    root = normpath(joinpath(dirname(pathof(MeTTaCore)), ".."))
    groups = ["stdlib" => joinpath(root, "stdlib"),
        "src/standard" => joinpath(root, "src", "standard"),
        "lib" => joinpath(root, "lib")]

    files = String[]
    for (_, d) in groups, (rt, _, fs) in walkdir(d), f in fs
        endswith(f, ".metta") && push!(files, joinpath(rt, f))
    end

    # Pass 1 — every defined head in the whole corpus, so cross-file calls are visible.
    programs = Dict{String, MeTTaCore.CompilerIR.IRProgram}()   # NO `Any`: standing project rule, tests included
    allfuns = Set{Symbol}()
    for f in files
        atoms = try
            _ratchet_parse(sp, read(f, String))
        catch
            continue
        end
        prog = try
            _RF.lower_program(atoms)
        catch
            continue
        end
        programs[f] = prog
        for d in prog.definitions
            push!(allfuns, d.name)
        end
    end
    @test !isempty(programs)                       # the corpus loaded at all
    @test length(allfuns) > 500                    # and produced a plausible head set

    # Pass 2 — emit with that set.
    counts = Dict{String, Tuple{Int, Int}}()        # group => (emitted, total)
    for (label, dir) in groups
        em = 0
        tot = 0
        for f in files
            startswith(f, dir) || continue
            haskey(programs, f) || continue
            cls = try
                _RA.translate_program(programs[f])
            catch
                continue
            end
            r = _RE.emit_program(cls; extra_funs=allfuns)
            em += r.emitted
            tot += length(cls)
        end
        counts[label] = (em, tot)
    end
    total_em = sum(first(v) for v in values(counts))
    total_tot = sum(last(v) for v in values(counts))

    for (label, floor) in ("stdlib" => FLOOR_STDLIB, "src/standard" => FLOOR_STANDARD,
        "lib" => FLOOR_LIB)
        em, tot = counts[label]
        @info "compiler coverage" group=label emitted=em total=tot floor=floor
        @test em >= floor
    end
    @info "compiler coverage TOTAL" emitted=total_em total=total_tot floor=FLOOR_TOTAL
    @test total_em >= FLOOR_TOTAL

    # ── THE MeTTa-IL STAGE, same corpus, same pass ─────────────────────────────────────────────
    # Ratcheted separately from MM2 because they are different targets with different reach, and a
    # single number would hide a regression in one behind a gain in the other. Accounting is checked
    # too, not just the floor: emitted + declined must equal the clause count. That identity is what
    # caught the zero-branch GDisj bug — a clause was counted emitted while producing nothing, and
    # only the totals disagreeing revealed it.
    il_em = 0
    il_resfree = 0
    il_tot = 0
    il_out = 0
    il_decl = 0
    malformed = String[]
    for f in files
        haskey(programs, f) || continue
        cls = try
            _RA.translate_program(programs[f])
        catch
            continue
        end
        r = MeTTaCore.CompilerEmitIL.emit_il_program(cls)
        il_em += r.emitted
        for c in cls           # residual-free = emitted AND no `GResidual` anywhere in its goals
            MeTTaCore.CompilerEmitIL.emit_il_clause(c) === nothing && continue
            MeTTaCore.CompilerEmitIL._first_residual(c.goals) === nothing && (il_resfree += 1)
        end
        il_tot += length(cls)
        il_out += length(r.clauses)
        il_decl += length(r.declined)
        for c in r.clauses
            _rt_wellformed(c) || (length(malformed) < 8 && push!(malformed, first(c, 110)))
        end
    end
    # 🔴 A COUNT MUST NOT BE ABLE TO COUNT GARBAGE — see `_rt_wellformed`.
    for m in malformed
        @info "MALFORMED emitted IL" clause=m
    end
    @test isempty(malformed)

    # ⚠️ AND THE GATE ITSELF IS EXERCISED, because a check that has never rejected anything is not
    # known to work — the same reason every differential here carries a positive control. The first
    # string is verbatim what the emitter produced for 106 clauses while the ratchet scored 832.
    @test !_rt_wellformed(
        "(= (f) (function (chain (eval <unrenderable:IRSpecial>) \$t (return \$t))))"
    )
    @test !_rt_wellformed("(= (f) (chain")                       # unbalanced ⇒ not one atom
    @test !_rt_wellformed("(= (f) a) (= (g) b)")                 # two atoms ⇒ not one clause
    @test !_rt_wellformed("(foo bar)")                           # not a `(=)` clause
    @test _rt_wellformed("(= (f \$x) (function (return \$x)))")  # …and a real one passes
    @info "MeTTa-IL coverage TOTAL" emitted=il_em total=il_tot floor=FLOOR_IL_TOTAL clauses_out=il_out
    @info "MeTTa-IL RESIDUAL-FREE" residual_free=il_resfree emitted=il_em floor=FLOOR_IL_RESIDUAL_FREE
    @test il_em >= FLOOR_IL_TOTAL
    @test il_resfree >= FLOOR_IL_RESIDUAL_FREE
    @test il_resfree <= il_em                # residual-free is a SUBSET of emitted, never larger
    @test il_em + il_decl == il_tot          # every clause is emitted OR declined — never dropped
    @test il_out >= il_em                    # emission never produces FEWER clauses than it counts
    @test il_em > total_em                   # the IL is the better target; if this flips, find out why

    # ── THE DECLINE HISTOGRAM IS A MEASUREMENT, SO IT RUNS ─────────────────────────────────────
    # These figures drive every "what to build next" decision. They were previously narrated in a
    # CURATED CODEMAP ROW -- the artifact meant to BE the trusted source, not a stray docstring -- and
    # within a day they were wrong AND THE RANKING HAD INVERTED:
    #
    #     CODEMAP row said  call_in_body 237 · residual 209 · control_flow 177 · mixed_arithmetic 95
    #     re-measured       residual 301 · call_in_body 180 · control_flow 146 · mixed_arithmetic 91
    #     after staging     residual 301 · control_flow 146 · mixed_arithmetic 91 · call_in_body 89
    #     after expansion   residual 300 · control_flow 144 · call_in_body 107 · mixed_arithmetic 91
    # `call_in_body` ROSE 89 -> 107 because expansion exposes calls that were hidden inside branch
    # arms; `decline_reason` is first-match, so those clauses simply moved bucket.
    #
    # `residual` overtook `call_in_body` as the largest bucket, which changes the priority order. A
    # number in prose is a measurement AT A TIME and does not announce when it expires; a number in a
    # test cannot go stale silently. Prints on every run so a shifted ranking is visible immediately.
    hist = Dict{Symbol, Int}()
    for f in files
        haskey(programs, f) || continue
        cls = try
            _RA.translate_program(programs[f])
        catch
            continue
        end
        r = _RE.emit_program(cls; extra_funs=allfuns)
        for cl in r.declined
            k = _RE.decline_reason(cl)
            hist[k] = get(hist, k, 0) + 1
        end
    end
    @info "compiler DECLINE HISTOGRAM (re-measured every run)" sort(
        collect(hist), by=x -> -x[2]
    )
    @test sum(values(hist)) == total_tot - total_em      # every decline is attributed
    @test haskey(hist, :residual) && haskey(hist, :call_in_body)

    # A ratchet that only ever passes teaches nothing. If coverage has RISEN, say so loudly so the
    # floor gets raised in the same commit rather than drifting stale and stopping being a ratchet.
    if total_em > FLOOR_TOTAL
        @warn "compiler coverage ROSE above the floor — RAISE FLOOR_TOTAL (and the group floors) " *
            "in this commit" floor=FLOOR_TOTAL now=total_em
    end
end
