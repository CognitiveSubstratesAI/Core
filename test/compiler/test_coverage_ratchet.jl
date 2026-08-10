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
const FLOOR_STDLIB  = 10     # of 61  clauses
const FLOOR_STANDARD = 8     # of 51
const FLOOR_LIB     = 358    # of 888
const FLOOR_TOTAL   = 376    # of 1000

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
const FLOOR_IL_TOTAL = 726   # of 1000

"Parse MeTTa text to surface atoms WITHOUT evaluating — a compiler frontend must not run the program."
function _ratchet_parse(sp, text::AbstractString)::Vector{_RS.Atom}
    toks = _RI.tokenize(text); i = Ref(1); out = _RS.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _RI.parse_from(toks, i, sp.tokens))
    end
    out
end

@testset "compiler coverage RATCHET — emitted clauses may not decrease" begin
    sp = _RI.Space(); _RI.load_core_stdlib!(sp)
    root = normpath(joinpath(dirname(pathof(MeTTaCore)), ".."))
    groups = ["stdlib"       => joinpath(root, "stdlib"),
              "src/standard" => joinpath(root, "src", "standard"),
              "lib"          => joinpath(root, "lib")]

    files = String[]
    for (_, d) in groups, (rt, _, fs) in walkdir(d), f in fs
        endswith(f, ".metta") && push!(files, joinpath(rt, f))
    end

    # Pass 1 — every defined head in the whole corpus, so cross-file calls are visible.
    programs = Dict{String, MeTTaCore.CompilerIR.IRProgram}()   # NO `Any`: standing project rule, tests included
    allfuns = Set{Symbol}()
    for f in files
        atoms = try _ratchet_parse(sp, read(f, String)) catch; continue end
        prog  = try _RF.lower_program(atoms) catch; continue end
        programs[f] = prog
        for d in prog.definitions; push!(allfuns, d.name); end
    end
    @test !isempty(programs)                       # the corpus loaded at all
    @test length(allfuns) > 500                    # and produced a plausible head set

    # Pass 2 — emit with that set.
    counts = Dict{String, Tuple{Int,Int}}()        # group => (emitted, total)
    for (label, dir) in groups
        em = 0; tot = 0
        for f in files
            startswith(f, dir) || continue
            haskey(programs, f) || continue
            cls = try _RA.translate_program(programs[f]) catch; continue end
            r = _RE.emit_program(cls; extra_funs = allfuns)
            em += r.emitted; tot += length(cls)
        end
        counts[label] = (em, tot)
    end
    total_em  = sum(first(v)  for v in values(counts))
    total_tot = sum(last(v)   for v in values(counts))

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
    il_em = 0; il_tot = 0; il_out = 0; il_decl = 0
    for f in files
        haskey(programs, f) || continue
        cls = try _RA.translate_program(programs[f]) catch; continue end
        r = MeTTaCore.CompilerEmitIL.emit_il_program(cls)
        il_em += r.emitted; il_tot += length(cls)
        il_out += length(r.clauses); il_decl += length(r.declined)
    end
    @info "MeTTa-IL coverage TOTAL" emitted=il_em total=il_tot floor=FLOOR_IL_TOTAL clauses_out=il_out
    @test il_em >= FLOOR_IL_TOTAL
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
    hist = Dict{Symbol,Int}()
    for f in files
        haskey(programs, f) || continue
        cls = try _RA.translate_program(programs[f]) catch; continue end
        r = _RE.emit_program(cls; extra_funs = allfuns)
        for cl in r.declined
            k = _RE.decline_reason(cl)
            hist[k] = get(hist, k, 0) + 1
        end
    end
    @info "compiler DECLINE HISTOGRAM (re-measured every run)" sort(collect(hist), by = x -> -x[2])
    @test sum(values(hist)) == total_tot - total_em      # every decline is attributed
    @test haskey(hist, :residual) && haskey(hist, :call_in_body)

    # A ratchet that only ever passes teaches nothing. If coverage has RISEN, say so loudly so the
    # floor gets raised in the same commit rather than drifting stale and stopping being a ratchet.
    if total_em > FLOOR_TOTAL
        @warn "compiler coverage ROSE above the floor — RAISE FLOOR_TOTAL (and the group floors) " *
              "in this commit" floor=FLOOR_TOTAL now=total_em
    end
end
