# DualTrack.jl — the dual-track capstone: ONE entry over both execution lanes.
#
# This session built two lanes (project_dual_track_mettail): the CeTTa-style DIRECT lane
# (MM2 programs → `mm2_route!`) and the F1R3FLY MeTTa-IL lane (rewrites/pipelines/GSLT theories →
# `metta_il_run!`/`metta_il_run_pipeline!`/`theory_run!`). They are different FRONT-ENDS over the same
# MM2/MORK substrate, so `mc_run` dispatches by the program's FORM (not by interchangeable engine):
#
#   (theory …)  → GSLT theory lane     (theory_run!)        — pass theory=NAME to pick one
#   (def …)     → def/match/emit lane  (metta_il_run_pipeline!)
#   (~> …)      → rewrite lane          (metta_il_run!)      — saturate=true for recursive closure
#   otherwise   → DIRECT lane           (mm2_route!)         — MM2 exec / data / !(match …)
#
# `mode` forces a lane (:direct/:rewrite/:pipeline/:theory). Returns `(; lane, results)` — the chosen
# lane plus its NATIVE result (Vector{String} for the IL lanes; the route NamedTuple for :direct).

_dual_heads(program::AbstractString) =
    Set{String}(mm2_head(f) for (bang, f) in mm2_split_forms(program) if !bang)

function _last_theory_name(program::AbstractString)
    name = nothing
    for (bang, f) in mm2_split_forms(program)
        (bang || mm2_head(f) != "theory") && continue
        a = mm2_expr_args(f)
        length(a) >= 2 && (name = a[2])
    end
    name
end

# Evaluate `deferred` bangs on a SCRATCH Eval Space over the same program (stdlib + `data` +
# the program's non-bang forms verbatim — never reconstructed from the trie, PathMap normalizes
# variables; the mm2_eq_bisim recipe). Returns [(bang, [answers…])…]. Never writes the MORK space.
# Shared by the streaming (mm2_route!) and supercompiler (sc_execute!) direct-lane branches.
# ── the may-mutate predicate for region staging ──────────────────────────────────────────────────
# REUSES the existing impurity-propagation fixpoint instead of adding a second classifier, and that
# is the whole point: `Eval._pure_heads` is a WHITELIST fixpoint — `Eval.jl:1040` classifies any op
# that is neither a pure primitive nor a defined head as IMPURE, so an unrecognised name fails SAFE
# (extra regions, never a missed barrier). A hand-written denylist of mutator names fails OPEN, which
# is exactly how JeTTa's memo gate went unsound: 6 dead entries with both space mutators MISSPELLED
# (`"add-atom!"` against a registered `add-atom`), silently memoising impure functions.
#
# It needs a stdlib-loaded analysis Space, so it is SKIPPED unless the program has two ADJACENT
# bangs — the only shape in which a mutating query can reach a later query with no definition
# between them. Definition boundaries are handled by the partition itself and need no purity
# information at all.
#
# MEASURED 2026-08-08 (min of 3, noisy — totals spread 8.9–13.8 ms, so read this as order-of-
# magnitude, not precision):
#     defs + 3 adjacent bangs   1 region · predicate 1.3 ms of an 8.9 ms mc_run   ≈ 14%
#     def/bang interleaved      3 regions · predicate 0.00 ms                     short-circuited
#     single bang               1 region · predicate 0.00 ms                      short-circuited
# So this is NOT free on the adjacent-bang shape: it is ~14% bought for soundness. The cheap
# alternative — a denylist of mutator names — costs nothing and is UNSOUND (see above). Dropping
# stdlib from the analysis Space would cut the cost but classify every stdlib call as impure,
# trading one measured cost for an unmeasured one in extra regions. Revisit with a profile if the
# adjacent-bang shape ever shows up hot; do not "optimize" it on intuition.
# MOVED 2026-08-09 to `CompileLane.jl` as `purity_may_mutate`, and called from there rather than
# duplicated. The predicate is lane-neutral — it follows from Invariant 1, not from this lane — and
# this file's direct surface-(=)→MM2 arrow is due for deletion. Two copies of a FAIL-SAFE predicate
# drifting apart is the denylist failure mode one level up: the copy that stops being maintained is
# the one that silently stops being safe.
_mc_may_mutate(program::AbstractString) = purity_may_mutate(program)

function _mc_fallback_eval(data::AbstractString, program::AbstractString,
    deferred::AbstractVector{<:AbstractString};
    fallback::Symbol=:interpreter, fallback_table::Bool=true)
    evaluated = Tuple{String, Vector{String}}[]
    (fallback === :interpreter && !isempty(deferred)) || return evaluated
    isp = Eval.Space()
    Eval.load_core_stdlib!(isp)
    isempty(strip(data)) || Eval.load_metta!(isp, data)
    for (bang, f) in mm2_split_forms(program)
        bang || Eval.load_metta!(isp, f)
    end
    # Memoize PURE heads for the bang evals (auto_table! is purity-gated and result-preserving;
    # fib(17) 294×, commit 410d1a4). Tabling state (_TABLED_HEADS/_ANSWER_TABLE) is
    # PROCESS-GLOBAL, so snapshot/restore: heads tabled for this scratch eval must not leak —
    # another Space's same-NAMED head may be impure, and memoizing an impure function is
    # unsound. The answer cache is cleared on restore (perf-only for other spaces; their
    # revision stamps evict stale entries anyway).
    prev_tabled = fallback_table ? copy(Eval._TABLED_HEADS) : nothing
    try
        fallback_table && Eval.auto_table!(isp)
        for b in deferred
            res = Eval.load_metta!(isp, "!" * b)   # re-prefix exactly as mm2_eq_bisim does
            push!(evaluated,
                (
                    String(b),
                    String[
                        string(x) for r in res for x in (r isa AbstractVector ? r : [r])
                    ]
                ))
        end
    finally
        if prev_tabled !== nothing
            empty!(Eval._TABLED_HEADS)
            union!(Eval._TABLED_HEADS, prev_tabled)
            Eval._table_reset!()
        end
    end
    evaluated
end

"""
    mc_run(cs, data, program; mode=:auto, theory=nothing, saturate=false, steps=1_000_000) -> (; lane, results)

Unified dual-track entry. Auto-dispatches by program form (`mode=:auto`) to the lane that fits, or force
a lane with `mode ∈ (:direct, :rewrite, :pipeline, :theory)`. For the theory lane, `theory=NAME` selects
which theory to run (default = the last `(theory …)` defined). `saturate=true` runs the rewrite/theory
lane to fixpoint (recursive closure). On the **direct** lane, `supercompile=true` (OFF by default) routes
through the MorkSupercompiler (`sc_execute!`, options `sc_opts`) instead of the lean streaming calculus —
for multi-source-conjunction / Rule-of-64 / closure workloads (it MATERIALIZES, ~5–30× slower otherwise,
so never use it as a general accelerator). Returns the chosen `lane` and its native `results`.

Direct-lane **interpreter fallback** (`fallback=:interpreter`, default ON): bangs the ZAM/MM2 lane cannot
serve (`route.deferred` — anything but `!(match …)`) are evaluated on the Eval over the SAME
program (fresh typed Space + stdlib + `data` + the program's non-bang forms; each deferred bang
re-prefixed with `!` — the `mm2_eq_bisim` recipe, MM2Router.jl). This is the merge design's §5 R7 lane 3
("grounded/control stay in the interpreter lane") and MeTTa-spec §4 conformance (a `!`-atom must be
evaluated, not silently deferred). Results land in `results.evaluated::Vector{Tuple{String,Vector{String}}}`;
`results.deferred` stays as the honest routing record of what the fastlane could not serve. The fallback
evaluates in a scratch Space — it never writes the MORK space. `fallback=:none` = pure-routing behavior.
`fallback_table=true` (default) runs `auto_table!` on the scratch Space before evaluating — purity-gated,
result-preserving memoization of the program's PURE heads (fib(17) 294×, commit 410d1a4); the process-global
tabling state is snapshot/restored so nothing leaks to other Spaces.

Under `supercompile=true` the same discipline applies (SC-lane BANG HYGIENE): the SC frontend's byte
parsers treat `!` as a symbol byte and would corrupt a raw bang into inert trie atoms, so bangs are
stripped bang-aware before `sc_execute!` — match-bangs pass BARE (still lowered via §10.3), non-match
bangs go to the interpreter fallback. The supercompile branch returns `(; sc::SCResult, evaluated,
deferred, zam_served)` (previously the bare `SCResult`; no test/src consumer read its fields through
`mc_run`).

FASTLANE-FIRST (streaming branch): before the interpreter fallback, deferred bangs in the
reduction-servable SAFE SUBSET (all rules lowered · one clause per head · acyclic · no nested
rule-head calls — see `mm2_zam_answers`) are answered ON the ZAM itself via scratch-space
demand-injection + redex-delete readback; `results.zam_served` lists the bangs the ZAM answered.
"""
function mc_run(cs::CoreSpace, data::AbstractString, program::AbstractString;
    mode::Symbol=:auto, theory=nothing, saturate::Bool=false, steps::Int=1_000_000,
    supercompile::Bool=false, sc_opts::SCOptions=SC_DEFAULTS, eq_mode::Symbol=:reduction,
    fallback::Symbol=:interpreter, fallback_table::Bool=true)
    heads = _dual_heads(program)
    lane = if mode != :auto
        mode
    elseif (theory !== nothing || "theory" in heads)
        :theory
    elseif "def" in heads
        :pipeline
    elseif "~>" in heads
        :rewrite
    else
        :direct
    end
    results = if lane === :theory
        tname = theory !== nothing ? String(theory) : _last_theory_name(program)
        tname === nothing && error(
            "mc_run: :theory lane needs a (theory …) in the program or theory=NAME"
        )
        theory_run!(cs, data, program, tname; steps=steps, saturate=saturate,
            use_magic_sets=sc_opts.use_magic_sets, magic_query=sc_opts.magic_query,
            magic_bound=sc_opts.magic_bound)
    elseif lane === :pipeline
        metta_il_run_pipeline!(cs, data, program; steps=steps)
    elseif lane === :rewrite
        metta_il_run!(cs, data, program; steps=steps, saturate=saturate,
            use_magic_sets=sc_opts.use_magic_sets, magic_query=sc_opts.magic_query,
            magic_bound=sc_opts.magic_bound)
    elseif lane === :direct
        isempty(strip(data)) || space_add_all_sexpr!(cs.inner, data)
        # opt-in (OFF by default): route the Direct lane through the MorkSupercompiler (join-planning /
        # Rule-of-64 decomposition / saturation). It MATERIALIZES intermediate joins (~5–30× vs the
        # streaming ZAM calculus), so it's a win only for multi-source conjunctions, not general queries.
        if supercompile
            # SC-lane BANG HYGIENE: the SC frontend's byte parsers treat `!` as a symbol byte
            # (frontend/SExpr.jl _sym_byte; MORK Frontend symbol branch), so a raw bang would be
            # CORRUPTED into two inert trie atoms (`!` + the query) instead of running. `!(match …)`
            # only survived because §10.3 _lower_match_snode keys on the (match …) list node and
            # tolerates the stray `!` atom. So: split bang-AWARE here (mm2_split_forms), pass
            # non-bang forms verbatim + match-bangs BARE (still lowered via §10.3 — and the stray-`!`
            # trie pollution disappears), and route non-match bangs to the interpreter fallback,
            # exactly like the streaming branch's deferred.
            keep = String[]
            sc_deferred = String[]
            for (bang, f) in mm2_split_forms(program)
                if !bang || mm2_head(f) == "match"
                    push!(keep, f)
                else
                    push!(sc_deferred, f)          # SC cannot serve a non-match bang
                end
            end
            scres = sc_execute!(cs, join(keep, "\n"); opts=sc_opts)
            evaluated = _mc_fallback_eval(data, program, sc_deferred;
                fallback=fallback, fallback_table=fallback_table)
            (; sc=scres, evaluated, deferred=sc_deferred, zam_served=String[])
        else
            # ── PREFIX-EXACT REGION STAGING (MeTTa Invariant 1: effects are sequential) ──────────
            # This branch used to hand the WHOLE program to all three consumers at once, so every
            # bang saw every rule regardless of textual order. MEASURED 2026-08-08:
            #     (= (f) a) !(f) (= (f) b) !(f)  →  ["a","b"] twice, where the oracle gives
            #                                       ["a"] then ["a","b"]
            # All three consumers flatten independently — `mm2_route!` lowers the whole program,
            # `mm2_zam_answers` re-splits it (`MM2Router.jl:496`), and `_mc_fallback_eval` loads
            # EVERY non-bang form before evaluating ANY bang (`DualTrack.jl:39-41`). One region loop
            # fixes all three, because each now receives the program PREFIX up to its own queries.
            #
            # The partition itself is lane-neutral and lives in `SexprForms.jl` — it follows from
            # Invariant 1, not from this lane, and it must outlive the direct-lowering arrow that
            # this file exists to serve. The `:rewrite` (MeTTa-IL) lane cannot exhibit the defect
            # TODAY only because `_il_assert_all_rewrites` refuses any program containing a bang
            # (`MeTTaIL.jl:50`); it inherits the defect the day the compiler's emitter feeds it
            # bang-bearing programs, and will call the same partition.
            #
            # `prog_r` is CUMULATIVE in definitions and LOCAL in queries: all rules seen so far plus
            # only this region's bangs. Re-adding earlier rules to `cs` is a no-op (the MORK trie is
            # a set) and their redexes are already consumed, so they do not re-fire.
            regions = split_program_regions(program, _mc_may_mutate(program))
            n_exec = 0
            n_data = 0
            matched = Tuple{String, Vector{String}}[]
            deferred = String[]
            evaluated = Tuple{String, Vector{String}}[]
            zam_served = String[]
            cum = String[]
            for r in regions
                append!(cum, r.defs)
                prog_r = region_program(ProgramRegion(cum, r.queries))
                route = mm2_route!(cs, prog_r; steps=steps, eq_mode=eq_mode)
                # FASTLANE-FIRST, literal: deferred bangs in the reduction-servable SAFE SUBSET are
                # answered ON the ZAM (mm2_zam_answers — scratch space, redex-delete readback); only
                # the remainder goes to the interpreter FALLBACK (design §5 R7 lane 3; MeTTa-spec §4).
                # Both evaluate in scratch spaces — the live MORK space is not written by either.
                zam = if fallback === :none
                    (; served=Tuple{String, Vector{String}}[],
                        remaining=String[String(b) for b in route.deferred])
                else
                    mm2_zam_answers(prog_r, route.deferred; steps=steps)
                end
                # n_exec/n_data are counts over `prog_r`, which is cumulative ⇒ the LAST region's
                # figures are the program totals. Summing them would double-count earlier rules.
                n_exec = route.n_exec
                n_data = route.n_data
                append!(matched, route.matched)
                append!(deferred, route.deferred)
                append!(evaluated, zam.served)
                append!(
                    evaluated,
                    _mc_fallback_eval(data, prog_r, zam.remaining;
                        fallback=fallback, fallback_table=fallback_table)
                )
                append!(zam_served, String[b for (b, _) in zam.served])
            end
            (; n_exec, n_data, matched, deferred, evaluated, zam_served)
        end
    else
        error("mc_run: unknown mode $mode (expected :auto/:direct/:rewrite/:pipeline/:theory)")
    end
    (lane=lane, results=results)
end
