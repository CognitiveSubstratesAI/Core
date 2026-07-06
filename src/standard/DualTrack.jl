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
        a = mm2_expr_args(f); length(a) >= 2 && (name = a[2])
    end
    name
end

# Evaluate `deferred` bangs on a SCRATCH Interpreter Space over the same program (stdlib + `data` +
# the program's non-bang forms verbatim — never reconstructed from the trie, PathMap normalizes
# variables; the mm2_eq_bisim recipe). Returns [(bang, [answers…])…]. Never writes the MORK space.
# Shared by the streaming (mm2_route!) and supercompiler (sc_execute!) direct-lane branches.
function _mc_fallback_eval(data::AbstractString, program::AbstractString,
                           deferred::AbstractVector{<:AbstractString};
                           fallback::Symbol = :interpreter, fallback_table::Bool = true)
    evaluated = Tuple{String, Vector{String}}[]
    (fallback === :interpreter && !isempty(deferred)) || return evaluated
    isp = Interpreter.Space(); Interpreter.load_core_stdlib!(isp)
    isempty(strip(data)) || Interpreter.load_metta!(isp, data)
    for (bang, f) in mm2_split_forms(program)
        bang || Interpreter.load_metta!(isp, f)
    end
    # Memoize PURE heads for the bang evals (auto_table! is purity-gated and result-preserving;
    # fib(17) 294×, commit 410d1a4). Tabling state (_TABLED_HEADS/_ANSWER_TABLE) is
    # PROCESS-GLOBAL, so snapshot/restore: heads tabled for this scratch eval must not leak —
    # another Space's same-NAMED head may be impure, and memoizing an impure function is
    # unsound. The answer cache is cleared on restore (perf-only for other spaces; their
    # revision stamps evict stale entries anyway).
    prev_tabled = fallback_table ? copy(Interpreter._TABLED_HEADS) : nothing
    try
        fallback_table && Interpreter.auto_table!(isp)
        for b in deferred
            res = Interpreter.load_metta!(isp, "!" * b)   # re-prefix exactly as mm2_eq_bisim does
            push!(evaluated,
                (String(b), String[string(x) for r in res for x in (r isa AbstractVector ? r : [r])]))
        end
    finally
        if prev_tabled !== nothing
            empty!(Interpreter._TABLED_HEADS)
            union!(Interpreter._TABLED_HEADS, prev_tabled)
            Interpreter._table_reset!()
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
serve (`route.deferred` — anything but `!(match …)`) are evaluated on the Interpreter over the SAME
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
                mode::Symbol = :auto, theory = nothing, saturate::Bool = false, steps::Int = 1_000_000,
                supercompile::Bool = false, sc_opts::SCOptions = SC_DEFAULTS, eq_mode::Symbol = :reduction,
                fallback::Symbol = :interpreter, fallback_table::Bool = true)
    heads = _dual_heads(program)
    lane = mode != :auto ? mode :
           (theory !== nothing || "theory" in heads) ? :theory :
           "def" in heads ? :pipeline :
           "~>"  in heads ? :rewrite : :direct
    results = if lane === :theory
        tname = theory !== nothing ? String(theory) : _last_theory_name(program)
        tname === nothing && error("mc_run: :theory lane needs a (theory …) in the program or theory=NAME")
        theory_run!(cs, data, program, tname; steps = steps, saturate = saturate,
            use_magic_sets = sc_opts.use_magic_sets, magic_query = sc_opts.magic_query, magic_bound = sc_opts.magic_bound)
    elseif lane === :pipeline
        metta_il_run_pipeline!(cs, data, program; steps = steps)
    elseif lane === :rewrite
        metta_il_run!(cs, data, program; steps = steps, saturate = saturate,
            use_magic_sets = sc_opts.use_magic_sets, magic_query = sc_opts.magic_query, magic_bound = sc_opts.magic_bound)
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
            keep = String[]; sc_deferred = String[]
            for (bang, f) in mm2_split_forms(program)
                if !bang || mm2_head(f) == "match"
                    push!(keep, f)
                else
                    push!(sc_deferred, f)          # SC cannot serve a non-match bang
                end
            end
            scres = sc_execute!(cs, join(keep, "\n"); opts = sc_opts)
            evaluated = _mc_fallback_eval(data, program, sc_deferred;
                                          fallback = fallback, fallback_table = fallback_table)
            (; sc = scres, evaluated, deferred = sc_deferred, zam_served = String[])
        else
            route = mm2_route!(cs, program; steps = steps, eq_mode = eq_mode)
            # FASTLANE-FIRST, literal: deferred bangs in the reduction-servable SAFE SUBSET are
            # answered ON the ZAM (mm2_zam_answers — scratch space, redex-delete readback); only
            # the remainder goes to the interpreter FALLBACK (design §5 R7 lane 3; MeTTa-spec §4).
            # Both evaluate in scratch spaces — the live MORK space is not written by either.
            zam = fallback === :none ?
                (; served = Tuple{String, Vector{String}}[],
                   remaining = String[String(b) for b in route.deferred]) :
                mm2_zam_answers(program, route.deferred; steps = steps)
            evaluated = vcat(zam.served,
                             _mc_fallback_eval(data, program, zam.remaining;
                                               fallback = fallback, fallback_table = fallback_table))
            (; route..., evaluated, zam_served = String[b for (b, _) in zam.served])
        end
    else
        error("mc_run: unknown mode $mode (expected :auto/:direct/:rewrite/:pipeline/:theory)")
    end
    (lane = lane, results = results)
end
