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

"""
    mc_run(cs, data, program; mode=:auto, theory=nothing, saturate=false, steps=1_000_000) -> (; lane, results)

Unified dual-track entry. Auto-dispatches by program form (`mode=:auto`) to the lane that fits, or force
a lane with `mode ∈ (:direct, :rewrite, :pipeline, :theory)`. For the theory lane, `theory=NAME` selects
which theory to run (default = the last `(theory …)` defined). `saturate=true` runs the rewrite/theory
lane to fixpoint (recursive closure). On the **direct** lane, `supercompile=true` (OFF by default) routes
through the MorkSupercompiler (`sc_execute!`, options `sc_opts`) instead of the lean streaming calculus —
for multi-source-conjunction / Rule-of-64 / closure workloads (it MATERIALIZES, ~5–30× slower otherwise,
so never use it as a general accelerator). Returns the chosen `lane` and its native `results`.
"""
function mc_run(cs::CoreSpace, data::AbstractString, program::AbstractString;
                mode::Symbol = :auto, theory = nothing, saturate::Bool = false, steps::Int = 1_000_000,
                supercompile::Bool = false, sc_opts::SCOptions = SC_DEFAULTS)
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
        supercompile ? sc_execute!(cs, program; opts = sc_opts) :
                       mm2_route!(cs, program; steps = steps)
    else
        error("mc_run: unknown mode $mode (expected :auto/:direct/:rewrite/:pipeline/:theory)")
    end
    (lane = lane, results = results)
end
