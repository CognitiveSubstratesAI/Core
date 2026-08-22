# AC8 Phase-2b — STATE-DEPENDENT (path-integral) drift: does the entanglement create synergy?
# Spec ../../docs/actpc/AC8_synergy_gate.md §9. Step-2a falsified the LINEAR-drift task (the
# drift-blind single half recovered the rule from the wrap). Implication: the drift must be
# something a constrained single fit CANNOT marginalize but that requires the symbol track to
# estimate. Construction here: the continuous channel is the PATH INTEGRAL of a per-symbol
# increment — z_t = Σ_{τ<t} φ(s_τ) — so z_t depends on the whole symbol HISTORY. Observable
# x_t = ⟨y_t,u⟩ = s_t + z_t (drift along the proto line u, corrupting). To remove z you need
# the track (the rule); to get the track you need z removed. Chicken-egg.
#
# Conditions (profiled-joint = the bridge's joint-inference ideal, deterministic):
#   coupled        = argmin_δ over [φ profiled out: φ̂=lstsq(F(track_δ), x−s_δ)]   (joint δ,φ)
#   symbolic-only  = argmin_δ with φ=0                                           (drift-blind)
#   neural-only    = δ=0 (no rule ⇒ const track) ⇒ φ̂ degenerates to a t-trend   (rule-blind)
#   parallel-uncpl = neural's ẑ (δ=0) subtracted, THEN symbolic picks δ once     (no bridge)
# Capability metric = held-out track accuracy (roll out the induced δ̂ from each seed).
# HONEST: if symbolic-only STILL recovers δ, that's evidence a grid/lstsq harness is too
# powerful to isolate synergy ⇒ the real modality-limited substrates (FabricPC + soup) are
# required. We TEST it, we don't assume it.
using LinearAlgebra, Statistics, Printf, Random

const K = 8           # smaller alphabet (clearer wraps)
const D = 12

make_u(seed) = (rng=MersenneTwister(seed); u=randn(rng, D); u ./ norm(u))
rule_track(s0, δ, T) = Int[mod(s0 + (i - 1) * δ, K) for i in 1:T]

# per-symbol increment φ0 (the drift "law"); path integral z_t = Σ_{τ<t} φ0[s_τ]
make_phi(seed; scale=1.0) = (rng=MersenneTwister(seed); scale .* randn(rng, K))
function zpath(track, φ)
    T = length(track)
    z = zeros(T)
    for t in 2:T
        z[t] = z[t - 1] + φ[track[t - 1] + 1]
    end
    return z
end
function observe(u, s0, δ, φ, T; noise=0.0, seed=1)
    rng = MersenneTwister(seed)
    s = rule_track(s0, δ, T)
    z = zpath(s, φ)
    Y = zeros(T, D)
    for i in 1:T
        Y[i, :] = s[i] .* u .+ z[i] .* u .+ noise .* randn(rng, D)
    end
    return Y, s
end
xproj(u, Y) = Y * u

# cumulative-count features F[t,k] = #(symbol k in s_1..s_{t-1}); then z_t = F[t,:]·φ
function cumfeat(track)
    T = length(track)
    F = zeros(T, K)
    for t in 2:T
        F[t, :] = F[t - 1, :]
        F[t, track[t - 1] + 1] += 1
    end
    return F
end

# residual of rule δ over training seqs, with φ either fixed (=0) or profiled out (lstsq)
function rule_resid(seqs, δ; profile=true)
    Fs = Matrix{Float64}[]
    tg = Float64[]
    rows = Int[]
    for (s0, x) in seqs
        tr = rule_track(s0, δ, length(x))
        F = cumfeat(tr)
        push!(Fs, F)
        append!(tg, x .- tr)
        push!(rows, length(x))
    end
    Fall = reduce(vcat, Fs)
    if profile
        φ̂ = Fall \ tg                       # joint: best drift law given this rule's tracks
        r = Fall * φ̂ .- tg
        return sum(abs2, r) / length(tg), φ̂
    else
        return sum(abs2, tg) / length(tg), zeros(K)   # φ=0 (drift-blind)
    end
end

const ΔG = 1:(K - 1)

# ── MODALITY-FAITHFUL single halves ──────────────────────────────────────────────────────
# The SOUP operates only on DISCRETE tokens: cleanup x→nearest symbol (mod K), then induce
# δ̂ = mode of step-diffs. No continuous drift model — so drift corrupts the tokens directly.
function induce_discrete(seqs)
    counts = zeros(Int, K)
    for (s0, x) in seqs
        ŝ = mod.(round.(Int, x), K)
        for d in diff(ŝ)
            counts[mod(d, K) + 1] += 1
        end
    end
    return argmax(counts) - 1
end
# The NEURAL half does continuous regression only (here: a per-sequence cubic in t — a smooth,
# rule-BLIND channel fit). It has NO discrete rule ⇒ cannot roll out a track (capability=chance).
function neural_dedrift(x)
    T = length(x)
    t = collect(1.0:T) ./ T
    A = hcat(ones(T), t, t .^ 2, t .^ 3)
    return x .- A * (A \ x)
end

# coupled = the BRIDGE ideal: joint inference (continuous precision FROM neural, rule FROM soup).
coupled(seqs) = argmin(δ -> rule_resid(seqs, δ; profile=true)[1], ΔG)
symbolic(seqs) = induce_discrete(seqs)                                   # discrete tokens, raw (drift-corrupted)
parallel(seqs) = induce_discrete([(s0, neural_dedrift(x)) for (s0, x) in seqs])  # neural de-drift → soup, 1-shot

track_acc(testtruth, δ̂) =
    mean(mean(rule_track(s0, δ̂, length(st)) .== st) for (s0, st) in testtruth)

function run(; δ0=1, Ttrain=40, Ttest=60, noise=0.1, φscale=1.0, verbose=true)
    u = make_u(0)
    φ0 = make_phi(3; scale=φscale)
    train_seeds = collect(0:(K - 1))                # all seeds (some wrap within Ttrain)
    test_seeds = [2, 5, 7]                      # UNSEEN-as-instances (held-out episodes)
    wraps(s0, T) = count(i -> rule_track(s0, δ0, T)[i] < rule_track(s0, δ0, T)[i - 1], 2:T)
    trainseqs = [
        (s0, xproj(u, observe(u, s0, δ0, φ0, Ttrain; noise=noise, seed=10 + s0)[1])) for
        s0 in train_seeds
    ]
    testtruth = [(s0, rule_track(s0, δ0, Ttest)) for s0 in test_seeds]

    δ_cpl = coupled(trainseqs)
    δ_sym = symbolic(trainseqs)
    δ_par = parallel(trainseqs)
    _, φ̂c = rule_resid(trainseqs, δ_cpl; profile=true)
    φcorr = cor(φ̂c, φ0)
    cpl = track_acc(testtruth, δ_cpl)
    sym = track_acc(testtruth, δ_sym)
    neu = 1.0 / K                                  # neural-only: no discrete rule ⇒ chance rollout
    par = track_acc(testtruth, δ_par)
    S1 = cpl > sym + 0.1 && cpl > neu + 0.1
    S2 = cpl > par + 0.1
    if verbose
        @printf(
            "φscale=%.1f | δ̂: coupled=%d sym=%d par=%d | acc: cpl=%.2f sym=%.2f neu=%.2f par=%.2f | corr(φ̂,φ0)=%.2f | S1=%s S2=%s\n",
            φscale, δ_cpl, δ_sym, δ_par, cpl, sym, neu, par, φcorr, S1, S2)
    end
    return (; S1, S2, cpl, sym, neu, par, δ_cpl, δ_sym, δ_par)
end

# Robustness sweep over drift magnitude: is there a BROAD synergy window, or is it knife-edge?
println(
    "AC8 Phase-2b — path-integral drift, robustness sweep over drift scale (δ0=1, K=",
    K,
    ")"
)
let any_syn = false
    for φs in (0.5, 1.0, 2.0, 3.0, 4.0, 6.0, 8.0)
        r = run(; φscale=φs)
        any_syn |= (r.S1 && r.S2)
    end
    println("\n>>> ANY robust synergy window (S1∧S2 for some scale): ", any_syn)
end

# ─────────────────────────────────────────────────────────────────────────────────────────
# RESULT (2026-06-10) — PARTIAL POSITIVE. Path-integral drift z_t=Σ_{τ<t}φ(s_τ) (the channel
# is the accumulation of a per-symbol increment ⇒ estimating it REQUIRES the symbol track).
# Modality-faithful single halves: symbolic = discrete tokens (round→induce, drift-corrupted);
# neural = continuous regression only, NO rule (cubic-in-t de-drift). coupled = joint-inference
# IDEAL (continuous precision FROM neural + rule FROM soup). Sweep over drift scale:
#   scale 0.5–1: symbolic STILL recovers δ (small zero-mean φ ⇒ modal step = δ). No gap.
#   scale ≥ 2  : S1 HOLDS ROBUSTLY — coupled 1.00 vs symbolic 0.13 (≈chance), neural 0.12.
#                Large drift destroys the discrete modal-step heuristic; only the continuous
#                JOINT fit recovers δ (and corr(φ̂,φ0)=1.0 — it also recovers the drift law).
#   S2 NOT clean: parallel-uncoupled (cubic-in-t neural de-drift, one-shot) recovers δ by LUCK
#                 at some scales (3,6). The cubic is a poor neural proxy ⇒ S2 is inconclusive here.
#
# CONCLUSION: the redesigned task produces GENUINE S1 capability synergy (coupled ≫ both
# modality-limited singles), robustly for drift scale ≥ 2 — this validates the task. S2
# (synergy = error-EXCHANGE, not ensembling) specifically needs the REAL FabricPC PC neural
# half: its de-drift is principled, so parallel-uncoupled fails STRUCTURALLY (no rule ⇒ no
# proto-baseline ⇒ can't isolate the path-drift), not coincidentally. → Step 2b-real =
# FabricPC PC neural half + real ActPC-Chem soup on THIS task; settle S2 + realize the bridge.
# ─────────────────────────────────────────────────────────────────────────────────────────
