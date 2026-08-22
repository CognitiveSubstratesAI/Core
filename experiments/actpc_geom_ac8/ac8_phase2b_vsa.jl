# AC8 Phase-2b-VSA — synergy gate S1/S2 with FAST subsymbolic substrates: FabricPC PC neural
# half ↔ FactorVSA associative rule memory (the HDC interlingua the AC8 spec specifies).
# Spec ../../docs/actpc/AC8_synergy_gate.md §9. The real MeTTa soup (ac8_phase2b_real.jl) is
# ~6s per chem-step! ⇒ an iterative bootstrap is ~1 hr, untunable. The discrete rule is instead
# carried in VSA: symbol s ↔ bipolar hypervector v(s); the transition rule is an associative
# memory  T = ⊕_t  v(s_t) ⊗ v(s_{t+1})  (bundle of bound pairs); predict next via
# cleanup(T ⊗ v(s)) = argmax_n ⟨v(n), T⊗v(s)⟩. Native matrix ops (µs), so the full bootstrap +
# drift sweep + multi-seed run is tractable — and the bridge is cleaner (both halves vectorial).
#
# Task = the validated path-integral confound: y_t = proto[s_t] + z_t·ddir + noise,
# z_t = Σ_{τ<t} φ(s_τ) (channel = accumulation of per-symbol increment ⇒ needs the track).
# Modality-limited halves: symbolic = VSA on cleaned DISCRETE tokens (drift-corrupted); neural =
# FabricPC continuous regression, no rule. coupled = bridge bootstrap (rule ⇄ neural de-drift).
# parallel-uncoupled = neural de-drifts RULE-BLIND (position only) → VSA learns once. S2 control.
using FabricPC, FactorVSA, Random, LinearAlgebra, Statistics, Printf
import FactorVSA: HV, BipolarMAP, Codebook, random_codebook, bind, bundle, cleanup, permute

# ---------------- task (path-integral drift in proto space) ----------------
nextsym(s, δ, K) = mod(s - 1 + δ, K) + 1
function make_data(rng; nseq, T, K, Dy, δ, φscale, noise, proto, ddir, φ)
    Y = zeros(Float32, nseq * T, Dy)
    S = zeros(Int, nseq * T)
    seqid = zeros(Int, nseq * T)
    seeds = rand(rng, 1:K, nseq)
    r = 1
    for b in 1:nseq
        s = seeds[b]
        z = 0.0f0
        for t in 1:T
            S[r] = s
            seqid[r] = b
            Y[r, :] = proto[s, :] .+ z .* ddir .+ noise .* randn(rng, Float32, Dy)
            z += φ[s]
            s = nextsym(s, δ, K)
            r += 1
        end
    end
    (; Y, S, seeds, seqid)
end
proto_rows(P, idx) = reduce(vcat, (transpose(@view P[idx[i], :]) for i in eachindex(idx)))
clean_proto(P, M) = [
    argmin([sum((@view(P[k, :]) .- @view(M[i, :])) .^ 2) for k in 1:size(P, 1)]) for
    i in 1:size(M, 1)
]
function histfeat(track, seqid, K)
    n = length(track)
    F = zeros(Float32, n, K)
    for r in 2:n
        (seqid[r] == seqid[r - 1]) && (F[r, :]=F[r - 1, :]; F[r, track[r - 1]] += 1)
    end
    F
end
posfeat(seqid, T) =
    reshape(Float32[(((r - 1) % T) + 1) / T for r in 1:length(seqid)], length(seqid), 1)

# ---------------- neural half (FabricPC PC, Linear ⇒ autodiff-free) ----------------
function build_net(Kin, Dy; H=10)
    cin = Linear((Kin,), "c")
    h = Linear((H,), "h"; activation=TanhActivation())
    out = Linear((Dy,), "out")
    g = graph(
        [cin, h, out],
        [Edge(cin, h), Edge(h, out)],
        TaskMap(; x=cin, y=out),
        InferenceSGD(; eta_infer=0.1, infer_steps=15)
    )
    g, initialize_params(g, MersenneTwister(7))
end
train_net!(g, p, X, Tgt; epochs=30) = first(
    train_pcn(
        p,
        g,
        [Dict("x" => X, "y" => Tgt)],
        AdamW(p; lr=0.02);
        num_epochs=epochs,
        rng=MersenneTwister(7),
        verbose=false
    )
)
predict_net(g, p, X) = predict(p, g, Dict("x" => X), MersenneTwister(7); output_task="y")

# ---------------- symbolic half: FactorVSA associative rule memory ----------------
cw(V, s) = HV{BipolarMAP}(V.atoms[:, s])
# DIRECTED transition memory: a permutation role ρ breaks bind-commutativity, so a bound pair
# encodes the ORDERED edge c→n (else querying v(s) retrieves BOTH successor and predecessor).
function learn_vsa_rule(estS, seqid, V)        # T = ⊕ ρ(v(c)) ⊗ v(n) over within-sequence transitions
    bs = HV{BipolarMAP}[]
    for r in 2:length(estS)
        seqid[r] == seqid[r - 1] &&
            push!(bs, bind(permute(cw(V, estS[r - 1])), cw(V, estS[r])))
    end
    isempty(bs) ? cw(V, 1) : bundle(bs...)
end
vsa_next(T, V, s) = argmax(V.atoms' * bind(permute(cw(V, s)), T).data)   # cleanup(ρ(v(s)) ⊗ T)
function vsa_track(T, V, seed, Tt)
    o = zeros(Int, Tt)
    s = seed
    for t in 1:Tt
        o[t] = s
        s = vsa_next(T, V, s)
    end
    o
end
function heldout_acc(T, V, K, δ; Ttest=30, testseeds=1:K)
    accs = Float64[]
    for sd in testseeds
        truth = Int[]
        s = sd
        for _ in 1:Ttest
            push!(truth, s)
            s = nextsym(s, δ, K)
        end
        push!(accs, mean(vsa_track(T, V, sd, Ttest) .== truth))
    end
    mean(accs)
end

function run(;
    K=5,
    Dy=10,
    N=512,
    T=14,
    nseq=12,
    δ=1,
    φscale=2.0f0,
    noise=0.1f0,
    rounds=4,
    epochs=25,
    seed=0
)
    rng = MersenneTwister(seed)
    proto = randn(rng, Float32, K, Dy)
    ddir = randn(rng, Float32, Dy)
    ddir ./= sqrt(sum(ddir .^ 2))
    φ = φscale .* randn(rng, Float32, K)
    V = random_codebook(BipolarMAP, N, K; rng=MersenneTwister(seed + 1))
    d = make_data(rng; nseq, T, K, Dy, δ, φscale, noise, proto, ddir, φ)

    rawS = clean_proto(proto, d.Y)                               # symbolic-only: VSA on drift-corrupted tokens
    W_sym = learn_vsa_rule(rawS, d.seqid, V)

    g, p = build_net(K, Dy)
    W_cpl = W_sym                       # coupled: bridge bootstrap
    for _ in 1:rounds
        track = vcat([vsa_track(W_cpl, V, d.seeds[b], T) for b in 1:nseq]...)
        F = histfeat(track, d.seqid, K)
        resid = d.Y .- proto_rows(proto, track)
        p = train_net!(g, p, F, resid; epochs)                  # neural learns drift(history)
        estS = clean_proto(proto, d.Y .- predict_net(g, p, F))  # de-drift → re-cleanup
        W_cpl = learn_vsa_rule(estS, d.seqid, V)
    end

    gp, pp = build_net(1, Dy)
    Xp = posfeat(d.seqid, T)         # parallel: rule-blind de-drift, VSA once
    pp = train_net!(gp, pp, Xp, d.Y; epochs)
    parS = clean_proto(proto, d.Y .- predict_net(gp, pp, Xp))
    W_par = learn_vsa_rule(parS, d.seqid, V)

    acc(W) = heldout_acc(W, V, K, δ)
    cpl, sym_, par = acc(W_cpl), acc(W_sym), acc(W_par)
    neu = 1.0 / K
    (; S1=cpl > sym_ + 0.1 && cpl > neu + 0.1, S2=cpl > par + 0.1, cpl, sym_, neu, par)
end

println("AC8 Phase-2b-VSA — FabricPC PC ↔ FactorVSA rule memory (path-integral drift)")
# SHORT sequences (T<K): symbol histories are seed-specific ⇒ drift is NOT position-predictable,
# so parallel's rule-blind positional de-drift should FAIL and only the history-aware bridge wins.
println(
    "T<K (short, seed-specific histories) — drift sweep × 6 seeds (S1=coupled≫singles; S2=bridge≫no-bridge):"
)
const NSEED = 6
for φs in (2.0f0, 3.0f0, 4.0f0)
    s1 = 0
    s2 = 0
    cs = Float64[]
    ss = Float64[]
    ps = Float64[]
    for sd in 0:(NSEED - 1)
        r = run(; K=8, T=6, nseq=16, φscale=φs, seed=sd, rounds=6, epochs=35)
        s1 += r.S1
        s2 += r.S2
        push!(cs, r.cpl)
        push!(ss, r.sym_)
        push!(ps, r.par)
    end
    @printf("  φscale=%.1f | acc coupled=%.2f sym=%.2f par=%.2f | S1 %d/%d  S2 %d/%d\n",
        φs, mean(cs), mean(ss), mean(ps), s1, NSEED, s2, NSEED)
end

# ─────────────────────────────────────────────────────────────────────────────────────────
# RESULT (2026-06-10) — VSA PIVOT WORKED; S1 weak/non-robust; S2 HONEST NEGATIVE.
# The FactorVSA substrate made the bootstrap fast + debuggable (vs the 6s/call MeTTa soup in
# ac8_phase2b_real.jl). It also exposed a real VSA bug: BipolarMAP bind is COMMUTATIVE, so a
# bound pair v(c)⊗v(n) is an UNDIRECTED edge — querying v(s) returned BOTH successor AND
# predecessor (all conditions ≈ chance). Fix: a permutation ROLE  T=⊕ρ(v(c))⊗v(n), query
# ρ(v(s))⊗T  (directed). Clean-data recovery then exact.
#
# With a working rule learner, across drift scales × 6 seeds, and across TWO task variants
# (T>K long, and T<K short/seed-specific histories):
#   S1 (coupled ≫ both singles): WEAK + non-robust (best ~3/6 at scale 3; symbolic competitive
#       elsewhere). The drift corrupts symbolic only in a narrow band.
#   S2 (coupled ≫ parallel-uncoupled): FAILS. The rule-blind POSITIONAL de-drift (parallel)
#       stays competitive with or beats the bridge (coupled) at essentially every scale/variant.
#       Root cause: the drift remains de-driftable WITHOUT the rule — a positional/global proxy
#       captures enough of it, so the error-EXCHANGE adds no value over running both halves once.
#       Making histories seed-specific (T<K) did NOT fix it.
#
# CONCLUSION (honest negative, NOT p-hacked): cognitive synergy in the strong S2 sense (the
# bridge beats ensembling) is NOT established on this rule-induction-under-drift family, despite
# multiple principled task variants. S2 demands a channel that is genuinely UN-de-driftable
# without the discrete rule — a property this task family does not robustly provide. The bridge
# MECHANISM works (AC8 Phase-0/1), and an idealized JOINT inference shows S1 (pure-Julia
# ac8_phase2b_nonlinear), but the *capability* synergy that beats a strong independent baseline
# remains an open task-design problem. Recorded rather than engineered into a false positive.
# ─────────────────────────────────────────────────────────────────────────────────────────
