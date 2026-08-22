# AC8 Phase-2b-REAL — synergy gate S1/S2 with the REAL substrates: FabricPC PC neural half
# (Linear nodes ⇒ autodiff-free, no Enzyme) ↔ the REAL Core/lib/ActPC-Chem MeTTa soup.
# Spec ../../docs/actpc/AC8_synergy_gate.md §9. The pure-Julia harness (ac8_phase2b_nonlinear)
# showed S1 holds for path-integral drift but could NOT settle S2, because a grid/lstsq stand-in
# gives every condition too much power. Here the substrates are MODALITY-LIMITED by construction:
#   neural = continuous PC regression only (FabricPC);  symbolic = discrete ChemRule soup (MeTTa).
# The bridge is the only path that lets continuous precision inform discrete rule learning.
#
# Task (path-integral drift): y_t = proto[s_t] + z_t·ddir + noise, z_t = Σ_{τ<t} φ(s_τ); cyclic
# rule s→((s-1+δ) mod K)+1. The drift is the accumulation of a per-symbol increment ⇒ removing it
# REQUIRES the symbol track (the rule); reading the symbols REQUIRES the drift removed. Chicken-egg.
#
# Conditions → each yields a learned rule (soup transition weights); capability = held-out track
# accuracy (roll out the soup's max-weight rule from UNSEEN seeds over an extrapolation horizon):
#   coupled        = bridge bootstrap: soup rule ⇄ neural de-drift (neural input = rule-derived
#                    history features F; target = y − proto[predicted track]). Error EXCHANGE.
#   symbolic-only  = soup learns from RAW (drift-corrupted) cleanup. No neural.
#   neural-only    = continuous regression, no rule ⇒ cannot roll out a track (chance).
#   parallel-uncpl = neural de-drifts RULE-BLIND (regress y on position t only) → soup learns ONCE.
#                    Same substrates + compute as coupled, but NO bridge exchange. The S2 control.
using MeTTaCore, FabricPC, Random, LinearAlgebra, Statistics, Printf
register_core_primitives!()

# ---------------- task ----------------
nextsym(s, δ, K) = mod(s - 1 + δ, K) + 1
function make_data(rng; nseq, T, K, Dy, δ=1, φscale=2.5f0, noise=0.1f0, proto, ddir, φ)
    nsamp = nseq * T
    Y = zeros(Float32, nsamp, Dy)
    S = zeros(Int, nsamp)
    seqid = zeros(Int, nsamp)
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
cleanup(P, M) = [
    argmin([sum((@view(P[k, :]) .- @view(M[i, :])) .^ 2) for k in 1:size(P, 1)]) for
    i in 1:size(M, 1)
]
# cumulative-count history feature per sequence (resets each sequence); F[r,k] = #symbol k before t
function histfeat(track, seqid, K)
    n = length(track)
    F = zeros(Float32, n, K)
    for r in 1:n
        if r > 1 && seqid[r] == seqid[r - 1]
            F[r, :] = F[r - 1, :]
            F[r, track[r - 1]] += 1
        end
    end
    F
end
posfeat(seqid, T) =
    (n=length(seqid); reshape(Float32[(((r-1) % T) + 1) / T for r in 1:n], n, 1))

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
train_net!(g, p, X, Tgt; epochs=30, lr=0.02) = first(
    train_pcn(
        p,
        g,
        [Dict("x" => X, "y" => Tgt)],
        AdamW(p; lr=lr);
        num_epochs=epochs,
        rng=MersenneTwister(7),
        verbose=false
    )
)
predict_net(g, p, X) = predict(p, g, Dict("x" => X), MersenneTwister(7); output_task="y")

# ---------------- real ActPC-Chem soup (MeTTaCore) ----------------
sym(i) = "s$i"
function fresh_soup()
    s = new_core_space()
    ef = e -> to_sexpr(eval_metta(from_sexpr(e), s))
    _register_atom_ops!(ef)
    load_stdlib!(s)
    run_metta("!(import! &self (library ActPC-Chem))", s)
    s
end
function seed_soup!(s, K; w0=1.0)
    for i in 1:K, j in 1:K
        run_metta("!(add-atom &self (ChemRule $(sym(i)) $(sym(j)) $w0))", s)
    end
end
soup_learn!(s, transitions; reps=4) =
    for _ in 1:reps, (c, n) in transitions
        run_metta("!(chem-step! $(sym(c)) $(sym(n)) 1.0)", s)
    end
function soup_weights(s, K)
    W = Dict{Tuple{Int, Int}, Float64}()
    for i in 1:K, j in 1:K
        r = run_metta("!(match &self (ChemRule $(sym(i)) $(sym(j)) \$w) \$w)", s)
        isempty(r) || (W[(i, j)] = Float64(r[1]))
    end
    W
end
soup_next(W, i, K) = argmax([get(W, (i, j), -Inf) for j in 1:K])
function soup_track(W, seed, T, K)
    out = zeros(Int, T)
    s = seed
    for t in 1:T
        out[t] = s
        s = soup_next(W, s, K)
    end
    out
end
# learn a rule from a symbol track estimate (transitions within each sequence).
# NOTE: the real MeTTa chem-step! is ~6s/call ⇒ keep reps and rule-set TINY.
const LOG = open("/tmp/ac8_real.out", "w")
plog(m) = (println(LOG, m); flush(LOG))
function learn_rule(estS, seqid, K; reps=3, soup=nothing)
    soup === nothing && (soup=fresh_soup(); seed_soup!(soup, K))
    trans = Tuple{Int, Int}[]
    for r in 2:length(estS)
        seqid[r] == seqid[r - 1] && push!(trans, (estS[r - 1], estS[r]))
    end
    soup_learn!(soup, unique(trans); reps=reps)
    soup_weights(soup, K)
end

# held-out capability: roll out the learned rule from UNSEEN seeds; fraction of symbols correct
function heldout_acc(W, K, δ; Ttest=30, testseeds=1:K)
    accs = Float64[]
    for sd in testseeds
        truth = [(
            s=sd;
            for _ in 2:t
                s = nextsym(s, δ, K)
            end;
            s
        ) for t in 1:Ttest]
        push!(accs, mean(soup_track(W, sd, Ttest, K) .== truth))
    end
    mean(accs)
end

function run(;
    K=4, Dy=8, T=10, nseq=6, δ=1, φscale=2.5f0, noise=0.1f0, rounds=2, seed=0, epochs=15
)
    rng = MersenneTwister(seed)
    proto = randn(rng, Float32, K, Dy)
    ddir = randn(rng, Float32, Dy)
    ddir ./= sqrt(sum(ddir .^ 2))
    φ = φscale .* randn(rng, Float32, K)
    d = make_data(
        rng; nseq=nseq, T=T, K=K, Dy=Dy, δ=δ, noise=noise, proto=proto, ddir=ddir, φ=φ
    )

    # ---- symbolic-only: soup from raw (drift-corrupted) cleanup ----
    rawS = cleanup(proto, d.Y)
    plog("  symbolic-only: learning rule from raw cleanup…")
    W_sym = learn_rule(rawS, d.seqid, K)

    # ---- coupled: bridge bootstrap (soup rule ⇄ neural de-drift via rule-derived features) ----
    g, p = build_net(K, Dy; H=8)
    estS = copy(rawS)
    W_cpl = W_sym
    coupled_soup = fresh_soup()
    seed_soup!(coupled_soup, K)
    for rnd in 1:rounds
        track = vcat([soup_track(W_cpl, d.seeds[b], T, K) for b in 1:nseq]...)   # rule prediction per seq
        F = histfeat(track, d.seqid, K)
        resid = d.Y .- proto_rows(proto, track)
        p = train_net!(g, p, F, resid; epochs=epochs)                          # neural learns drift(history)
        estS = cleanup(proto, d.Y .- predict_net(g, p, F))                       # de-drift → re-cleanup
        W_cpl = learn_rule(estS, d.seqid, K; soup=coupled_soup)                # REAL soup, persisted across rounds
        plog("  coupled round $rnd done")
    end

    # ---- parallel-uncoupled: neural de-drifts RULE-BLIND (input = position t), soup learns ONCE ----
    gp, pp = build_net(1, Dy; H=8)
    Xp = posfeat(d.seqid, T)
    pp = train_net!(gp, pp, Xp, d.Y; epochs=epochs)        # regress RAW y on position (no proto baseline)
    parS = cleanup(proto, d.Y .- predict_net(gp, pp, Xp))
    plog("  parallel: learning rule from rule-blind de-drift…")
    W_par = learn_rule(parS, d.seqid, K)

    acc(W) = heldout_acc(W, K, δ; testseeds=1:K)
    cpl, sym_, par = acc(W_cpl), acc(W_sym), acc(W_par)
    neu = 1.0 / K
    S1 = cpl > sym_ + 0.1 && cpl > neu + 0.1
    S2 = cpl > par + 0.1
    msg = @sprintf(
        "seed %d (φscale=%.1f): coupled=%.2f | symbolic=%.2f neural=%.2f parallel=%.2f | S1=%s S2=%s",
        seed, φscale, cpl, sym_, neu, par, S1, S2)
    plog(msg)
    println(msg)
    return (; S1, S2, cpl, sym_, neu, par)
end

plog(
    "AC8 Phase-2b-REAL — FabricPC PC ↔ real ActPC-Chem soup (path-integral drift) — MINIMAL run"
)
println(
    "AC8 Phase-2b-REAL — FabricPC PC ↔ real ActPC-Chem soup (path-integral drift) — MINIMAL run"
)
let r = run(; seed=0)
    v = @sprintf("\n=== SYNERGY GATE (real substrates, 1 seed) === S1=%s S2=%s", r.S1, r.S2)
    plog(v)
    println(v)
    plog("DONE")
end

# ─────────────────────────────────────────────────────────────────────────────────────────
# RESULT (2026-06-10) — SUPERSEDED by ac8_phase2b_vsa.jl. The real MeTTa-interpreted soup is
# ~6s per chem-step! (measured: steady-state, NOT JIT) ⇒ an iterative bootstrap × conditions ×
# seeds is ~1 hr — untunable. A minimal run (K=4, reps=1) collapsed all conditions to ≈chance
# because reps=1 left soup weights tied (argmax defaulted to symbol 1). Rather than fight the
# interpreter, the symbolic half was moved to the FAST subsymbolic VSA substrate (FactorVSA),
# which is also the HDC interlingua the AC8 spec specifies. See ac8_phase2b_vsa.jl. This file is
# kept as the record that the real soup WORKS but is too slow to serve as an iterative learner.
# ─────────────────────────────────────────────────────────────────────────────────────────
