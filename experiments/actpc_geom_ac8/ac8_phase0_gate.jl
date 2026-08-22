#!/usr/bin/env julia
# AC8 Phase-0 mechanism gate — VALIDATED PROTOTYPE (2026-06-09). See AC8_bridge_gate.md.
# Pure-Julia: FabricPC PC neural half + toy in-Julia rule soup + HDC (prototype) cleanup
# + the AC8 bridge (shared joint error). NO MeTTa interop (that is Phase 1).
# Run:  julia --project=/home/shivaji1012/code/CognitiveSubstratesAI/FabricPC/benchmark/jit \
#            /home/shivaji1012/PRIMUS/docs/specs/ac8_phase0_gate.jl
# RESULT (5 seeds): G1 (joint-error relaxation, monotone ~0.69→0.02) PASS; G2 (coupled
# ≪ neural-only AND symbolic-only; neither half alone solves it) PASS; bidirectional
# error flow shown — symbolic→neural (G1 relaxation) + neural→symbolic (cleanup symbol
# acc 0.85→1.0 once de-drifted). Mechanism validated → Phase 1 = real FabricPC↔Core(MeTTa).
# AC8 Phase-0 pure-Julia mechanism gate (docs/specs/AC8_bridge_gate.md §4).
# Task: y[t] = proto[s[t]] + α·c[t]·drift  (discrete rule-governed prototype + continuous drift).
#   - neural half sees only c  → can't recover the discrete prototype
#   - symbolic half sees only the symbol structure → can't recover the drift
#   - recovering s needs de-drifting; learning drift needs de-prototyping → coupled relaxation
# HDC interlingua = prototype embeddings + nearest-neighbour cleanup.
# Gate: G1 joint error relaxes; G2 coupled < neural-only AND < symbolic-only.
using FabricPC, Random, LinearAlgebra, Statistics, Printf
const FP = FabricPC

# ---------------- data ----------------
function make_data(rng; nseq=24, T=6, K=4, Dy=8, alpha=4.0f0)
    proto = randn(rng, Float32, K, Dy) .* 1.0f0          # K prototype vectors (the "symbols")
    drift = randn(rng, Float32, Dy)
    drift ./= sqrt(sum(drift .^ 2))   # unit drift direction
    nsamp = nseq * T
    C = zeros(Float32, nsamp, 1)        # continuous context c[t] = t/T  (per step)
    Y = zeros(Float32, nsamp, Dy)       # target
    S = zeros(Int, nsamp)               # hidden true symbol
    seed = zeros(Int, nseq)             # observed seed symbol s[1] per sequence
    r = 1
    for b in 1:nseq
        s = rand(rng, 1:K)
        seed[b] = s
        for t in 1:T
            c = Float32(t) / T
            C[r, 1] = c
            S[r] = s
            Y[r, :] =
                proto[s, :] .+ alpha .* c .* drift .+ 0.05f0 .* randn(rng, Float32, Dy)
            s = (s % K) + 1                              # cyclic successor rule
            r += 1
        end
    end
    return (; proto, drift, C, Y, S, seed, nseq, T, K, Dy, alpha)
end

# Symbolic inference WITHOUT the seed: the soup knows the cyclic rule + prototypes,
# but must infer each sequence's PHASE φ (start symbol) by matching the rule's
# prototype-sequence to the (optionally de-drifted) targets over the WHOLE sequence.
# This is the symbolic half's job; de-drifting (from the neural half) de-corrupts it.
function infer_symbols(d, R)            # R = (de-drifted) targets (nsamp, Dy)
    ŝ = zeros(Int, size(R, 1))
    r = 1
    for b in 1:d.nseq
        rows = r:(r + d.T - 1)
        bestφ = 1
        bd = Inf32
        for φ in 1:d.K
            tot = 0.0f0
            for (ti, row) in enumerate(rows)
                s = ((φ - 1 + ti - 1) % d.K) + 1
                tot += sum((@view(R[row, :]) .- @view(d.proto[s, :])) .^ 2)
            end
            tot < bd && (bd=tot; bestφ=φ)
        end
        for (ti, row) in enumerate(rows)
            ŝ[row] = ((bestφ - 1 + ti - 1) % d.K) + 1
        end
        r += d.T
    end
    ŝ
end

# HDC cleanup: nearest prototype to each row of M  → symbol indices
function cleanup(proto, M)
    n = size(M, 1)
    out = zeros(Int, n)
    for i in 1:n
        best = 1
        bd = Inf32
        for k in 1:size(proto, 1)
            dist = sum((@view(proto[k, :]) .- @view(M[i, :])) .^ 2)
            dist < bd && (bd=dist; best=k)
        end
        out[i] = best
    end
    out
end

proto_rows(proto, idx) =
    reduce(vcat, (transpose(@view proto[idx[i], :]) for i in eachindex(idx)))  # (n,Dy)
mse(A, B) = sum((A .- B) .^ 2) / size(A, 1)

# ---------------- neural half: FabricPC PC net  c → Dy-vector (the drift) ----------------
function build_net(d; H=12, infer=20)
    cin = Linear((1,), "c")
    h = Linear((H,), "h"; activation=TanhActivation())
    out = Linear((d.Dy,), "out")
    g = graph([cin, h, out], [Edge(cin, h), Edge(h, out)],
        TaskMap(; x=cin, y=out), InferenceSGD(; eta_infer=0.1, infer_steps=infer))
    g, initialize_params(g, MersenneTwister(7))
end
train_net!(g, p, C, Tgt; epochs=60, lr=0.02) =
    first(
        train_pcn(p, g, [Dict("x"=>C, "y"=>Tgt)], AdamW(p; lr=lr);
            num_epochs=epochs, rng=MersenneTwister(7), verbose=false)
    )
predict_net(g, p, C) = predict(p, g, Dict("x"=>C), MersenneTwister(7); output_task="y")

# ---------------- the three systems ----------------
function run_gate(; seed=0)
    rng = MersenneTwister(seed)
    d = make_data(rng)

    # (A) NEURAL-ONLY: predict full y from c (no symbol info) → drift + blurred prototype
    g, pN = build_net(d)
    pN = train_net!(g, pN, d.C, d.Y)
    J_neural = mse(predict_net(g, pN, d.C), d.Y)

    # (B) SYMBOLIC-ONLY: infer phase from RAW (drift-corrupted) targets → proto[ŝ], no drift
    ŝ_sym = infer_symbols(d, d.Y)
    J_symbolic = mse(proto_rows(d.proto, ŝ_sym), d.Y)

    # (C) COUPLED (AC8): EM relaxation across the bridge — the chicken-and-egg.
    #   E (symbolic): infer ŝ from the DE-DRIFTED target (neural→symbolic error flow).
    #   M (neural):   train the drift on the residual y − proto[ŝ] (symbolic→neural error flow).
    #   Neither converges alone; the joint error J = ‖y − (proto[ŝ] + drift)‖² relaxes.
    gC, pC = build_net(d)
    drift_pred = zeros(Float32, size(d.Y))
    Ĵtraj = Float32[]
    local ŝ = infer_symbols(d, d.Y)
    for em in 1:8
        ŝ = infer_symbols(d, d.Y .- drift_pred)          # E: de-drifted phase inference
        protoŝ = proto_rows(d.proto, ŝ)
        pC = train_net!(gC, pC, d.C, d.Y .- protoŝ; epochs=40, lr=0.01)   # M: learn drift
        drift_pred = predict_net(gC, pC, d.C)
        push!(Ĵtraj, mse(protoŝ .+ drift_pred, d.Y))
    end
    J_coupled = minimum(Ĵtraj)                            # converged value (robust to a late wobble)

    # Smoking gun for the neural→symbolic error flow: when the symbolic half relies on
    # CLEANUP (per-step nearest-prototype, no rule), the neural de-drift is what makes
    # symbol recovery possible — cleanup on raw (drift-corrupted) targets vs on de-drifted.
    perstep_uncoupled = mean(cleanup(d.proto, d.Y) .== d.S)
    perstep_coupled = mean(cleanup(d.proto, d.Y .- drift_pred) .== d.S)

    return (; J_neural, J_symbolic, J_coupled, Ĵtraj,
        sym_acc_uncoupled=mean(ŝ_sym .== d.S),       # rule-based phase, WITHOUT de-drift
        sym_acc_coupled=mean(ŝ .== d.S),           # rule-based phase, WITH de-drift
        perstep_uncoupled, perstep_coupled)
end

open("/tmp/jlmark", "w") do io
    g1pass = g2pass = nsflow = true
    for sd in 0:4
        r = run_gate(; seed=sd)
        mono = all(r.Ĵtraj[2:end] .<= r.Ĵtraj[1:(end - 1)] .+ 1.0f-3)   # monotone (small tol)
        g1 = (r.Ĵtraj[1] - r.J_coupled) > 0.1f0 && mono             # relaxed substantially + monotone
        g2 = r.J_coupled < r.J_neural && r.J_coupled < r.J_symbolic
        ns = r.perstep_coupled > r.perstep_uncoupled                # neural→symbolic helped
        g1pass &= g1
        g2pass &= g2
        nsflow &= ns
        @printf(io,
            "seed %d: J_n=%.3f J_s=%.3f J_coupled=%.3f | G1(relax+mono)=%s G2=%s | cleanup-acc %.3f→%.3f\n",
            sd, r.J_neural, r.J_symbolic, r.J_coupled, g1, g2, r.perstep_uncoupled,
            r.perstep_coupled)
    end
    @printf(
        io, "ALL SEEDS: G1=%s  G2=%s  neural→symbolic-flow=%s\n", g1pass, g2pass, nsflow
    )
    println(io, ">>>AC8 GATE DONE")
end
