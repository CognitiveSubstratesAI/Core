# AC8 PHASE 1 — the REAL bridge: FabricPC (Julia PC) ↔ Core/lib/ActPC-Chem (MeTTa soup).
# Same task + gate as Phase 0, but the symbolic half is now the ACTUAL ChemRule soup
# (run via MeTTaCore: chem-step! learning = AC1/AC3, weights = AC1, prediction by the
# highest-weight matching rule). The bridge drives the real soup with neural-de-drifted
# transitions; the soup's predictions anchor the neural drift. Re-run G1/G2.
using MeTTaCore, FabricPC, Enzyme, Random, LinearAlgebra, Statistics, Printf
register_core_primitives!()

# ---------- task (proto[s] + α·c·drift; cyclic successor; seed observed) ----------
function make_data(rng; nseq=20, T=6, K=4, Dy=8, alpha=2.0f0)
    proto = randn(rng, Float32, K, Dy) .* 1.0f0
    drift = randn(rng, Float32, Dy)
    drift ./= sqrt(sum(drift .^ 2))
    nsamp = nseq * T
    C = zeros(Float32, nsamp, 1)
    Y = zeros(Float32, nsamp, Dy)
    S = zeros(Int, nsamp)
    seed = zeros(Int, nseq)
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
            s = (s % K) + 1
            r += 1
        end
    end
    (; proto, drift, C, Y, S, seed, nseq, T, K, Dy)
end
proto_rows(P, idx) = reduce(vcat, (transpose(@view P[idx[i], :]) for i in eachindex(idx)))
mse(A, B) = sum((A .- B) .^ 2) / size(A, 1)
cleanup(P, M) = [
    argmin([sum((@view(P[k, :]) .- @view(M[i, :])) .^ 2) for k in 1:size(P, 1)]) for
    i in 1:size(M, 1)
]

# ---------- neural half (FabricPC PC net c → drift) ----------
function build_net(d; H=12)
    cin = Linear((1,), "c")
    h = Linear((H,), "h"; activation=TanhActivation())
    out = Linear((d.Dy,), "out")
    g = graph(
        [cin, h, out],
        [Edge(cin, h), Edge(h, out)],
        TaskMap(; x=cin, y=out),
        InferenceSGD(; eta_infer=0.1, infer_steps=20)
    )
    g, initialize_params(g, MersenneTwister(7))
end
train_net!(g, p, C, Tgt; epochs=40, lr=0.01) = first(
    train_pcn(
        p,
        g,
        [Dict("x"=>C, "y"=>Tgt)],
        AdamW(p; lr=lr);
        num_epochs=epochs,
        rng=MersenneTwister(7),
        verbose=false
    )
)
predict_net(g, p, C) = predict(p, g, Dict("x"=>C), MersenneTwister(7); output_task="y")

# ---------- the REAL ActPC-Chem soup (MeTTaCore) ----------
function fresh_soup()
    s = new_core_space()
    ef = e -> to_sexpr(eval_metta(from_sexpr(e), s))
    _register_atom_ops!(ef)
    load_stdlib!(s)
    run_metta("!(import! &self (library ActPC-Chem))", s)
    s
end
sym(i) = "s$i"
function seed_soup!(s, K; w0=1.0)         # seed ALL K² candidate transitions (correct + distractors)
    for i in 1:K, j in 1:K
        run_metta("!(add-atom &self (ChemRule $(sym(i)) $(sym(j)) $w0))", s)
    end
end
# Drive AC1/AC3 learning: reinforce observed (cur→nxt) transitions (ν=1 ⇒ correct grows, others flat).
function soup_learn!(s, transitions; reps=6)
    for _ in 1:reps, (cur, nxt) in transitions
        run_metta("!(chem-step! $(sym(cur)) $(sym(nxt)) 1.0)", s)
    end
end
# Read all rule weights into a Julia dict (pattern,rewrite)->weight (one MeTTa query).
function soup_weights(s, K)
    W = Dict{Tuple{Int, Int}, Float64}()
    for i in 1:K, j in 1:K
        r = run_metta("!(match &self (ChemRule $(sym(i)) $(sym(j)) \$w) \$w)", s)
        isempty(r) || (W[(i, j)] = Float64(r[1]))
    end
    W
end
soup_next(W, i, K) = argmax([get(W, (i, j), -Inf) for j in 1:K])   # highest-weight rule from i
# Predict the symbol track of a sequence from its seed via the learned soup.
function soup_track(W, seed, T, K)
    out = zeros(Int, length(seed)*T)
    r = 1
    for b in eachindex(seed)
        s = seed[b]
        for t in 1:T
            out[r] = s
            s = soup_next(W, s, K)
            r += 1
        end
    end
    out
end

function run_phase1(; seed=0)
    rng = MersenneTwister(seed)
    d = make_data(rng)
    soup = fresh_soup()
    seed_soup!(soup, d.K)

    # (A) neural-only
    g, pN = build_net(d)
    pN = train_net!(g, pN, d.C, d.Y)
    J_neural = mse(predict_net(g, pN, d.C), d.Y)

    # (C) COUPLED: rounds of [neural de-drift → cleanup → transitions → soup learns →
    #     soup predicts track → neural trains on residual]. The bridge drives the REAL soup.
    gC, pC = build_net(d)
    drift = zeros(Float32, size(d.Y))
    Jtraj = Float32[]
    local track = d.S
    for round in 1:6
        ŝ = cleanup(d.proto, d.Y .- drift)                 # de-drifted symbol estimates
        trans = Tuple{Int, Int}[]                            # observed transitions per sequence
        r = 1
        for b in 1:d.nseq, t in 1:(d.T - 1)
            push!(trans, (ŝ[r + t - 1], ŝ[r + t]))
            r += (t==d.T-1 ? d.T : 0)
        end
        soup_learn!(soup, unique(trans); reps=4)            # REAL AC1/AC3 learning
        W = soup_weights(soup, d.K)
        track = soup_track(W, d.seed, d.T, d.K)             # soup prediction (learned rule)
        protoŝ = proto_rows(d.proto, track)
        pC = train_net!(gC, pC, d.C, d.Y .- protoŝ; epochs=30)
        drift = predict_net(gC, pC, d.C)
        push!(Jtraj, mse(protoŝ .+ drift, d.Y))
    end
    J_coupled = minimum(Jtraj)

    # (B) symbolic-only: soup track (learned) but NO drift
    Wfin = soup_weights(soup, d.K)
    track_s = soup_track(Wfin, d.seed, d.T, d.K)
    J_symbolic = mse(proto_rows(d.proto, track_s), d.Y)
    soup_track_acc = mean(track .== d.S)
    # show the soup learned the cyclic rule: correct (i→succ) weight vs mean distractor
    w_correct = mean(get(Wfin, (i, (i%d.K)+1), 0.0) for i in 1:d.K)
    w_distract = mean(get(Wfin, (i, j), 0.0) for i in 1:d.K, j in 1:d.K if j != (i%d.K)+1)
    (; J_neural, J_symbolic, J_coupled, Jtraj, soup_track_acc, w_correct, w_distract)
end

open("/tmp/jlmark", "w") do io
    for sd in 0:2
        r = run_phase1(; seed=sd)
        mono = all(r.Jtraj[2:end] .<= r.Jtraj[1:(end - 1)] .+ 1.0f-2)
        @printf(io,
            "seed %d: J_n=%.3f J_s=%.3f J_coupled=%.3f | G1mono=%s G2=%s | soup-track-acc=%.3f | w_correct=%.2f w_distract=%.2f\n",
            sd, r.J_neural, r.J_symbolic, r.J_coupled, mono,
            (r.J_coupled < r.J_neural && r.J_coupled < r.J_symbolic), r.soup_track_acc,
            r.w_correct, r.w_distract)
    end
    println(io, ">>>PHASE1 DONE")
end
