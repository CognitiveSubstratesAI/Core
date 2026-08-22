# AC8 Phase-2 — synergy gate S1/S2/S3 (pure-Julia mechanism validation; spec §4, §6).
# Spec: ../../docs/actpc/AC8_synergy_gate.md. Step 1 (ac8_phase2_task.jl) PROVED the task is
# non-vacuous. This builds the four conditions and evaluates the capability gate.
#
# FAITHFUL FORMULATION (the key design realization): in the pure no-wrap regime the confound is
# EXACT even for the coupled system — there is no information to separate rule-step δ from
# drift-rate b. The disambiguating signal is the mod-K WRAP, which must be PRESENT in training.
# The synergy is that only JOINT inference over (δ,b) can exploit the wrap; each CONSTRAINED
# single half cannot:
#   coupled        = joint argmin over (δ,b)        — the bridge's de-drift↔induce realizes this
#   symbolic-alone = argmin over δ with b=0         — drift-blind (can't subtract the ramp)
#   neural-alone   = argmin over b with δ=0         — rule-blind (no discrete rule to roll out)
#   parallel-uncpl = neural picks b (δ=0), THEN symbolic picks δ given that b — one-shot, no bridge
# Disambiguator = reconstruction residual on training that INCLUDES wraps. Capability metric =
# held-out track accuracy (roll out ŝ_t=(s0+(t-1)δ̂) mod K from the seed) on UNSEEN seeds +
# extrapolation horizon. (The grid search is the joint-inference IDEAL the PC bridge approximates;
# the FabricPC + real-soup realization is the next, heavier leg.)
using LinearAlgebra, Statistics, Printf, Random

const K = 50          # symbol alphabet
const D = 16          # observation dim

make_u(seed) = (rng=MersenneTwister(seed); u=randn(rng, D); u ./ norm(u))
rule_track(s0, δ, T) = Int[mod(s0 + (i - 1) * δ, K) for i in 1:T]
function observe(u, s0, δ, b, T; noise=0.0, seed=1)
    rng = MersenneTwister(seed)
    s = rule_track(s0, δ, T)
    Y = zeros(T, D)
    for i in 1:T
        Y[i, :] = s[i] .* u .+ b * (i - 1) .* u .+ noise .* randn(rng, D)
    end
    return Y, s
end
xproj(u, Y) = Y * u

# reconstruction residual of hypothesis (δ,b) over training seqs [(s0, x=⟨y,u⟩), …]
function recon_resid(seqs, δ, b)
    r = 0.0
    n = 0
    for (s0, x) in seqs
        for i in eachindex(x)
            x̂ = mod(s0 + (i - 1) * δ, K) + b * (i - 1)     # rule part wraps (mod K); drift does not
            r += (x[i] - x̂)^2
            n += 1
        end
    end
    return r / n
end

# inference conditions → each returns (δ̂, b̂)
const ΔG = 1:6
const BG = 0:6
argmin2(f, As, Bs) = (best=(first(As), first(Bs)); bv=Inf;
    for a in As, b in Bs
        v = f(a, b)
        v < bv && (bv=v; best=(a, b))
    end; best)

coupled(seqs) = argmin2((δ, b) -> recon_resid(seqs, δ, b), ΔG, BG)              # joint
symbolic(seqs) = (argmin2((δ, b) -> recon_resid(seqs, δ, 0), ΔG, 0:0)[1], 0)     # b=0
neural(seqs) = (0, argmin2((δ, b) -> recon_resid(seqs, 0, b), 0:0, BG)[2])     # δ=0
function parallel_uncoupled(seqs)                                                  # neural→symbolic, 1-shot
    b̂ = neural(seqs)[2]
    δ̂ = argmin2((δ, b) -> recon_resid(seqs, δ, b̂), ΔG, b̂:b̂)[1]
    return (δ̂, b̂)
end

# capability: roll out the induced rule from each seed; fraction of symbols correct
function track_acc(testtruth, δ̂)
    accs = Float64[]
    for (s0, strue) in testtruth
        ŝ = rule_track(s0, δ̂, length(strue))
        push!(accs, mean(ŝ .== strue))
    end
    return mean(accs)
end

function run(; δ0=1, b0=2, Ttrain=30, Ttest=60, noise=0.2)
    u = make_u(0)
    train_seeds = collect(0:7:49)          # mix: low seeds (no wrap, confounded) + high (wrap in Ttrain)
    test_seeds = [3, 11, 25, 38, 45]      # UNSEEN
    wraps(s0, T) = count(i -> rule_track(s0, δ0, T)[i] < rule_track(s0, δ0, T)[i - 1], 2:T)

    trainseqs = [
        (s0, xproj(u, observe(u, s0, δ0, b0, Ttrain; noise=noise, seed=100 + s0)[1])) for
        s0 in train_seeds
    ]
    testtruth = [(s0, rule_track(s0, δ0, Ttest)) for s0 in test_seeds]
    # confound subset = test seeds whose first wrap is LATE (hardest: long confounded window)
    conf_subset = [(s0, t) for (s0, t) in testtruth if wraps(s0, Ttrain) == 0]

    @printf(
        "AC8 Phase-2 synergy gate — S1/S2/S3 (truth δ0=%d, b0=%d, K=%d, noise=%.2f)\n",
        δ0,
        b0,
        K,
        noise
    )
    @printf(
        "  train seeds %s (wraps in Ttrain=%d: %s)\n",
        train_seeds',
        Ttrain,
        [wraps(s, Ttrain) for s in train_seeds]'
    )
    @printf(
        "  test  seeds %s (UNSEEN), Ttest=%d ; confound subset (no train-wrap) = %s\n\n",
        test_seeds', Ttest, [s for (s, _) in conf_subset]')

    conds = Dict{String, Tuple{Int, Int}}()
    for (name, f) in (("coupled (joint δ,b)", coupled), ("symbolic-only (b=0)", symbolic),
        ("neural-only (δ=0)", neural), ("parallel-uncoupled", parallel_uncoupled))
        conds[name] = f(trainseqs)
    end

    @printf(
        "%-24s  %-10s  %-10s  %-12s\n", "condition", "(δ̂, b̂)", "test-acc", "confound-acc"
    )
    accs = Dict{String, Float64}()
    caccs = Dict{String, Float64}()
    for name in (
        "coupled (joint δ,b)",
        "symbolic-only (b=0)",
        "neural-only (δ=0)",
        "parallel-uncoupled"
    )
        δ̂, b̂ = conds[name]
        a = track_acc(testtruth, δ̂)
        ca = track_acc(conf_subset, δ̂)
        accs[name] = a
        caccs[name] = ca
        @printf("%-24s  (%d, %d)      %-10.3f  %-12.3f\n", name, δ̂, b̂, a, ca)
    end

    cpl = accs["coupled (joint δ,b)"]
    ccpl = caccs["coupled (joint δ,b)"]
    sym = accs["symbolic-only (b=0)"]
    neu = accs["neural-only (δ=0)"]
    par = accs["parallel-uncoupled"]
    csym = caccs["symbolic-only (b=0)"]
    cneu = caccs["neural-only (δ=0)"]
    S1 = cpl > sym + 0.1 && cpl > neu + 0.1
    S2 = cpl > par + 0.1
    S3 = ccpl > max(csym, cneu) + 0.3
    @printf("\n=== SYNERGY GATE ===\n")
    @printf(
        "  S1  coupled beats BOTH single halves (held-out) ......... %s  (%.2f vs sym %.2f / neu %.2f)\n",
        S1,
        cpl,
        sym,
        neu
    )
    @printf(
        "  S2  coupled beats parallel-but-uncoupled (bridge=value) . %s  (%.2f vs %.2f)\n",
        S2,
        cpl,
        par
    )
    @printf(
        "  S3  coupled ≫ singles on the confound subset ............ %s  (%.2f vs sym %.2f / neu %.2f)\n",
        S3,
        ccpl,
        csym,
        cneu
    )
    @printf("  >>> COGNITIVE SYNERGY (mechanism, pure-Julia): %s\n", S1 && S2 && S3)
    return S1 && S2 && S3
end

run()

# ─────────────────────────────────────────────────────────────────────────────────────────
# RESULT (2026-06-10) — HONEST NEGATIVE. The gate FAILS on this (linear-drift) task:
#   coupled (1,2) acc 1.00 | symbolic-only (1,0) acc 1.00 | neural-only (0,2) acc 0.03 |
#   parallel-uncoupled (1,2) acc 1.00   ⇒ S1=S2=false (only neural-alone fails).
#
# ROOT CAUSE: a LINEAR drift makes the disambiguating mod-K wrap TOO accessible. The
# drift-blind symbolic search (b=0) still recovers δ=1, because mis-locating a wrap costs
# ≈K² in residual — one sharp signal that dominates the unexplained linear ramp. So a
# CONSTRAINED single half nails the rule WITHOUT the bridge, and parallel-uncoupled also
# succeeds (neural's b̂ is coincidentally right). The task is too linear to ISOLATE synergy;
# the synergy regime is a knife-edge (tuning wrap-vs-confound weight), which would violate
# the gate's robustness spirit. NOT tuned to a fake pass (discipline: honest negative).
#
# IMPLICATION (drives the next leg): robust synergy needs a drift the single halves CANNOT
# marginalize — i.e. NONLINEAR / stochastic drift (a random-walk or context-nonlinear channel)
# that defeats any constrained global fit, yet that a real NEURAL net CAN regress GIVEN the
# rule's proto-baseline predictions. That genuinely requires the FabricPC neural half (a grid
# search cannot represent a flexible drift) + the real ActPC-Chem soup. So step-2b = richer
# (nonlinear-drift) task + FabricPC + soup. This pure-Julia harness has served its purpose:
# it falsified the simplest task design BEFORE the expensive build. See AC8_synergy_gate.md.
# ─────────────────────────────────────────────────────────────────────────────────────────
