# AC8 Phase-2 — task generator + the two PRE-BUILD vacuity proofs (synergy gate §5.1, §5.4).
# Spec: ../../docs/actpc/AC8_synergy_gate.md. Before ANY coupled run we must prove the task
# is non-vacuous, i.e.:
#   §5.4  the confound is REAL: on the confound subset, a WRONG (rule, drift) explains the
#         observation exactly as well as the truth — rule and channel are mutually
#         unidentifiable from a single half.
#   §5.1  the barrier is INFORMATION-theoretic, not capacity: because two DIFFERENT symbol
#         tracks produce IDENTICAL observations, NO map observation→symbol (any capacity)
#         can be correct on the confound family. Capacity cannot help.
# And we check the disambiguating information EXISTS (so the gate is feasible, not impossible):
#   over long horizons the discrete rule WRAPS (mod K) but the continuous drift does not, so
#   the joint sawtooth+ramp separates δ from b — recoverable only by using BOTH halves.
#
# Pure Julia (LinearAlgebra + Statistics) — the proofs are geometric/analytic, no neural deps.
# Construction: proto[s] = s·u (collinear along unit u ∈ R^D); drift = b·(t−1)·u (SAME u, the
# confound direction). Scalar observable x_t = ⟨y_t,u⟩ = (s0+(t−1)δ mod K) + b(t−1).
# No-wrap regime ⇒ x_t = s0 + (t−1)(δ+b): only the SUM δ+b is observable.
using LinearAlgebra, Statistics, Printf, Random

const K = 50          # symbol alphabet (large ⇒ a short-horizon no-wrap regime exists)
const D = 16          # observation dimension

make_u(seed) = (rng=MersenneTwister(seed); u=randn(rng, D); u ./ norm(u))
rule_track(s0, δ, T) = Int[mod(s0 + (i - 1) * δ, K) for i in 1:T]    # 0..K-1

# y_t = proto[s_t] + b·(t−1)·u + noise ; proto[s] = s·u (drift indexed from 0 ⇒ exact confound)
function observe(u, s0, δ, b, T; noise=0.0, seed=1)
    rng = MersenneTwister(seed)
    s = rule_track(s0, δ, T)
    Y = zeros(T, D)
    for i in 1:T
        Y[i, :] = s[i] .* u .+ b * (i - 1) .* u .+ noise .* randn(rng, D)
    end
    return Y, s
end
xproj(u, Y) = Y * u            # scalar observable x_t

# Confound family: (δ', b') = (δ+m, b−m) for integer m — all share δ+b ⇒ identical no-wrap obs.
twin(δ, b, m) = (δ + m, b - m)

function run()
    u = make_u(0)
    s0, δ, b = 0, 1, 2                       # ground truth: successor rule + drift rate 2
    Tshort, Tlong = 6, 60                    # Tshort: no wrap (max idx (Tshort-1)(δ+b)=15<50)

    @printf("AC8 Phase-2 task — pre-build vacuity proofs (spec §5.1, §5.4)\n")
    @printf("  ground truth: rule δ=%d, drift b=%d, s0=%d, K=%d, D=%d\n\n", δ, b, s0, K, D)

    # ── §5.4 CONFOUND IS REAL: enumerate twins (δ+m, b−m); noise-free obs must be IDENTICAL.
    @printf(
        "[§5.4] confound family (δ',b')=(δ+m,b−m), short horizon T=%d, noise=0:\n", Tshort
    )
    Ytrue, strue = observe(u, s0, δ, b, Tshort)
    confound_exact = true
    for m in (-1, 1, 2)                       # δ'∈{0?,2,3}; keep δ'≥1 and b'≥0 below
        δ2, b2 = twin(δ, b, m)
        (δ2 < 1 || b2 < 0) && continue
        Y2, s2 = observe(u, s0, δ2, b2, Tshort)
        gap = maximum(abs.(Ytrue .- Y2))     # max abs obs difference
        diff_track = s2 != strue             # but the SYMBOL TRACKS differ
        confound_exact &= (gap < 1e-10 && diff_track)
        @printf(
            "   m=%+d → (δ'=%d,b'=%d): obs-gap=%.2e  tracks-differ=%s  [true s=%s | twin s=%s]\n",
            m, δ2, b2, gap, diff_track, strue', s2')
    end

    # ── §5.1 INFORMATION BARRIER (capacity-independent): same obs ⇒ no map obs→symbol correct.
    δ2, b2 = twin(δ, b, 2)                    # (δ'=3, b'=0): a clean alternative reading
    _, sA = observe(u, s0, δ, b, Tshort)
    YB, sB = observe(u, s0, δ2, b2, Tshort)
    YA, _ = observe(u, s0, δ, b, Tshort)
    identical = maximum(abs.(YA .- YB)) < 1e-10
    barrier = identical && (sA != sB)
    @printf(
        "\n[§5.1] two DIFFERENT symbol tracks, IDENTICAL observations ⇒ capacity cannot help:\n"
    )
    @printf("   reading A: rule δ=%d,b=%d → symbols %s\n", δ, b, sA')
    @printf("   reading B: rule δ=%d,b=%d → symbols %s\n", δ2, b2, sB')
    @printf(
        "   obs(A)==obs(B): %s   ⇒  ANY f:obs→symbol is wrong on one reading.\n", identical
    )

    # ── A single SYMBOLIC half (naive cleanup, drift-blind) mis-induces the rule:
    x = xproj(u, Ytrue)                       # x_t = s0+(t−1)(δ+b)
    ŝ = round.(Int, x)                        # nearest-proto cleanup, ignoring drift
    δ̂ = round(Int, median(diff(ŝ)))          # induced step
    sym_wrong = (δ̂ != δ)
    @printf(
        "\n[neither-alone, symbolic] drift-blind cleanup induces δ̂=%d (truth δ=%d) → %s\n",
        δ̂, δ, sym_wrong ? "WRONG rule (=δ+b)" : "correct")

    # ── DISAMBIGUATION EXISTS (gate is feasible): long horizon, the rule WRAPS, drift does not.
    YtL, _ = observe(u, s0, δ, b, Tlong)
    YtwL, _ = observe(u, s0, δ2, b2, Tlong)
    sep = sqrt(mean((YtL .- YtwL) .^ 2))      # RMS obs separation over long horizon
    feasible = sep > 1.0
    nwrap_true = count(
        i -> rule_track(s0, δ, Tlong)[i] < rule_track(s0, δ, Tlong)[max(i - 1, 1)], 2:Tlong
    )
    @printf(
        "\n[feasible] long horizon T=%d: obs(A) vs obs(B) RMS-separation=%.3f (rule wraps %d×)\n",
        Tlong, sep, nwrap_true)
    @printf(
        "   ⇒ the joint sawtooth(rule)+ramp(drift) DISTINGUISHES δ from b — but only by\n"
    )
    @printf(
        "     using BOTH halves (de-drift to expose the wrap; wrap-period to fix the rule).\n"
    )

    pass = confound_exact && barrier && sym_wrong && feasible
    @printf("\n=== PRE-BUILD GATE ===\n")
    @printf(
        "  §5.4 confound exact (wrong rule+drift ≡ truth) ........ %s\n", confound_exact
    )
    @printf("  §5.1 barrier is informational (capacity-independent) .. %s\n", barrier)
    @printf("  neither-alone: symbolic half mis-induces the rule ..... %s\n", sym_wrong)
    @printf("  disambiguation INFO exists (gate feasible) ............ %s\n", feasible)
    @printf("  >>> TASK NON-VACUOUS (safe to build the coupled run): %s\n", pass)
    return pass
end

run()
