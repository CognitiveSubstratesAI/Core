;; lib/pln/decay.metta — belief confidence DYNAMICS (R10).
;;
;; A truth value is not static in a dynamic world: confidence decays with age, and when it falls below a
;; threshold the world model schedules re-validation. That makes the decay LAW a first-class piece of
;; reasoning policy — the shape of the curve (exponential vs hyperbolic vs stepped) and the rate λ are
;; exactly the things an evolutionary search over the agent's own cognition should be free to vary. So
;; they live here as atoms, not as a Julia expression.
;;
;; This file is the counterpart to `base_rate.metta`: that one derives a truth value from evidence COUNTS,
;; this one ages a truth value over TIME. Both build on `pln_core_logic.metta` and neither re-derives it.
;;
;; NO type declarations, deliberately (see base_rate.metta's header): a declared return type of `Atom`
;; makes the driver return the body LAZILY. Domain libs stay bare.
;;
;; PRIOR ART IN THIS TREE: ECAN already gets this right for ATTENTION — `(= (ecan-decay-factor) 0.05)`
;; in `../ecan/ECAN_Policies.metta` is a named, rewritable atom. Belief confidence had no equivalent; the
;; law lived only as `c0 * exp(-lambda * (t - t0))` in `WorldModel/src/Beliefs.jl` with `lambda = 0.1` as
;; a Julia keyword default, which is what this file replaces.

;; ── the decay rate ───────────────────────────────────────────────────────────────────────────────
;; λ = 0.1 per unit time: confidence halves in ≈6.93 ticks. Named so it can be retuned — or made
;; per-space, or made a function of evidence volatility — without touching the law.
(= (BeliefDecayRate) 0.1)

;; ── the law ──────────────────────────────────────────────────────────────────────────────────────
;; c(t) = c₀·exp(−λ(t−t₀))   (§6.1.3, R10)
;; λ is a PARAMETER rather than baked in, so a caller can decay two spaces at different rates while
;; still sharing one definition of what decay MEANS; `(BeliefDecayRate)` supplies the default.
;; Ages BACKWARD gracefully: t < t₀ yields c > c₀ rather than an error, and callers clamp at the point
;; of use — this rule states the law, it does not police its domain.
(= (DecayedConfidence $c0 $t0 $t $lambda)
   (* $c0 (exp (* -1.0 (* $lambda (- $t $t0))))))

;; ── re-validation confidence (R10) ───────────────────────────────────────────────────────────────
;; Moved here from base_rate.metta, where it sat unreferenced next to the base-rate formulas. A stale
;; belief's confidence, refreshed from the evidence that still anchors the symbol. Strength is
;; deliberately NOT recomputed: re-validation refreshes how confident we are given current evidence, it
;; does not invent what we believe. Deriving a node's base-rate STRENGTH is `BaseRateTv`'s job and needs
;; an extension/universe notion, not just a count.
(= (EvidenceConfidence $n) (Truth_w2c $n))
