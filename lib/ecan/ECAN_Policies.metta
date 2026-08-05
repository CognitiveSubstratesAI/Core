;; ECAN_Policies.metta
;; ECAN Economic Parameters — all evolvable MeTTa atoms
;; Reference: iCog-Labs metta-attention/attention/AttentionParam.metta
;;
;; ALL values here are live atoms — the AGI can rewrite them without restarting Julia.
;; Two-tier rent: WA (whole atomspace) rate < AF (attentional focus) rate.
;;
;; ⚠️ SCOPE OF "the AGI can rewrite them" (qualified 2026-08-05 against Hyperon Whitepaper 2026 v5).
;; The line above is right about THESE constants and wrong as a blanket rule for the file's future.
;; v5 §6.11 (Self-Modification Governor) puts "attention thresholds / routing weights" on the LOWEST
;; rung of a region-differentiated ladder — "may auto-adjust WITHIN BOUNDS" — so every value currently
;; in this file is legitimately self-adjustable, at the lightest ceremony there is. But the same
;; section requires that every accepted change leave a record (normalised proposal, policy version,
;; before/after snapshot), and it excludes three regions from ordinary self-modification entirely:
;; safety invariants, protected capability boundaries, and the governor itself. v5 §7.7 adds that
;; Allow-granting authority "must come from an immutable, signed, versioned manifest verified against
;; a trust root OUTSIDE the agent-controlled revision loop."
;; So: if a bound, a safety invariant, or anything permission-granting is ever added to this file, the
;; blanket sentence above stops being true of it. Keep those in a separate, externally-rooted place.
;;
;; ┌──────────────────────────────────────────────────────────────────────────────────────────┐
;; │ 🛑 THIS FILE IS THE ONLY HOME FOR THESE CONSTANTS. Do not copy them into Julia.          │
;; │                                                                                          │
;; │ There is a Julia numeric kernel for ECAN spreading at                                    │
;; │   MORKTensorNetworks/src/ecan/ECANTensorBridge.jl                                        │
;; │ It computes v' = Dv fast (dense/GPU). It must own NO policy — its parameters are         │
;; │ REQUIRED arguments with no defaults, precisely so it cannot hold a stale copy of         │
;; │ anything below. If you are adding a parameter for it, add the atom HERE and pass it in.  │
;; │                                                                                          │
;; │ WHY THE WARNING IS THIS LOUD — it has been ignored twice:                                │
;; │   2026-05-10  the Julia bridge implemented ECAN without anyone opening this directory.   │
;; │   2026-06-04  an audit caught it and recorded that Core is the only ground truth.        │
;; │   2026-08-05  while fixing that, a Julia duplicate of `combine-prob-vectors`             │
;; │               (SpreadingActivation.metta:126) was written as if it were a gap, and       │
;; │               hebbian-max-allocation-percentage was hardcoded there as 0.05 — upstream   │
;; │               metta-attention's value — while THIS FILE says 0.5. A 10x divergence.      │
;; │                                                                                          │
;; │ Note for anyone porting from upstream `metta-attention`: Core is ALREADY a faithful      │
;; │ port of it (SpreadingActivation.metta:3 cites it directly). "Upstream has X and we       │
;; │ don't" is therefore a claim about THIS directory and must be checked here first — and    │
;; │ where a value here differs from upstream's, the difference is deliberate. This file's    │
;; │ 0.5 is not a typo for AttentionParam.metta's 0.05.                                       │
;; └──────────────────────────────────────────────────────────────────────────────────────────┘

;; -------------------------------------------------------
;; 1. Global Attention Fund Pools
;; -------------------------------------------------------
;; Total available STI/LTI currency in the system.
;; Depleted as AV is allocated; replenished by wages.
(= (starting-funds-sti) 100000.0)
(= (starting-funds-lti) 100000.0)

;; Target fund levels — wages scale to restore funds toward these.
(= (sti-funds-target) 10000.0)
(= (lti-funds-target) 10000.0)

;; Buffer for wage normalization (clamps deficit ratio to [-1, 1]).
(= (sti-funds-buffer) 10000.0)
(= (lti-funds-buffer) 10000.0)

;; -------------------------------------------------------
;; 2. Wage Parameters
;; -------------------------------------------------------
;; Base wage paid to an atom each time it is used (stimulated).
;; Actual wage = base-wage * clamp((target - funds) / buffer, -1, 1)
(= (sti-atom-wage) 10.0)
(= (lti-atom-wage) 10.0)
(= (vlti-atom-wage) 2.0)

;; -------------------------------------------------------
;; 3. Rent Parameters (Two-Tier)
;; -------------------------------------------------------
;; WA rent: charged to ALL atoms every governance tick.
(= (wa-sti-rent-rate) 0.01)
(= (wa-lti-rent-rate) 0.005)

;; AF rent: charged ADDITIONALLY to atoms inside Attentional Focus.
;; Higher than WA — creates pressure gradient that flushes stale focus atoms.
(= (af-sti-rent-rate) 0.05)
(= (af-lti-rent-rate) 0.02)

;; -------------------------------------------------------
;; 4. Decay / Normalization (Julia primitive parameters)
;; -------------------------------------------------------
;; Used by apply-decay! → decimate-importance!(ecan-decay-factor)
(= (ecan-decay-factor) 0.05)
;; Used by apply-normalization! → normalize-attention!(ecan-target-sti-sum)
(= (ecan-target-sti-sum) 1000.0)

;; -------------------------------------------------------
;; 5. Attentional Focus Parameters
;; -------------------------------------------------------
(= (max-af-size) 100.0)
(= (max-link-num) 300.0)
;; Minimum STI for an atom to enter the AF.
(= (af-min-sti-threshold) 0.1)

;; -------------------------------------------------------
;; 6. Spreading Parameters (overridden by self-evolution)
;; -------------------------------------------------------
(= (max-spreading-depth) 3)
(= (spreading-decay-factor) 0.7)
(= (spreading-threshold) 0.1)
(= (max-spread-percentage) 0.3)
(= (hebbian-max-allocation-percentage) 0.5)

;; -------------------------------------------------------
;; 7. Governance Policies (call Julia primitives)
;; -------------------------------------------------------
;; Effect functions return True (not the () that decimate-importance!/normalize-attention! inherit from
;; set-av!→add-atom). On the faithful engine a ()-value bound in a `let` whose body is another nested
;; `let` poisons the chain (returns empty) — so governance-step!/fluid-attention-step! short-circuit.
;; Returning True keeps these usable as effect statements in a let-sequence.
(= (apply-decay!)
   (let $dummy (println! "Applying ECAN Decay...")
        (let $d (decimate-importance! (ecan-decay-factor)) True)))

(= (apply-normalization!)
   (let $n (normalize-attention! (ecan-target-sti-sum)) True))
