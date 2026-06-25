;; ECAN_Policies.metta
;; ECAN Economic Parameters — all evolvable MeTTa atoms
;; Reference: iCog-Labs metta-attention/attention/AttentionParam.metta
;;
;; ALL values here are live atoms — the AGI can rewrite them without restarting Julia.
;; Two-tier rent: WA (whole atomspace) rate < AF (attentional focus) rate.

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
(= (apply-decay!)
   (let $dummy (println! "Applying ECAN Decay...")
        (decimate-importance! (ecan-decay-factor))))

(= (apply-normalization!)
   (normalize-attention! (ecan-target-sti-sum)))
