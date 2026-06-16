;; pln_ecan_coupling.metta — §4.9 "demand as backward attention"
;; ─────────────────────────────────────────────────────────────────────────────
;; Couples PLN's backward DEMAND field (pln_factor_graph.metta) to ECAN's STI
;; (lib/ecan/), making PLN and ECAN co-working cognitive algorithms over ONE shared
;; metagraph: what the reasoner needs to know (demand) drives what is important (STI),
;; and ECAN's budget normalization keeps the loop stable.
;;
;; GROUNDED in the source paper, NOT an invented calibration (cf. the explicitly
;; "PLAUSIBLE-BUT-ILLUSTRATIVE" metamo/ecan_bridge.metta). The coupling is
;; PLN_backward_chaining_factor_graphs_spec.md §4.9, verbatim:
;;
;;     STI_new(v) = (1 - ρ)·STI_old(v) + ρ·d̂(v),   0 < ρ ≤ 1
;;     followed by normalization to a fixed STI budget.
;;
;;   "Rule/factor attention can modulate backward demand, but only through a damped
;;    + normalized channel → avoids uncontrolled positive feedback between demand
;;    and attention."
;;
;; The TWO halves of that safety property are both present here:
;;   (1) ρ damping        — demand only nudges STI by a fraction ρ per step.
;;   (2) budget normalize  — normalize-attention! rescales Σ STI to a fixed sum.
;; Together they bound the demand↔attention loop (validated in test_pln_ecan.jl:
;; iterating the coupling stays bounded — it does not blow up).
;;
;; d̂(v) (normalized demand): the demand field's per-atom dem(v) is already clamped
;; to [0,1] by the §3.3 adjoint `clampu`, so dem(v) IS the normalized backward-
;; attention signal d̂(v). The absolute STI scale is reconciled by step (2): the EMA
;; blends the prior-STI pattern with the demand pattern by weight ρ, then
;; normalize-attention! re-budgets the population. ρ is the source's tunable.
;;
;; Co-work usage (both libs are independent — load explicitly, like ecan_bridge):
;;   !(import! &self (library pln))   ;; or load pln_factor_graph.metta
;;   !(import! &self (library ecan))
;;   !(import! &self ".../lib/pln/pln_ecan_coupling.metta")
;;   !(gated-demand-field! <query> <tau> True)   ;; PLN computes the demand field
;;   !(couple-demand->attention!)                ;; demand → STI, then re-budget

;; --- coupling rate ρ ∈ (0,1]; source leaves it tunable. 0.5 = equal blend. ---
(= (pln-ecan-rho) 0.5)

;; --- d̂(v): normalized backward demand for atom v (dem is pre-clamped to [0,1]) ---
;;     returns 0.0 if v carries no demand (no (dem v _) atom).
(= (dem-hat $v)
   (let $d (collapse (match &self (dem $v $d0) $d0))
        (if (== $d ()) 0.0 (car-atom $d))))

;; --- §4.9 damped EMA update for ONE atom: STI_new = (1-ρ)·STI_old + ρ·d̂ ---
(= (demand->sti! $v)
   (let* (($rho (pln-ecan-rho))
          ($old (get-sti $v))
          ($dh  (dem-hat $v))
          ($new (+ (* (- 1.0 $rho) $old) (* $rho $dh))))
     (set-sti! $v $new)))

;; --- couple the WHOLE demand field to attention, then re-budget ---
;;     (collapse forces the per-atom EMA over every demanded node; then normalize.)
;;     Iterating over (dem v _) touches only variable nodes (query+premises), not
;;     factors — attention accrues to the propositions being reasoned about.
(= (couple-demand->attention!)
   (let $_ (collapse (match &self (dem $v $d) (demand->sti! $v)))
        (normalize-attention! (ecan-target-sti-sum))))

;; --- one full co-work tick: PLN demand field → ECAN attention ---
;;     query-focused attention in one call (gated demand expansion + §4.9 coupling).
(= (pln-attention-tick! $query $tau)
   (let $_ (gated-demand-field! $query $tau True)
        (couple-demand->attention!)))
