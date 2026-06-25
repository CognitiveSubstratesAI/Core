;; lib/hyperseed/adaptive_attention.metta — Self-Evolving Attention Policy
;;
;; Phase 1c port from packages/PRIMUS_Core/lib/hyperseed/adaptive_attention.metta.
;; Closes the self-evolution loop for the cognitive heartbeat's Attend phase:
;;
;;   measure  → classify  → adapt
;;   |          |           └─ rewrite spreading-decay-factor and
;;   |          |              max-spreading-depth atoms in &self
;;   |          └─ Collapsed / Balanced / Diffuse
;;   └─ samples STI distribution from AV atoms
;;
;; ── Adaptations vs PRIMUS_Core source ───────────────────────────────────
;;
;; 1.  (Importance $id $sti $lti)        → (AV $id $sti $lti $vlti)
;;     PRIMUS_Core has BOTH Importance and AV atoms (legacy + current).
;;     Core unifies on AV; we walk the AV atoms here.
;;
;; 2.  (current-time)                    → (get-ecan-tick)
;;     Use the deterministic ECAN tick counter instead of wall-clock — ties
;;     scan/cooldown timing to the heartbeat that drives this loop.
;;
;; 3.  Removed duplicate scan-due? / update-scan-tick!  — state_logic
;;     already defines `(scan-due?)` (0-arg, reads tick internally) and
;;     `set-attention-scan-tick!`.  This file uses those.
;;
;; 4.  (length $atoms)                   → (size-atom $atoms)
;;
;; 5.  count-atoms-in-sti-range fixed: PRIMUS used a conditional template
;;     `(if in-range :found ())` assuming `()` results would be filtered
;;     from match output.  Core's match pushes every template result
;;     unevaluated, so the count was wrong.  Fixed via the scalar-template
;;     count pattern: do a separate match per range and count `yes` results.
;;
;; 6.  collapse(match) atom-template fixes applied to rewrite-spreading-param!,
;;     record-policy-change! (drop collapse, use match result directly).

;; ============================================================
;; 0. Scan & Adaptation Parameters (evolvable atoms)
;; ============================================================

;; NOTE: (attention-scan-interval) is already defined in state_logic.metta
;; as a default of 50.  The original PRIMUS file redefined it; we leave the
;; state_logic version authoritative.

;; Minimum ticks between policy changes (oscillation damping)
(= (attention-policy-cooldown) 30)

;; ============================================================
;; 1. Attention State Measurement
;; ============================================================

;; Count AV atoms whose STI falls in [lo, hi).
;;
;; PRIMUS_Core attempted to filter via a conditional template, but Core's
;; match does not evaluate the template (the substituted expression gets
;; pushed verbatim).  An attempt with `(if ... yes (empty))` as the template
;; also fails — `(empty)` is not filtered post-hoc; every match contributes.
;;
;; Working approach: collect (Box (Pair id sti)) atoms for ALL matches via
;; collapse-match (Box keeps the count correct per the Phase 1b audit),
;; then filter at iteration time inside foldl-atom — where the body IS
;; evaluated per element.
(= (count-atoms-in-sti-range $lo $hi)
   (let $boxes (collapse (match &self (AV $id $sti $lti $vlti)
                                (Box (Pair $id $sti))))
        (foldl-atom $boxes 0 $acc $boxed
          (let* (((Pair $id $sti) (unbox $boxed)))
            (if (and (>= $sti $lo) (< $sti $hi))
                (+ $acc 1)
                $acc)))))

;; Measure the current attention distribution.  Gated by `(scan-due?)` from
;; state_logic so we don't run the full O(N) scan every tick.
;;
;; Returns (AttentionMeasure $high $mid $low $total)
;;      or (AttentionMeasure skipped) when cooldown is active.
(= (measure-attention-state!)
   (if (== (scan-due?) True)
       (let $_ (set-attention-scan-tick! (get-ecan-tick))
            (let* (($high  (count-atoms-in-sti-range 0.6 1.1))
                   ($mid   (count-atoms-in-sti-range 0.2 0.6))
                   ($low   (count-atoms-in-sti-range 0.0 0.2))
                   ($total (+ $high (+ $mid $low))))
              (AttentionMeasure $high $mid $low $total)))
       (AttentionMeasure skipped)))

;; ============================================================
;; 2. Attention State Classification
;; ============================================================

;; Skipped-scan passthrough — keeps Skipped distinct from real classes.
(= (classify-attention-state (AttentionMeasure skipped)) Skipped)

;; Collapsed: monopoly (>70% of atoms in the high band) → entropy too low.
;; Diffuse:   no atoms in the high band → entropy too high.
;; Balanced:  healthy mix.
(= (classify-attention-state (AttentionMeasure $high $mid $low $total))
   (if (== $total 0)
       Balanced
       (let* (($high-ratio (/ $high $total)))
         (if (> $high-ratio 0.7)
             Collapsed
             (if (== $high 0)
                 Diffuse
                 Balanced)))))

;; ============================================================
;; 3. Adaptive Policy Update — rewrites spreading parameter atoms.
;; ============================================================

;; Replace a parameter rule's value.
;;   (= ($param-expr) old-value)  →  (= ($param-expr) new-value)
;; collapse dropped — the matched atom IS the rule expression itself.
(= (rewrite-spreading-param! $param-expr $new-value)
   (let $old (match &self (= ($param-expr) $v) (= ($param-expr) $v))
        (let $_ (if (== $old ()) () (remove-atom &self $old))
             (add-atom &self (= ($param-expr) $new-value)))))

;; Allow a policy change iff cooldown elapsed OR state differs from last change.
(= (policy-change-allowed? $new-state $current-tick)
   (let $last (match &self (AttentionPolicyLastChanged $t $s)
                           (AttentionPolicyLastChanged $t $s))
        (if (== $last ())
            True
            (let* (((AttentionPolicyLastChanged $last-tick $last-state) $last)
                   ($elapsed (- $current-tick $last-tick)))
              (if (>= $elapsed (attention-policy-cooldown))
                  True
                  (if (== $last-state $new-state) False True))))))

;; Record a policy change (replace any prior AttentionPolicyLastChanged atom).
(= (record-policy-change! $tick $state)
   (let $old (match &self (AttentionPolicyLastChanged $t $s)
                          (AttentionPolicyLastChanged $t $s))
        (let $_ (if (== $old ()) () (remove-atom &self $old))
             (add-atom &self (AttentionPolicyLastChanged $tick $state)))))

;; Adapt spreading parameters based on classified attention state.
;;
;; Collapsed → increase decay factor (spread STI further out)
;;             increase depth         (reach more atoms)
;; Diffuse   → decrease decay factor (conserve STI near focus)
;;             decrease depth         (tighten focus)
;; Balanced / Skipped → no change

(= (adapt-spreading-policy! Skipped) True)

(= (adapt-spreading-policy! Balanced)
   (add-atom &self (AttentionEvolutionLog
                     (tick (get-ecan-tick))
                     (state Balanced)
                     (no-change True))))

(= (adapt-spreading-policy! Collapsed)
   (let $tick (get-ecan-tick)
        (if (== (policy-change-allowed? Collapsed $tick) True)
            (let* (($current-decay (spreading-decay-factor))
                   ($current-depth (max-spreading-depth))
                   ($new-decay (clamp (+ $current-decay 0.05) 0.0 0.95))
                   ($new-depth (clamp (+ $current-depth 1) 1 6)))
              (do (rewrite-spreading-param! spreading-decay-factor $new-decay)
                  (rewrite-spreading-param! max-spreading-depth    $new-depth)
                  (record-policy-change! $tick Collapsed)
                  (add-atom &self (AttentionEvolutionLog
                                    (tick $tick)
                                    (state Collapsed)
                                    (decay $current-decay -> $new-decay)
                                    (depth $current-depth -> $new-depth)))))
            (AttentionPolicyCooldownActive Collapsed))))

(= (adapt-spreading-policy! Diffuse)
   (let $tick (get-ecan-tick)
        (if (== (policy-change-allowed? Diffuse $tick) True)
            (let* (($current-decay (spreading-decay-factor))
                   ($current-depth (max-spreading-depth))
                   ($new-decay (clamp (- $current-decay 0.05) 0.3 1.0))
                   ($new-depth (clamp (- $current-depth 1) 1 6)))
              (do (rewrite-spreading-param! spreading-decay-factor $new-decay)
                  (rewrite-spreading-param! max-spreading-depth    $new-depth)
                  (record-policy-change! $tick Diffuse)
                  (add-atom &self (AttentionEvolutionLog
                                    (tick $tick)
                                    (state Diffuse)
                                    (decay $current-decay -> $new-decay)
                                    (depth $current-depth -> $new-depth)))))
            (AttentionPolicyCooldownActive Diffuse))))

;; ============================================================
;; 4. Main Entry Point — overrides the stub in AttentionPolicies.
;;
;; This is what makes governance-step!'s Phase 4 (self-evolution) live —
;; when this file is loaded, (attention-evolution-step!) returns a real
;; classified AttentionState (Collapsed/Balanced/Diffuse/Skipped) instead
;; of the EvolutionStubUnloaded sentinel from the Phase 1b stub.
;; ============================================================

(= (attention-evolution-step!)
   (let* (($measure (measure-attention-state!))
          ($state   (classify-attention-state $measure)))
     (do (adapt-spreading-policy! $state)
         $state)))
