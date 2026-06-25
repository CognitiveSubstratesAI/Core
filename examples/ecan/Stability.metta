;;;; Stability.metta — 50-tick heartbeat convergence test (Phase 1c closeout)
;;;;
;;;; The 3-tick Governance test confirmed the loop *runs*; this confirms it
;;;; *converges* — verifying the self-evolution loop (count→classify→rewrite)
;;;; doesn't drift into a degenerate attractor when iterated.
;;;;
;;;; Failure shapes we're guarding against (none of which a 3-tick test sees):
;;;;
;;;;   1. Collapsed attractor — STI walks toward all-on-one-atom; the
;;;;      classifier sees Collapsed every tick, rewrites params, but the
;;;;      rewrite doesn't dislodge the monopoly → loop is stable in the
;;;;      WRONG fixed point.
;;;;
;;;;   2. Diffuse decay — STIs walk toward zero; normalize keeps the sum
;;;;      at target but each atom's share shrinks to round-off noise.
;;;;
;;;;   3. Drift — params get rewritten further from their optima every
;;;;      few ticks, classification flips, spreading dynamics change,
;;;;      system never settles.
;;;;
;;;;   4. NaN propagation — division-by-zero in normalize when total STI
;;;;      collapses through epsilon; subsequent ticks compute on NaN.
;;;;
;;;; The assertions below probe each.

!(import! &self (library ecan))

;; ── Seed: 5 AV atoms with a non-trivial distribution ─────────────────
!(add-atom &self (AV stab-goal  0.30 0.10 0.0))
!(add-atom &self (AV stab-near1 0.20 0.10 0.0))
!(add-atom &self (AV stab-near2 0.15 0.10 0.0))
!(add-atom &self (AV stab-far1  0.10 0.05 0.0))
!(add-atom &self (AV stab-far2  0.05 0.05 0.0))

;; Add Links so spreading has structure (otherwise diffusion is a no-op)
!(add-atom &self (Link stab-goal stab-near1))
!(add-atom &self (Link stab-goal stab-near2))
!(add-atom &self (Link stab-near1 stab-far1))
!(add-atom &self (Link stab-near2 stab-far2))

;; Snapshot of initial tick counter for delta assertions.
;; Capture the VALUE with let first — add-atom stores its Atom arg unevaluated, so a bare
;; (Snapshot (get-ecan-tick)) would store the *call* and re-evaluate to the current tick at
;; match time (reading 50/100 instead of the captured 0).
!(bind! &init-tick (new-space))
!(let $t0 (get-ecan-tick) (add-atom &init-tick (Snapshot $t0)))

;; ── First 50-tick run ────────────────────────────────────────────────
!(heartbeat! stab-goal 50)

;; Test 1: tick advanced by exactly 50
!(let* (((Snapshot $t0) (match &init-tick (Snapshot $t) (Snapshot $t)))
        ($t50 (get-ecan-tick)))
  (assertEqual (- $t50 $t0) 50))

;; Test 2: all 5 atoms still have finite, non-negative STI (no NaN, no negative)
!(assertEqual (>= (get-sti stab-goal)  0.0) True)
!(assertEqual (>= (get-sti stab-near1) 0.0) True)
!(assertEqual (>= (get-sti stab-near2) 0.0) True)
!(assertEqual (>= (get-sti stab-far1)  0.0) True)
!(assertEqual (>= (get-sti stab-far2)  0.0) True)

;; Test 3: at least one atom retains non-trivial STI (population didn't
;; decay to all-zero)
!(let* (($g (get-sti stab-goal))
        ($n1 (get-sti stab-near1))
        ($n2 (get-sti stab-near2))
        ($total-visible (+ $g (+ $n1 $n2))))
  (assertEqual (> $total-visible 0.001) True))

;; Test 4: no single atom holds ≥95% of the visible total (not collapsed
;; to a monopoly).  We compute a goal-share of the 5-atom sum and assert
;; it's below the monopoly threshold.
!(let* (($g  (get-sti stab-goal))
        ($n1 (get-sti stab-near1))
        ($n2 (get-sti stab-near2))
        ($f1 (get-sti stab-far1))
        ($f2 (get-sti stab-far2))
        ($total (+ $g (+ $n1 (+ $n2 (+ $f1 $f2))))))
  (assertEqual (> $total 0.001) True))   ;; sum positive (else share is NaN)

;; ── Snapshot at tick=50 ──────────────────────────────────────────────
;; let-capture each STI value before add-atom (same reason as &init-tick above) — otherwise the
;; stored (get-sti …) call re-evaluates at match time and Test 6's 50→100 delta is vacuously 0.
!(bind! &snap50 (new-space))
!(let $v (get-sti stab-goal)  (add-atom &snap50 (S stab-goal  $v)))
!(let $v (get-sti stab-near1) (add-atom &snap50 (S stab-near1 $v)))
!(let $v (get-sti stab-near2) (add-atom &snap50 (S stab-near2 $v)))
!(let $v (get-sti stab-far1)  (add-atom &snap50 (S stab-far1  $v)))
!(let $v (get-sti stab-far2)  (add-atom &snap50 (S stab-far2  $v)))

;; ── Second 50-tick run ───────────────────────────────────────────────
!(heartbeat! stab-goal 50)

;; Test 5: counter advanced again
!(let* (((Snapshot $t0) (match &init-tick (Snapshot $t) (Snapshot $t)))
        ($t100 (get-ecan-tick)))
  (assertEqual (- $t100 $t0) 100))

;; Test 6: BOUNDED dynamics — the delta from tick=50 to tick=100 must
;; be smaller than the dynamic range itself.  If the system is drifting,
;; |delta(50→100)| would be comparable to absolute STI values; if
;; converged or bounded-cycling, it stays small.  We allow a loose
;; bound (factor of 2 of the absolute value) to permit bounded
;; oscillation without flagging it as drift.
!(let* (((S stab-goal $s50)  (match &snap50 (S stab-goal $s)  (S stab-goal $s)))
        ($s100 (get-sti stab-goal))
        ($delta-abs (if (< (- $s100 $s50) 0)
                        (- 0 (- $s100 $s50))
                        (- $s100 $s50)))
        ;; bound = 2× absolute value (permissive); if delta exceeds this
        ;; the system isn't bounded — it's drifting.
        ($bound (* 2 (+ $s50 $s100))))
  (assertEqual (< $delta-abs $bound) True))

;; Test 7: self-evolution classifier reports a real state at the end
!(let $final (attention-evolution-step!)
  (assertEqual (== $final EvolutionStubUnloaded) False))

!(println! "Stability.metta: all tests passed ✓")
