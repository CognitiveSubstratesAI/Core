;; t1_core_logic.metta
;; ECAN Core: AV Model, Global Funds, Wages, Stimulation
;; Reference: iCog-Labs metta-attention/attention-bank/
;;
;; Atom structures:
;;   (AV $id $sti $lti $vlti)           — attention value per atom
;;   (AttentionFunds STI $amount)        — global STI fund pool
;;   (AttentionFunds LTI $amount)        — global LTI fund pool

;; -------------------------------------------------------
;; 0. Helpers for match-result filtering
;; -------------------------------------------------------
;;
;; Workaround for the trie sub-expression contamination bug (2026-04-09):
;; `match &self` inside a rule body can return spurious variable-name
;; matches from other rules' bodies alongside the correct data match.
;; The correct value is always a Number; the spurious values are always
;; Symbols (variable names like $sti, $s, $new-sti). This helper walks
;; a collapsed match-result list and returns the first Number found,
;; or a default value if no Number exists.
;;
;; This is a WORKAROUND, not the root fix. The proper fix is in the
;; match dispatch path in the interpreter (ensuring match inside rule
;; bodies uses the same trie-only path as top-level match). Filed for
;; future investigation. See commit message for details.

(= (find-first-number $list $default)
   (if (== $list ())
       $default
       (let $head (car-atom $list)
            (if (== (get-type $head) Number)
                $head
                (find-first-number (cdr-atom $list) $default)))))

;; -------------------------------------------------------
;; 0b. Box / unbox — SD-2 workaround for Core's collapse-with-atom-template
;;     ambiguity.  Defined here so every later file in the load chain can
;;     use them.  See packages/Core/docs/SEMANTIC_DELTA.md SD-2.
;; -------------------------------------------------------
(= (unbox (Box $x)) $x)

;; -------------------------------------------------------
;; 1. AV Accessors
;; -------------------------------------------------------
;;
;; Examples:
;;   (get-sti nonexistent-atom-xyz) → 0.0
;;
;; ECAN Bug (discovered 2026-04-09 via doctest):
;;   (get-sti <existing-atom>) returns 0.0 (the default fallback) instead of
;;   the actual STI value. Raw `(match &self (AV atom $sti ...) $sti)` works
;;   correctly and returns the value; but the `collapse(match(...))` pattern
;;   inside get-sti's rule body returns an empty list, triggering the default.
;;   Same issue affects get-lti and get-vlti. Root cause is likely that &self
;;   inside a rule body resolves to a different evaluation context than the
;;   top-level &self, or that collapse evaluates the match in a scope where
;;   the atom isn't visible. Investigation deferred — this is the ECAN
;;   equivalent of the PLN Channel-leak class of bugs.
;;
;; When the collapse-match-in-rule-body bug is fixed, add doctests
;; for get-sti, get-lti, get-vlti with a seeded (AV ...) atom and
;; verify they return the correct values instead of 0.0 defaults.

(= (get-av $id)
   (match &self (AV $id $sti $lti $vlti) (AV $id $sti $lti $vlti)))

;; AV accessors — use find-first-number to filter out spurious
;; variable-name matches from rule-body contamination. See section 0 above.
;;
;; Fixtures:
;;   (add-atom &self (AV ecan-doctest-acc 0.42 0.13 0.02))
;;
;; Examples:
;;   (get-sti ecan-doctest-acc) → 0.42
;;   (get-sti nonexistent-atom-xyz) → 0.0

;; Inlined form (2026-04-17): (let $result (collapse ...) (find-first-number $result 0.0))
;; was fragile in rule bodies. Inlining is closer to canonical MeTTa style.
;;
;; KNOWN INFRA BUG (investigation deferred): even after inlining, get-sti and
;; get-lti still return 0.0 while get-vlti works, despite rules being
;; structurally IDENTICAL after parsing (same aliased $a, $b, $Then, $Else
;; binding shape). Runtime-defined versions of the same rules work. Deep
;; interpreter dispatch-order bug — not in the rule code itself. Tracked
;; in project todos; revisit after D1 quoting.
(= (get-sti $id)
   (find-first-number (collapse (match &self (AV $id $sti $lti $vlti) $sti)) 0.0))

(= (get-lti $id)
   (find-first-number (collapse (match &self (AV $id $sti $lti $vlti) $lti)) 0.0))

(= (get-vlti $id)
   (find-first-number (collapse (match &self (AV $id $sti $lti $vlti) $vlti)) 0.0))

;; -------------------------------------------------------
;; 2. AV Mutation
;; -------------------------------------------------------

;; Upsert: remove any existing AV for $id, then add the new one. Both-evaluator idiom:
;;  (1) existence check via `(collapse (match ... found))` — () on no-match, (found) on hit,
;;      identical on Minimal and the legacy full Eval;
;;  (2) the remove runs OUTSIDE the match template (bare match-bind + remove-atom in evaluated
;;      position). Needed because the full Eval does NOT evaluate match templates (a
;;      remove-in-template never fires there), while Minimal's match returns EMPTY (not ()) on
;;      no-match (a bare `(let $old (match...))` no-op's there) — so neither idiom works on both alone.
(= (set-av! $id $new-sti $new-lti $new-vlti)
   (let $exists (collapse (match &self (AV $id $s $l $v) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (AV $id $a $b $c) (AV $id $a $b $c))
                               (remove-atom &self $old)))
             (add-atom &self (AV $id $new-sti $new-lti $new-vlti)))))

(= (set-sti! $id $new-sti)
   (let* (($lti  (get-lti $id))
          ($vlti (get-vlti $id)))
     (set-av! $id $new-sti $lti $vlti)))

(= (set-lti! $id $new-lti)
   (let* (($sti  (get-sti $id))
          ($vlti (get-vlti $id)))
     (set-av! $id $sti $new-lti $vlti)))

;; Clamp value to [lo, hi]
;;
;; Examples:
;;   (clamp 0.5 0.0 1.0) → 0.5
;;   (clamp 1.5 0.0 1.0) → 1.0
;;   (clamp -0.3 0.0 1.0) → 0.0
;; clamp lives in Core stdlib/math.metta (always loaded) — local copy removed 2026-06-10.

;; Direct STI boost (clamped to max-attention-concentration)
;;
;; Examples:
;;   (max-attention-concentration) → 0.3
(= (max-attention-concentration) 0.3)

(= (boost-sti! $id $amount)
   (let* (($current (get-sti $id))
          ($new     (clamp (+ $current $amount) 0.0 (max-attention-concentration))))
     (set-sti! $id $new)))

;; -------------------------------------------------------
;; 3. Global Funds
;; -------------------------------------------------------

(= (get-funds-sti)
   (let $result (collapse (match &self (AttentionFunds STI $a) $a))
        (if (== $result ()) (starting-funds-sti) (car-atom $result))))

(= (get-funds-lti)
   (let $result (collapse (match &self (AttentionFunds LTI $a) $a))
        (if (== $result ()) (starting-funds-lti) (car-atom $result))))

;; Same both-evaluator upsert as set-av! above.
(= (set-funds-sti! $amount)
   (let $exists (collapse (match &self (AttentionFunds STI $a) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (AttentionFunds STI $b) (AttentionFunds STI $b))
                               (remove-atom &self $old)))
             (add-atom &self (AttentionFunds STI $amount)))))

(= (set-funds-lti! $amount)
   (let $exists (collapse (match &self (AttentionFunds LTI $a) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (AttentionFunds LTI $b) (AttentionFunds LTI $b))
                               (remove-atom &self $old)))
             (add-atom &self (AttentionFunds LTI $amount)))))

;; -------------------------------------------------------
;; 4. Dynamic Wage Calculation
;; Reference: calculateSTIWage in attention-bank.metta
;;
;; wage = clamp((target - funds) / buffer, -1, 1) * base-wage
;; When funds are low  → positive wage (reward atoms, replenish funds)
;; When funds are high → negative wage (suppress inflation)
;; -------------------------------------------------------

(= (calculate-sti-wage)
   (let* (($funds  (get-funds-sti))
          ($target (sti-funds-target))
          ($buffer (sti-funds-buffer))
          ($ratio  (/ (- $target $funds) $buffer))
          ($clamped (clamp $ratio -1.0 1.0)))
     (* $clamped (sti-atom-wage))))

(= (calculate-lti-wage)
   (let* (($funds  (get-funds-lti))
          ($target (lti-funds-target))
          ($buffer (lti-funds-buffer))
          ($ratio  (/ (- $target $funds) $buffer))
          ($clamped (clamp $ratio -1.0 1.0)))
     (* $clamped (lti-atom-wage))))

;; -------------------------------------------------------
;; 5. Stimulate — pay wages when atom is used
;; Reference: stimulate() in attention-bank.metta
;; Called by the evaluator/reasoning engine whenever an atom
;; participates in inference or goal evaluation.
;; -------------------------------------------------------

(= (stimulate! $id $factor)
   (let* (($sti-wage  (calculate-sti-wage))
          ($lti-wage  (calculate-lti-wage))
          ($cur-sti   (get-sti $id))
          ($cur-lti   (get-lti $id))
          ($cur-vlti  (get-vlti $id))
          ($new-sti   (+ $cur-sti (* $sti-wage $factor)))
          ($new-lti   (+ $cur-lti (* $lti-wage $factor)))
          ($new-funds-sti (- (get-funds-sti) (* $sti-wage $factor)))
          ($new-funds-lti (- (get-funds-lti) (* $lti-wage $factor))))
     (let $_ (set-av! $id $new-sti $new-lti $cur-vlti)
          (let $_ (set-funds-sti! $new-funds-sti)
               (set-funds-lti! $new-funds-lti)))))

;; -------------------------------------------------------
;; 6. Rent Collection (Two-Tier)
;; Reference: RentCollectionBaseAgent.metta
;;
;; WA rent: applied to ALL atoms (whole atomspace).
;; AF rent: applied ADDITIONALLY to atoms in Attentional Focus.
;; Rent refills funds (opposite direction of wages).
;; -------------------------------------------------------

(= (collect-wa-rent! $id)
   (let* (($sti (get-sti $id))
          ($lti (get-lti $id))
          ($vlti (get-vlti $id))
          ($new-sti (clamp (- $sti (wa-sti-rent-rate)) 0.0 1.0))
          ($new-lti (clamp (- $lti (wa-lti-rent-rate)) 0.0 1.0)))
     (set-av! $id $new-sti $new-lti $vlti)))

(= (collect-af-rent! $id)
   (let* (($sti (get-sti $id))
          ($lti (get-lti $id))
          ($vlti (get-vlti $id))
          ($new-sti (clamp (- $sti (af-sti-rent-rate)) 0.0 1.0))
          ($new-lti (clamp (- $lti (af-lti-rent-rate)) 0.0 1.0)))
     (set-av! $id $new-sti $new-lti $vlti)))

;; -------------------------------------------------------
;; 7. Attentional Focus Query
;; -------------------------------------------------------

;; SD-1 / SD-2 fix: match does not evaluate the (if ...) template, so the
;; original `(if (> $sti $threshold) $id (empty))` template filter was a
;; no-op — every AV atom got included regardless of STI.  Use the same
;; Box-collect + foldl-filter pattern as count-atoms-in-sti-range so the
;; filter happens at iteration time where evaluation actually occurs.
(= (get-attentional-focus $threshold)
   (let $boxes (collapse (match &self (AV $id $sti $lti $vlti)
                                (Box (Pair $id $sti))))
        (foldl-atom $boxes () $acc $boxed
          (let* (((Pair $id $sti) (unbox $boxed)))
            (if (> $sti $threshold)
                (cons-atom $id $acc)
                $acc)))))

(= (get-all-av-atoms)
   (collapse (match &self (AV $id $sti $lti $vlti) $id)))

;; Normalised STI to [0, 1] using max-attention-concentration as ceiling
(= (get-normalised-sti $id)
   (let $sti (get-sti $id)
        (/ $sti (max-attention-concentration))))

;; -------------------------------------------------------
;; 8. Bulk Operations (Phase 1b — pure MeTTa replacement for the Julia
;;    primitives `decimate-importance!` / `normalize-attention!` used by
;;    PRIMUS_Core's AttentionEngine.jl).
;;
;;    `apply-decay!` and `apply-normalization!` in t1_ECAN_Policies.metta
;;    invoke these — they had no effect in Phase 0 because the names were
;;    unbound.  Now they fire.
;;
;;    Trade-off: O(N²) get-sti scans inside the foldl vs PRIMUS's O(N) Julia
;;    bulk loop.  Acceptable for cognitive-tick scales (≤10k atoms); revisit
;;    if a hot loop needs sub-millisecond bulk decay.
;; -------------------------------------------------------

;; Decimate STI/LTI of all AV atoms by `factor`.
;; new-sti = old-sti * (1 - factor) ; same for LTI ; VLTI preserved.
(= (decimate-importance! $factor)
   (let $retention (- 1.0 $factor)
        (let $ids (collapse (match &self (AV $id $sti $lti $vlti) $id))
             (if (== $ids ()) True
                 (foldl-atom $ids True $_ $id
                   (let* (($s (get-sti $id))
                          ($l (get-lti $id))
                          ($v (get-vlti $id)))
                     (set-av! $id (* $s $retention) (* $l $retention) $v)))))))

;; Normalize STI across all AV atoms so that ∑sti = $target.  LTI preserved.
;; If the current sum is below epsilon, no-op (avoids division by zero).
(= (normalize-attention! $target)
   (let $ids (collapse (match &self (AV $id $sti $lti $vlti) $id))
        (if (== $ids ()) True
            (let $total (foldl-atom $ids 0.0 $acc $id
                          (+ $acc (get-sti $id)))
                 (if (< $total 0.000001) True
                     (let $scale (/ $target $total)
                          (foldl-atom $ids True $_ $id
                            (let* (($s (get-sti $id))
                                   ($l (get-lti $id))
                                   ($v (get-vlti $id)))
                              (set-av! $id (* $s $scale) $l $v)))))))))
