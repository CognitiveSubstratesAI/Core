;; core_logic.metta
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

;; Inlined collapse-match form (find-first-number filters to the first numeric match — see the
;; AV-accessors note above). get-sti/get-lti/get-vlti are verified working by the ECAN acceptance
;; suite (Stimulate asserts get-sti=10.1, etc.); the old "returns 0.0 / interpreter bug" note was a
;; false diagnosis (the real issue was a library-layer bug) and has been removed.
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
;; Conserving upsert — mirrors upstream metta-attention setAv (getter-and-setter.metta:16-50):
;; every STI/LTI change is balanced against the global funds pool so total STI (atoms + funds) is
;; conserved. stiDiff = oldSti - newSti; funds += stiDiff. Wages (STI up) draw from funds; rent
;; (STI down) refills funds — automatically, at the single accounting point. (2026-06-30: was
;; fund-blind, which split accounting into stimulate! and leaked rent — see Rent/Stimulate examples.)
(= (set-av! $id $new-sti $new-lti $new-vlti)
   (let* (($old-sti (get-sti $id))
          ($old-lti (get-lti $id)))
     (let $exists (collapse (match &self (AV $id $s $l $v) found))
          (let $cleared (if (== $exists ()) True
                            (let $old (match &self (AV $id $a $b $c) (AV $id $a $b $c))
                                 (remove-atom &self $old)))
               (let $_ (add-atom &self (AV $id $new-sti $new-lti $new-vlti))
                    (let $_ (set-funds-sti! (+ (get-funds-sti) (- $old-sti $new-sti)))
                         (set-funds-lti! (+ (get-funds-lti) (- $old-lti $new-lti)))))))))

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

;; Direct STI boost. Raw STI rides the economic scale (like funds/wages) — NOT capped at a fixed
;; "concentration". Canonical metta-attention keeps STI unbounded; the [0,1] concentration is a
;; normalized VIEW via recent-max-sti (see get-normalised-sti). The old 0.3 raw-STI cap was a scale
;; bug: it clamped every atom to 0.3 while funds/target/wage run at 100000/10000/10-scale, so atoms
;; could never absorb attention from the pool and trade-sti! was non-zero-sum. (2026-06-30)
(= (boost-sti! $id $amount)
   (set-sti! $id (+ (get-sti $id) $amount)))

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
;; Reference: calculateSTIWage in attention-bank.metta (canonical metta-attention / singnet attention).
;;
;; wage = base-wage * (1 + clamp((funds - target) / buffer, -1, 1))   ->  range [0, 2*base], NON-negative
;; When funds are HIGH -> pay MORE (up to 2*base): push STI out of the over-full pool into used atoms.
;; When funds are LOW  -> wage -> 0: stop paying. The pool is refilled by RENT, not by a negative wage.
;; (A wage is a PAYMENT and is structurally non-negative. The homeostatic negative feedback runs through
;;  RENT — opposite numerator, gated off when funds>=target. The prior (target-funds) numerator + the
;;  +/-base envelope was a DOUBLE sign-inversion that paid NEGATIVE wages at the shipped start state,
;;  punishing atoms for being used -> the negative-STI cascade. Verified vs ECAN theory + canonical
;;  calculateSTIWage, 2026-06-30.)
;; -------------------------------------------------------

(= (calculate-sti-wage)
   (let* (($funds  (get-funds-sti))
          ($target (sti-funds-target))
          ($buffer (sti-funds-buffer))
          ($ndiff  (clamp (/ (- $funds $target) $buffer) -1.0 1.0))   ; funds - target (canonical)
          ($base   (sti-atom-wage)))
     (+ $base (* $base $ndiff))))                                      ; [0, 2*base], never negative

(= (calculate-lti-wage)
   (let* (($funds  (get-funds-lti))
          ($target (lti-funds-target))
          ($buffer (lti-funds-buffer))
          ($ndiff  (clamp (/ (- $funds $target) $buffer) -1.0 1.0))
          ($base   (lti-atom-wage)))
     (+ $base (* $base $ndiff))))

;; -------------------------------------------------------
;; 5. Stimulate — pay wages when atom is used
;; Reference: stimulate() in attention-bank.metta
;; Called by the evaluator/reasoning engine whenever an atom
;; participates in inference or goal evaluation.
;; -------------------------------------------------------

;; Pay wages: raise the atom's STI/LTI; the funds debit is handled by set-av!'s conserving accounting
;; (STI up -> funds down), so we no longer adjust funds here (that double-counted before the recouple).
(= (stimulate! $id $factor)
   (let* (($sti-wage  (calculate-sti-wage))
          ($lti-wage  (calculate-lti-wage))
          ($cur-sti   (get-sti $id))
          ($cur-lti   (get-lti $id))
          ($cur-vlti  (get-vlti $id))
          ($new-sti   (+ $cur-sti (* $sti-wage $factor)))
          ($new-lti   (+ $cur-lti (* $lti-wage $factor))))
     (set-av! $id $new-sti $new-lti $cur-vlti)))

;; -------------------------------------------------------
;; 6. Rent Collection (Two-Tier, deficit-scaled)
;; Reference: RentCollectionBaseAgent.metta — the homeostat's COLLECT side.
;;
;; WA rent: applied to ALL atoms (whole atomspace).
;; AF rent: applied ADDITIONALLY to atoms in Attentional Focus.
;; Rent refills funds (opposite direction of wages), via set-av!'s conserving accounting.
;;
;; Deficit-scaled: rent is GATED OFF (0) when funds >= target (pool full enough — let wages drain the
;; surplus); below target it ramps  rate * (1 + clamp((target-funds)/buffer, 0, 1))  up to 2*rate as
;; funds fall a full buffer below target. This is the OPPOSITE numerator to calculate-sti-wage: the
;; wage pays MORE at high funds, rent collects MORE at low funds — together they regulate funds ->
;; target (the homeostat). Raw STI is economic-scale: floor at 0, no [0,1] ceiling (see boost-sti!).
;; -------------------------------------------------------

(= (deficit-rent-rate $base $funds $target $buffer)
   (if (>= $funds $target) 0.0
       (* $base (+ 1.0 (clamp (/ (- $target $funds) $buffer) 0.0 1.0)))))

(= (collect-wa-rent! $id)
   (let* (($sti (get-sti $id))
          ($lti (get-lti $id))
          ($vlti (get-vlti $id))
          ($sr (deficit-rent-rate (wa-sti-rent-rate) (get-funds-sti) (sti-funds-target) (sti-funds-buffer)))
          ($lr (deficit-rent-rate (wa-lti-rent-rate) (get-funds-lti) (lti-funds-target) (lti-funds-buffer)))
          ($new-sti (max 0.0 (- $sti $sr)))
          ($new-lti (max 0.0 (- $lti $lr))))
     (set-av! $id $new-sti $new-lti $vlti)))

(= (collect-af-rent! $id)
   (let* (($sti (get-sti $id))
          ($lti (get-lti $id))
          ($vlti (get-vlti $id))
          ($sr (deficit-rent-rate (af-sti-rent-rate) (get-funds-sti) (sti-funds-target) (sti-funds-buffer)))
          ($lr (deficit-rent-rate (af-lti-rent-rate) (get-funds-lti) (lti-funds-target) (lti-funds-buffer)))
          ($new-sti (max 0.0 (- $sti $sr)))
          ($new-lti (max 0.0 (- $lti $lr))))
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

;; recent-max-sti — the current max STI over all AV atoms (a stateless stand-in for upstream's
;; recentMaxSTI). Epsilon floor so the [0,1] normalization never divides by zero.
(= (recent-max-sti)
   (let $ids (get-all-av-atoms)
        (if (== $ids ()) 0.000001
            (foldl-atom $ids 0.000001 $acc $id (max $acc (get-sti $id))))))

;; Normalised STI to [0, 1] — raw STI over the dynamic recent-max (canonical: normalize by
;; recentMaxSTI, NOT a fixed divisor; raw STI is economic-scale, unbounded).
(= (get-normalised-sti $id)
   (/ (get-sti $id) (recent-max-sti)))

;; -------------------------------------------------------
;; 8. Bulk Operations (Phase 1b — pure MeTTa replacement for the Julia
;;    primitives `decimate-importance!` / `normalize-attention!` used by
;;    PRIMUS_Core's AttentionEngine.jl).
;;
;;    `apply-decay!` and `apply-normalization!` in ECAN_Policies.metta
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
