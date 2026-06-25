;; state_logic.metta
;; ECAN State: Attentional Focus Management + Tick Counters
;; Reference: iCog-Labs metta-attention/attention-bank/bank/attentional-focus/
;;
;; Atom structures:
;;   (InAF $id)           — marks atom as currently in Attentional Focus
;;   (MinAFSTI $sti)      — tracks minimum STI among AF members
;;   (ECATick $n)         — current governance tick counter
;;   (AttentionScanLastTick $n)  — last tick an entropy scan ran

;; -------------------------------------------------------
;; 1. Attentional Focus Membership
;; -------------------------------------------------------

(= (get-af-atoms)
   (collapse (match &self (InAF $id) $id)))

;; `length` is not in Core's stdlib — use the canonical `size-atom` instead.
(= (af-size)
   (let $atoms (get-af-atoms)
        (if (== $atoms ()) 0 (size-atom $atoms))))

;; Membership test. NB: a GROUND-pattern `(collapse (match &self (InAF $id) …))`
;; with $id already bound hits Core's collapse-match-in-rule-body quirk (returns
;; () even when the atom exists — the same quirk get-sti works around), so it
;; always reported False. Reuse the working free-pattern path (get-af-atoms) and
;; test membership of the returned list instead.
(= (is-in-af? $id)
   (member $id (get-af-atoms)))

;; -------------------------------------------------------
;; 2. Minimum AF STI Tracking
;; -------------------------------------------------------

(= (get-min-af-sti)
   (let $result (collapse (match &self (MinAFSTI $s) $s))
        (if (== $result ()) 0.0 (car-atom $result))))

;; Both-evaluator upsert idiom (mirrors set-av!/set-funds-sti! in core_logic): existence-guard via
;; `(collapse (match … found))` (() on no-match), then run the bare match+remove ONLY inside the
;; guarded branch so it always binds. The old unguarded `(let $old (match …))` no-op'd on the faithful
;; engine when no prior atom existed (empty match → let never binds → add skipped).
(= (set-min-af-sti! $sti)
   (let $exists (collapse (match &self (MinAFSTI $s) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (MinAFSTI $s) (MinAFSTI $s))
                               (remove-atom &self $old)))
             (add-atom &self (MinAFSTI $sti)))))

;; Recompute minimum STI across all AF members.
;; lambda → canonical 5-arg foldl-atom syntax for Core compatibility.
(= (update-min-af-sti!)
   (let $af-stis (collapse (match &self (InAF $id)
                                  (get-sti $id)))
        (if (== $af-stis ())
            (set-min-af-sti! 0.0)
            (set-min-af-sti! (foldl-atom $af-stis 1.0 $acc $v
                               (if (< $v $acc) $v $acc))))))

;; Find the AF atom with the lowest STI. foldl-atom is a SPECIAL FORM whose list/seed args are NOT
;; evaluated on the faithful engine — passing (cdr-atom $af)/(car-atom $af) inline folds over the
;; literal expression (returns the symbol `cdr-atom`). Bind both via let* first. (eval_metta tolerated
;; the inline form; the faithful engine does not.) See test_pln_ecan.jl:88.
(= (get-min-af-atom)
   (let $af (get-af-atoms)
        (if (== $af ())
            ()
            (let* (($rest (cdr-atom $af))
                   ($seed (car-atom $af)))
              (foldl-atom $rest $seed $best $id
                (if (< (get-sti $id) (get-sti $best)) $id $best))))))

;; -------------------------------------------------------
;; 3. Attentional Focus Update (Priority Queue Logic)
;; Reference: updateAf() in attentional-focus.metta
;;
;; If atom is already in AF → update STI only (membership unchanged).
;; If AF has space → add atom.
;; If AF is full AND new STI > min AF STI → evict min, add new.
;; -------------------------------------------------------

(= (update-af! $id $new-sti)
   (if (is-in-af? $id)
       True
       (if (< (af-size) (max-af-size))
           (let $_ (add-atom &self (InAF $id))
                (update-min-af-sti!))
           (if (> $new-sti (get-min-af-sti))
               (let $evicted (get-min-af-atom)
                    (let $_ (remove-atom &self (InAF $evicted))
                         (let $_ (add-atom &self (InAF $id))
                              (update-min-af-sti!))))
               False))))

(= (remove-from-af! $id)
   (let $_ (remove-atom &self (InAF $id))
        (update-min-af-sti!)))

;; -------------------------------------------------------
;; 4. Random AF Atom Selection (for stochastic diffusion)
;; Reference: getRandomAtomInAF / getRandomAtomNotInAF
;; -------------------------------------------------------

;; Stochastic AF atom selection.  The PRIMUS_Core version used random-int
;; which may not be registered in Core; the foldl just returned the last
;; element anyway (not actually random — bug in the original).  Port keeps
;; the behaviour but in 5-arg syntax; the function returns the last AF atom.
;; TODO Phase 1b: register random-int as a Julia primitive and re-introduce
;;       true stochastic selection.
(= (get-random-atom-in-af)
   (let $atoms (get-af-atoms)
        (if (== $atoms ())
            ()
            (foldl-atom $atoms () $_ $id $id))))

;; -------------------------------------------------------
;; 5. Tick Counter
;; -------------------------------------------------------

(= (get-ecan-tick)
   (let $result (collapse (match &self (ECATick $n) $n))
        (if (== $result ()) 0 (car-atom $result))))

(= (increment-ecan-tick!)
   (let $n (get-ecan-tick)
        (let $exists (collapse (match &self (ECATick $m) found))
             (let $cleared (if (== $exists ()) True
                               (let $old (match &self (ECATick $m) (ECATick $m))
                                    (remove-atom &self $old)))
                  (add-atom &self (ECATick (+ $n 1)))))))

;; -------------------------------------------------------
;; 6. Entropy Scan Gate (rate-limits adaptive_attention.metta scans)
;; -------------------------------------------------------

(= (get-attention-scan-tick)
   (let $result (collapse (match &self (AttentionScanLastTick $n) $n))
        (if (== $result ()) -1000 (car-atom $result))))

(= (set-attention-scan-tick! $n)
   (let $exists (collapse (match &self (AttentionScanLastTick $t) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (AttentionScanLastTick $t) (AttentionScanLastTick $t))
                               (remove-atom &self $old)))
             (add-atom &self (AttentionScanLastTick $n)))))

;; Default scan interval — Phase 1c (adaptive_attention.metta) may override
;; this rule and add policy-cooldown / live-rewriting.  For Phase 1a/b, the
;; constant is enough to make scan-due? answerable.
(= (attention-scan-interval) 50)

(= (scan-due?)
   (let* (($now  (get-ecan-tick))
          ($last (get-attention-scan-tick))
          ($interval (attention-scan-interval)))
     (>= (- $now $last) $interval)))
