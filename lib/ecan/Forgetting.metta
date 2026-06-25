;;;; Forgetting.metta — ECAN Forgetting Agent (memory reclamation)
;;;;
;;;; Port of metta-attention's ForgettingAgent. LTI (Long-Term Importance) is the
;;;; persistence currency, so atoms with LTI below a threshold are eligible to be
;;;; forgotten — EXCEPT atoms reinforced by Hebbian links, which are learning-
;;;; protected (removing them would erase associative structure). Forgetting fires
;;;; when the atom population exceeds a cap, keeping a long-running agent's working
;;;; set bounded.
;;;;
;;;; This closes the clearest functional gap found in the ECAN cross-check vs
;;;; upstream metta-attention (Core had no forgetting). Pure MeTTa; no grounded
;;;; primitives. Deliberately simpler than upstream: no importance-bin scan and no
;;;; LTI-then-STV secondary sort (those are scale-driven and deferred) — a flat
;;;; threshold + Hebbian protection, which is the core semantics.

;; ── Parameters (evolvable atoms) ────────────────────────────────────────────
(= (forget-lti-threshold) 0.05)   ;; LTI strictly below this ⇒ eligible to forget
(= (max-atoms) 1000.0)            ;; population cap above which forgetting fires

;; ── Hebbian protection ──────────────────────────────────────────────────────
;; An atom is protected iff it is a source OR target of any AsymHebbianLink.
;; NB: built on the FREE-pattern collapse (the path that works — cf. get-af-atoms)
;; plus membership, NOT a ground-pattern `(match &self (AsymHebbianLink $id …))`
;; which would hit the collapse-match-in-rule-body quirk (the is-in-af? lesson).
(= (hebbian-link-sources)
   (collapse (match &self (AsymHebbianLink $src $tgt $s $c) $src)))
(= (hebbian-link-targets)
   (collapse (match &self (AsymHebbianLink $src $tgt $s $c) $tgt)))
(= (hebbian-protected? $id)
   (or (member $id (hebbian-link-sources))
       (member $id (hebbian-link-targets))))

;; ── Forgettability ──────────────────────────────────────────────────────────
(= (forgettable? $id)
   (and (< (get-lti $id) (forget-lti-threshold))
        (not (hebbian-protected? $id))))

;; ── Removal ─────────────────────────────────────────────────────────────────
;; Drop the atom's AV record (single-match remove — the set-av! pattern) and its
;; AF membership if any. Returns True.
(= (forget-atom! $id)
   (let $old (match &self (AV $id $s $l $v) (AV $id $s $l $v))
        (let $_ (if (== $old ()) True (remove-atom &self $old))
             (if (is-in-af? $id) (remove-from-af! $id) True))))

;; ── Agent ───────────────────────────────────────────────────────────────────
;; Conditional sweep: forget every forgettable atom, but only once the population
;; exceeds max-atoms. The list is a collapsed snapshot, so removing during the
;; fold is safe.
(= (forgetting-step!)
   (let $all (get-all-av-atoms)
        (if (< (size-atom $all) (max-atoms))
            True
            (foldl-atom $all True $_ $id
              (if (forgettable? $id) (forget-atom! $id) True)))))

;; Unconditional sweep — ignores the population cap. Explicit GC + used by tests.
(= (forget-sweep!)
   (let $all (get-all-av-atoms)
        (foldl-atom $all True $_ $id
          (if (forgettable? $id) (forget-atom! $id) True))))
