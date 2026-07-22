;; stv.metta — Truth Value (STV) Storage Primitives
;;
;; MeTTa-First implementation: truth values stored as atoms in &self.
;; Pattern: (AtomSTV $atom $strength $confidence)
;; Same approach as ECAN's (AV $id $sti $lti $vlti) atoms.
;;
;; API:
;;   (get-stv $atom)               -> (STV $strength $confidence)
;;   (set-stv $atom $s $c)         -> True
;;   (stv-strength (STV $s $c))    -> $s
;;   (stv-confidence (STV $s $c))  -> $c

;; get-stv: retrieve truth value, default STV(0.0,0.0) if not found
(= (get-stv $atom)
   (match &self (AtomSTV $atom $s $c) (STV $s $c)))

;; set-stv: store truth value atom
;; NOTE: rule head uses $s,$c to match the alpha-invariant body pattern (AtomSTV $atom $s $c)
(= (set-stv $atom $s $c)
   (add-atom &self (AtomSTV $atom $s $c)))

;; Extract components from a truth value.
;;
;; BOTH constructor cases, deliberately. `(STV $s $c)` is what get-stv/get-tv above build; but every
;; truth FORMULA in the library — Truth_Deduction, Truth_Revision, Truth_Induction, BaseRateTv, … —
;; emits the LOWERCASE `(stv $s $c)`, and both files load into one Space. With only the uppercase
;; clause the accessors were PARTIAL over the library's own majority constructor: calling
;; `(stv-strength (Truth_Deduction …))` matched no rule, so it silently failed to reduce and marshalled
;; out as 0.0 — that is how `(0,0)` beliefs got written (commit 11fbc0c), and the consumer still
;; carries a positional `case` workaround (WorldModel/lib/base_rate_refresh.metta:20-28).
;; Note the direction of the fix: lowercase is the MAJORITY form, so the accessors widen to meet the
;; formulas rather than the formulas being switched to uppercase.
(= (stv-strength (STV $s $c)) $s)
(= (stv-confidence (STV $s $c)) $c)
(= (stv-strength (stv $s $c)) $s)
(= (stv-confidence (stv $s $c)) $c)

;; get-tv: canonical truth value retrieval (alias for get-stv)
;; Used by PLN inference rules (infer-step, |- rules)
(= (get-tv $atom)
   (match &self (AtomSTV $atom $s $c) (STV $s $c)))

;; clamp lives in Core stdlib/math.metta (always loaded) — local copy removed 2026-06-10.
