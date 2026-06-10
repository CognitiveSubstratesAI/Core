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

;; Extract components from a truth value
(= (stv-strength (STV $s $c)) $s)
(= (stv-confidence (STV $s $c)) $c)

;; get-tv: canonical truth value retrieval (alias for get-stv)
;; Used by PLN inference rules (infer-step, |- rules)
(= (get-tv $atom)
   (match &self (AtomSTV $atom $s $c) (STV $s $c)))

;; clamp lives in Core stdlib/math.metta (always loaded) — local copy removed 2026-06-10.
