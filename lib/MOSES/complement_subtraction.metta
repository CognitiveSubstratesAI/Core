;;;; complement_subtraction.metta — oneCcSub (port of metta-moses reduct/boolean-reduct/
;;;; one-constraint-complement-subtraction.metta). Removes a POA constraint X that is
;;;; commanded by its own negation: if a commanding AND's guard set contains ¬X and the
;;;; POA's guard set contains X, X is redundant in the POA.
;;;;   $parent (OR (AND D) (AND B C)), $poa (AND B C), $com ((NOT B) C) → (OR (AND D) (AND C))
;;;;
;;;; CORE-DIALECT: the superpose/collapse/let element-maps become map-atom; set
;;;; intersection/subtraction → intersection-atom/subtraction-atom; invertLiterals uses
;;;; Core's 4-arg `unify` (bind $x from (NOT $x), else negate) per element.

;; invertLiterals — negate each literal (strip a NOT, or add one).
;;   (A (NOT B)) → ((NOT A) B)
(= (invertLiterals $guardSet)
   (map-atom $guardSet $literal (unify $literal (NOT $x) $x (NOT $literal))))

;; oneCcSub — subtract from the POA's guard set the constraints whose negation
;; commands them.
(= (oneCcSub $parent $poa $com)
   (let* (($poaGuardSet    (getGuardSet $poa))
          ($invertedCom    (invertLiterals $com))
          ($commonElements (intersection-atom $poaGuardSet $invertedCom)))
     (map-atom $parent $el
        (if (== $el $poa) (subtraction-atom $poa $commonElements) $el))))
