;;;; propagate_not.metta — De Morgan negation push-down (port of metta-moses
;;;; reduct/boolean-reduct/n-ary-propagate-not.metta). Drives NOTs inward to the
;;;; literals: (NOT (AND A B)) → (OR (NOT A) (NOT B)), etc. First stage of applyReduce.
;;;;
;;;; CORE-DIALECT: upstream's `(map-atom $t (|-> ($x) …))` lambda becomes Core's
;;;; template `(map-atom $t $x …)`; `xor` is inlined as (not (== a b)).

;; xor is now a Core stdlib op (stdlib/core.metta) — was localized here, consolidated 2026-06-10.

(= (propagateNot $expr) (propagateNot $expr False))
(= (propagateNot $expr $negate)
   (if (== (get-metatype $expr) Expression)
       (if (== $expr ())
           ()
           (let* ((($op $t) (decons-atom $expr))
                  ($result (map-atom $t $childExpr
                                     (propagateNot $childExpr (xor (== $op NOT) $negate)))))
             (case $op
               ((AND (if $negate (cons-atom OR $result) (cons-atom AND $result)))
                (OR  (if $negate (cons-atom AND $result) (cons-atom OR $result)))
                (NOT (car-atom $result))
                ($_  ERROR)))))
       (if (== (get-metatype $expr) Symbol)
           (if $negate (NOT $expr) $expr)
           $expr)))
