;;;; cut_unnecessary_and.metta — andCut transformation (port of metta-moses
;;;; reduct/boolean-reduct/cut-unnecessary-and.metta). Removes a guard-set-empty,
;;;; single-child AND by lifting its grandchildren into the parent.
;;;;   POA (AND (OR (AND B D) (NOT E))) under parent (OR C …)
;;;;     → (OR C (AND B D) (NOT E))
;;;;
;;;; CORE-DIALECT: upstream's `(collapse (removeEmptyAND (superpose $x)))` element-map
;;;; that DROPS (empty) results → `(filter-atom (map-atom …) isNotUnit)`; the
;;;; if-decons-expr-custom calls (deferred Atom-arg eval, unsupported) are inlined
;;;; using the already-bound ($h $t) decons; result tuples are pre-bound via let*.

;; removeEmptyAND — strip empty `(AND)` nodes from an expression tree. An empty AND
;; maps to () and is dropped by its parent's child-map. (Deterministic rewrite of the
;; upstream superpose/collapse + `(empty)` form.)
(= (rmEA-children $xs)
   (if (== $xs ())
       ()
       (let* (($r    (removeEmptyAND (car-atom $xs)))
              ($rest (rmEA-children (cdr-atom $xs))))
         (if (== $r ()) $rest (cons-atom $r $rest)))))
(= (removeEmptyAND $expr)
   (if (== (get-metatype $expr) Symbol)
       $expr
       (let* ((($h $t) (decons-atom $expr)))
         (if (== $h AND)
             (if (== $t ()) () (cons-atom AND (rmEA-children $t)))
             (cons-atom $h (rmEA-children $t))))))

;; intersections — common literals across a nested tuple; () for a singleton (vs
;; findCommon which returns the lone element).
(= (intersections $nestedTuple)
   (case $nestedTuple
     ((() $nestedTuple)
      ($else
        (if (== (cdr-atom $nestedTuple) ())
            ()
            (let* (($first (car-atom $nestedTuple))
                   ($tail  (cdr-atom $nestedTuple)))
              (findCommonLiterals $first $tail)))))))

;; andCut — lift the grandchildren of a guard-set-empty single-child AND.
(= (andCut $parent $current)
   (if (== $parent $current)
       ($parent $current False)
       (let* (($parentSec  (filtP (map-atom $parent  $e (removeEmptyAND $e)) isNotUnit))
              ($currentSec  (if (=== $parent $current)
                                $parentSec
                                (filtP (map-atom $current $e (removeEmptyAND $e)) isNotUnit)))
              (($guardSet $child) (getLiteralChildren $currentSec))
              ($childIsExpr (and (== (get-metatype $child) Expression) (not (== $child ()))))
              (($h $t) (if $childIsExpr (decons-atom $child) (() ())))
              ($tail (if $childIsExpr $t "No child")))
         (if (and (== $tail ()) (== $guardSet ()))
             (let* (($childFirst (if $childIsExpr $h ()))
                    (($grandLiterals $grandChildren) (getLiteralChildren $childFirst))
                    ($allLiterals (map-atom $grandChildren $gc (getGuardSet $gc)))
                    ($common      (intersections $allLiterals))
                    ($updatedParent  (removeElement ($currentSec) $parentSec))
                    ($updatedParent' (if (== () (subtraction-atom $parentSec $currentSec))
                                         $updatedParent
                                         (addChildren $updatedParent $grandChildren)))
                    ($updatedParent'' (addLiterals $updatedParent' $grandLiterals)))
               (if (== $common ())
                   ($updatedParent'' () True)
                   ($parentSec $currentSec False)))
             ($parentSec $currentSec False)))))

;; applyAndCut — one andCut step threaded through the until loop's state.
(= (applyAndCut ($parent $bool ($child $remainingChildren)))
   (let* ((($updatedParent $updatedChild $appliedAndCut) (andCut $parent $child))
          ($newBool      (or $appliedAndCut $bool))
          ($nextChild    (if (~= $remainingChildren ()) (car-atom $remainingChildren) ()))
          ($restChildren (if (~= $remainingChildren ()) (cdr-atom $remainingChildren) ())))
     ($updatedParent $newBool ($nextChild $restChildren))))
