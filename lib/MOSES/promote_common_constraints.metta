;;;; promote_common_constraints.metta — promoteCommonConstraints (port of metta-moses
;;;; reduct/boolean-reduct/promote-common-constraints.metta). For an OR node, factor
;;;; the literals common to ALL its children up into the parent, removing them from
;;;; each child.
;;;;   POA (OR (AND A B) (AND A C)) → A promoted: children become (OR (AND B) (AND C)),
;;;;   parent gains A.
;;;;
;;;; CORE-DIALECT: `(collapse (getLiterals (superpose $children)))` per-child literal
;;;; map → `(map-atom $children $c (getLiterals $c))`; removeCommonLiterals likewise;
;;;; atomIntersection → grounded intersection-atom.

(= (promoteCommonConstraints $parent $current)
   (if (and (not (== $current ())) (not (== $parent ())))
       (let* ((($literals $children) (getLiteralChildren $current))
              ($childrenLiteral (if (not (== $children ()))
                                    (map-atom $children $c (getLiterals $c))
                                    ()))
              ($common (if (not (== $childrenLiteral ())) (findCommon $childrenLiteral) ())))
         (if (== $common ())
             ($parent $current False)
             (let* (($updatedChildren (removeCommonLiterals $common $children))
                    ($updatedLiterals (removeElement $common $literals))
                    ($newExp          (concatTuple $updatedLiterals $updatedChildren))
                    ($newCurrent      (cons-atom OR $newExp))
                    ($updatedParent   (findAndReplace $current $newCurrent $parent))
                    ($updatedParent'  (addLiterals $updatedParent $common)))
               ($updatedParent' $newCurrent True))))
       ($parent $current False)))

;; removeCommonLiterals — drop the $common literals from each member of a nested tuple.
(= (removeCommonLiterals $common $tuple)
   (if (== $tuple ())
       ()
       (map-atom $tuple $t (removeElement $common $t))))

;; atomIntersection — intersection of two literal tuples ($common when $lit is empty).
(= (atomIntersection $lit $common)
   (if (== $lit ()) $common (intersection-atom $lit $common)))
