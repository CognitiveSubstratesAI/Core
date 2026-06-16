;;;; subsumption.metta — constraint-subsumption transformations (port of metta-moses
;;;; reduct/boolean-reduct/{one,zero}-constraint-subsumption.metta).
;;;;   oneConstraintSubsume: drop an AND POA whose guard set meets the command set
;;;;     (AND E D) commanded by (C D) under (OR (AND E D) C) → (OR C).
;;;;   zeroConstraintSubsume: drop trivially-tautological OR children (empty AND).
;;;;   zeroConstraintSubsume': drop an empty AND/OR POA from its parent.
;;;;
;;;; CORE-DIALECT: `(collapse (intersection (superpose …) (superpose …)))` →
;;;; intersection-atom; `!=` (tokenizes as `! =`) → (not (==)); result tuples pre-bound
;;;; via let*.

;; oneConstraintSubsume — remove a commanded AND POA from its parent.
(= (oneConstraintSubsume $parent $current $commandSet)
   (if (== $current ())
       ($parent $current False)
       (let* (($head (car-atom $current))
              ($tail (cdr-atom $current)))
         (case $head
           ((OR  ($parent $current False))
            (NOT ($parent $current False))
            (AND (let* (($guardSet (getGuardSet $current))
                        ($common   (intersection-atom $guardSet $commandSet)))
                   (if (== $common ())
                       ($parent $current False)
                       (let $up (removeElement ($current) $parent)
                         ($up () True)))))
            ($else ($parent $current False)))))))

;; nodeHasChildOrGuard — node has at least one literal or one subexpression child.
(= (nodeHasChildOrGuard $node)
   (or (not (== (getLiterals $node) ())) (not (== (getChildrenExp $node) ()))))

;; zeroConstraintSubsume — drop OR children that have no guard set and no children.
;; NB: (get-metatype $current) is bound via let first — a case scrutinee
;; ((get-metatype $current) $current) would NOT evaluate the inner call (Core only
;; evaluates an expression whose HEAD is a symbol), leaving it unmatched.
(= (zeroConstraintSubsume $parent $current)
   (let $mt (get-metatype $current)
   (case ($mt $current)
     (((Expression ()) ($parent $current False))
      ((Expression (NOT $x)) ($parent $current False))
      ((Symbol $current) ($parent $current False))
      ((Expression $current)
       (let* (($head (car-atom $current))
              ($children (getChildrenExp $current))
              ($updatedChildren (filtP $children nodeHasChildOrGuard))
              ($updatedCurrent (cons-atom $head $updatedChildren)))
         (case ($head $children)
           (((AND $_) ($parent $current False))
            ((OR ()) ($parent $current False))
            ((OR $children)
             (let* (($up      (findAndReplace $current $updatedCurrent $parent))
                    ($applied (not (== $children $updatedChildren))))
               ($up $updatedCurrent $applied)))))))))))

;; zeroConstraintSubsume' — drop an empty AND/OR POA from its parent.
(= (zeroConstraintSubsume' $parent $current)
   (let $mt (get-metatype $current)
   (case ($mt $current)
     (((Expression ()) ($parent $current False))
      ((Expression (NOT $x)) ($parent $current False))
      ((Symbol $current) ($parent $current False))
      ((Expression $current)
       (if (and (== (car-atom $parent) OR) (== $current (AND)))
           (let $up (findAndReplace $parent (AND) $parent) ($up (AND) True))
           (let* (($children (getChildrenExp $current))
                  ($literals (getLiterals $current)))
             (if (and (not (== $current $parent)) (not (== $parent AND)))
                 (if (and (== $literals ()) (== $children ()))
                     (let $up (removeElement ($current) $parent) ($up () True))
                     ($parent $current False))
                 ($parent $current False)))))))))
