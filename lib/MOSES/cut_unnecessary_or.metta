;;;; cut_unnecessary_or.metta — orCut transformation (port of metta-moses
;;;; reduct/boolean-reduct/cut-unnecessary-or.metta). Removes a single-child OR by
;;;; lifting its child into the parent.
;;;;   POA (OR (AND (NOT D))) under parent (AND B (OR (AND (NOT D))))
;;;;     → (AND B (NOT D))
;;;;
;;;; CORE-DIALECT: each rewriting case arm binds its updated parent via let* before
;;;; building the result tuple — a bare ((addLiterals …) () True) tuple would keep
;;;; the call UNEVALUATED (list construction does not evaluate elements).

;; orCut — lift the single child of an OR node into the parent.
(= (orCut $parent $current)
   (case $current
     (((OR (NOT $x))
       (let $up (addLiterals (removeElement ($current) $parent) ((NOT $x)))
         ($up () True)))
      ((OR $x)
       (if (== (get-metatype $x) Symbol)
           (let $up (addLiterals (removeElement ($current) $parent) ($x))
             ($up () True))
           (let $up (addChildren (removeElement ($current) $parent) (getSubExpression $x))
             ($up () True))))
      ($else ($parent $current False)))))

;; getSubExpression — all subexpressions (literals + children) of a node; a (NOT …)
;; literal has none.
(= (getSubExpression $exp)
   (case $exp
     (((NOT $a) ())
      ($else (let* (($literals (getLiterals $exp))
                    ($children (getChildrenExp $exp)))
               (concatTuple $literals $children))))))

;; applyOrCut — one orCut step threaded through the until loop's (parent bool
;; (child remaining)) state. The combined bool is bound via let* (tuple construction
;; would not evaluate the (or …) call).
(= (applyOrCut ($parent $bool ($child $remainingChildren)))
   (let* ((($updatedParent $updatedChild $appliedOrCut) (orCut $parent $child))
          ($newBool      (or $appliedOrCut $bool))
          ($nextChild    (if (~= $remainingChildren ()) (car-atom $remainingChildren) ()))
          ($restChildren (if (~= $remainingChildren ()) (cdr-atom $remainingChildren) ())))
     ($updatedParent $newBool ($nextChild $restChildren))))
