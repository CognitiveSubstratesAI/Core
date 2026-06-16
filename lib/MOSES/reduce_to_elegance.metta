;;;; reduce_to_elegance.metta — the boolean-reduct orchestrator (port of metta-moses
;;;; reduct/boolean-reduct/reduce-to-elegance.metta). Drives a tree to elegant normal
;;;; form by repeatedly applying the constraint/normalization rules until a fixpoint.
;;;; `reduce-to` is the entry point cleanTree calls.
;;;;
;;;; CORE-DIALECT: `until` ported from general-helpers (fn/pred passed BY NAME — OK
;;;; post bare-symbol fix; the eval/`true`-string quirk dropped); `cut` → no-op;
;;;; setDifference → subtraction-atom; superpose-maps → map-atom; the
;;;; ((get-metatype $current) $current) case scrutinee is bound via let first
;;;; (Core only evaluates an expr whose HEAD is a symbol).

;; until — apply $function to $x until $predicate holds (do-while).
(= (until $predicate $function $x)
   (if (== ($predicate $x) True)
       $x
       (until $predicate $function ($function $x))))

;; cut — Core is single-result; the upstream backtracking-prune is a no-op here.
(= (cut) ())

;; setDifference — elements of $a not in $b.
(= (setDifference $a $b) (subtraction-atom $a $b))

;; ── reduceToElegance — the recursive core (AND / OR cases) ───────────────────
(= (reduceToElegance $parent $current $dominantSet $commandSet)
   (let $mt (get-metatype $current)
   (case ($mt $current)
     (((Symbol $symbol) ($parent $symbol False))
      ((Expression ()) ($parent $current False))
      ((Expression (NOT $a)) ($parent $current False))
      ((Expression $current)
       (case (car-atom $current)
         ((AND
           (let* (($guardSet (getGuardSet $current))
                  ($children (getChildrenExp $current))
                  ($updatedGuardSet  (setDifference $guardSet $dominantSet))
                  ($updatedGuardSet' (setDifference $updatedGuardSet $commandSet))
                  ($appliedRedundantOr1CC (or (not (== $updatedGuardSet $guardSet))
                                              (not (== $updatedGuardSet' $updatedGuardSet))))
                  ($updatedSubExpression (concatTuple $updatedGuardSet' $children))
                  ($updatedCurrent (cons-atom AND $updatedSubExpression))
                  ($updatedParent  (findAndReplace $current $updatedCurrent $parent))
                  (($oneSubsumeParent $oneSubsumeCurrent $appliedOneSubsume)
                     (oneConstraintSubsume $updatedParent $updatedCurrent $commandSet))
                  (($unwt3 $unwt2 ($updatedParent' $updatedCurrent' $bool))
                     (if $appliedOneSubsume
                         ($dominantSet $commandSet ($oneSubsumeParent $oneSubsumeCurrent True))
                         (until transformationsNotApplied applyAndTransformations
                                ($commandSet $dominantSet ($updatedParent $updatedCurrent True)))))
                  ($childFromParent (if (== $updatedCurrent' ()) (cdr-atom $updatedParent') $updatedCurrent'))
                  ($zeroCurrent (let $h (if (not (== $childFromParent ())) (car-atom $childFromParent) ())
                                  (if (== (get-metatype $h) Expression) $h $childFromParent)))
                  (($finalParent $finalCurrent $finalBool)
                     (zeroConstraintSubsume' $updatedParent' $zeroCurrent))
                  ($finalCurrent' (if (== $finalCurrent ()) (AND) $finalCurrent)))
             ($finalParent $finalCurrent'
                (any ($appliedRedundantOr1CC $appliedOneSubsume $bool $finalBool)))))
          (OR
           (let* ((($promoteParent $promoteCurrent $appliedPromote)
                     (promoteCommonConstraints $parent $current))
                  (($x $xs ($updatedParent $updatedCurrent $bool))
                     (until transformationsNotApplied applyOrTransformations
                            ($commandSet $dominantSet ($promoteParent $promoteCurrent True))))
                  (($finalUpdatedParent $finalUpdatedCurrent $finalBool)
                     (zeroConstraintSubsume' $updatedParent $updatedCurrent)))
             ($finalUpdatedParent $finalUpdatedCurrent
                (any ($bool $finalBool $appliedPromote))))))))))))

;; transformationsNotApplied — until predicate: stop once the carried bool is False.
(= (transformationsNotApplied ($dummy $dummy2 ($parent $current $bool))) (not $bool))

;; ── applyAndTransformations ──────────────────────────────────────────────────
(= (applyAndTransformations ($commandSet $dominantSet ($parent $current $unwt)))
   (let* (($guardSet (getGuardSet $current))
          ($children (getChildrenExp $current))
          ($firstChild (if (not (== $children ())) (car-atom $children) ()))
          ($remainingChildren (if (not (== $firstChild ())) (cdr-atom $children) ()))
          ($handleSet (unique-atom (union-atom $guardSet $dominantSet)))
          (($delInconHandleParent $delInconHandleCurrent $appliedDelInconHandle)
             (applyDeleteIncons $parent $current $handleSet))
          (($andCutParent $andCutCurrent $appliedAndCut)
             (andCut $delInconHandleParent $delInconHandleCurrent)))
     (if (or $appliedDelInconHandle $appliedAndCut)
         ($commandSet $dominantSet ($andCutParent $andCutCurrent True))
         (let* ((($commandSet'' $dominantSet'' ($updatedParent $updatedCurrent $appliedRTE))
                   (if (not (== $children ()))
                       (let* ((($dominantSet' $commandSet' ($finalUpdatedParent $finalUpdatedCurrent $bool) ($lastChild $lastRemainingChild))
                                 (until hasNoNextChild applyReduceToEleganceToOr
                                        ($commandSet $handleSet ($parent $current False) ($firstChild $remainingChildren))))
                              ($grandChildren (getChildrenExp $finalUpdatedCurrent))
                              ($firstGrandChild (if (not (== $grandChildren ())) (car-atom $grandChildren) ()))
                              ($remainingGChildren (if (not (== $firstGrandChild ())) (cdr-atom $grandChildren) ()))
                              (($finalUpdatedCurrent' $appliedOrCut ($lastGChild $restGChildren))
                                 (until hasNoNextChild applyOrCut
                                        ($finalUpdatedCurrent False ($firstGrandChild $remainingGChildren))))
                              ($finalUpdatedParent' (findAndReplace $finalUpdatedCurrent $finalUpdatedCurrent' $finalUpdatedParent)))
                         ($commandSet' $dominantSet' ($finalUpdatedParent' $finalUpdatedCurrent' (or $bool $appliedOrCut))))
                       ($commandSet $dominantSet ($parent $current False)))))
           ($commandSet $dominantSet ($updatedParent $updatedCurrent $appliedRTE))))))

;; applyReduceToEleganceToAnd — foldl-like RTE over an AND node's children.
(= (applyReduceToEleganceToAnd ($commandSet $dominantSet ($parent $prevCurrent $bool) ($firstChild $remainingChildren)))
   (let* (($nextChild (if (not (== $remainingChildren ())) (car-atom $remainingChildren) ()))
          ($rest (if (not (== $remainingChildren ())) (cdr-atom $remainingChildren) ()))
          (($updatedCurrent $updatedChild $appliedRTE)
             (reduceToElegance $prevCurrent $firstChild $dominantSet $commandSet))
          ($updatedParent (findAndReplace $prevCurrent $updatedCurrent $parent))
          ($updatedChildren (getChildrenExp $updatedCurrent))
          ($resetNextChild (if (not (== $updatedChildren ())) (car-atom $updatedChildren) ()))
          ($resetRemainingChildren (if (not (== $resetNextChild ())) (cdr-atom $updatedChildren) ())))
     (if $appliedRTE
         ($commandSet $dominantSet ($updatedParent $updatedCurrent (or $appliedRTE $bool)) ($resetNextChild $resetRemainingChildren))
         ($commandSet $dominantSet ($updatedParent $updatedCurrent (or $appliedRTE $bool)) ($nextChild $rest)))))

;; ── applyOrTransformations ───────────────────────────────────────────────────
(= (applyOrTransformations ($commandSet $dominantSet ($parent $current $bl)))
   (let* ((($zeroSubsumeParent $zeroSubsumeCurrent $appliedZeroSubsume)
             (zeroConstraintSubsume $parent $current))
          (($orCutParent $orCutCurrent $appliedOrCut)
             (orCut $zeroSubsumeParent $zeroSubsumeCurrent))
          ($children (getChildrenExp $current))
          ($firstChild (if (not (== $children ())) (car-atom $children) ()))
          ($remainingChildren (if (not (== $firstChild ())) (cdr-atom $children) ())))
     (if (any ($appliedZeroSubsume $appliedOrCut))
         ($commandSet $dominantSet ($orCutParent $orCutCurrent True))
         (let* ((($dominantSet' $commandSet' ($finalUpdatedParent $finalUpdatedCurrent $bool) ($lastChild $rest))
                   (until hasNoNextChild applyReduceToEleganceToAnd
                          ($commandSet $dominantSet ($parent $current False) ($firstChild $remainingChildren)))))
           ($commandSet $dominantSet ($finalUpdatedParent $finalUpdatedCurrent $bool))))))

;; applyReduceToEleganceToOr — RTE over an OR node's children (with localCommandSet).
(= (applyReduceToEleganceToOr ($commandSet $dominantSet ($parent $prevCurrent $bool) ($currentChild $remainingChildren)))
   (if (not (== $currentChild ()))
       (let* (($localCommandSet (localCommandSet $currentChild (getChildrenExp $prevCurrent) (getGuardSet $prevCurrent) $commandSet))
              ($nextChild (if (not (== $remainingChildren ())) (car-atom $remainingChildren) ()))
              ($restChildren (if (not (== $nextChild ())) (cdr-atom $remainingChildren) ()))
              (($updatedCurrent $updatedChild $appliedRTE)
                 (reduceToElegance $prevCurrent $currentChild $dominantSet $localCommandSet))
              (($promoteCurrent $promoteChild $appliedPromote)
                 (promoteCommonConstraints $updatedCurrent $updatedChild))
              ($grandChildren (getChildrenExp $promoteCurrent))
              ($firstGChild (if (not (== $grandChildren ())) (car-atom $grandChildren) ()))
              ($remainingGChildren (if (not (== $firstGChild ())) (cdr-atom $grandChildren) ()))
              (($finalUpdatedCurrent $appliedAndCut ($lastChild $rest))
                 (until hasNoNextChild applyAndCut ($promoteCurrent False ($firstGChild $remainingGChildren))))
              ($finalUpdatedParent (findAndReplace $prevCurrent $finalUpdatedCurrent $parent))
              ($updatedChildren (getChildrenExp $finalUpdatedCurrent))
              ($updatedFirstChild (if (not (== $updatedChildren ())) (car-atom $updatedChildren) ()))
              ($updatedRestChildren (if (not (== $updatedFirstChild ())) (cdr-atom $updatedChildren) ()))
              ($returnValue ($commandSet $dominantSet ($finalUpdatedParent $finalUpdatedCurrent (any ($appliedRTE $bool $appliedAndCut))) ($nextChild $restChildren))))
         (if (any ($appliedRTE $appliedAndCut))
             ($commandSet $dominantSet ($finalUpdatedParent $finalUpdatedCurrent (any ($appliedRTE $bool $appliedAndCut))) ($updatedFirstChild $updatedRestChildren))
             $returnValue))
       ($commandSet $dominantSet ($parent $prevCurrent False) (() ()))))

;; ── localCommandSet ──────────────────────────────────────────────────────────
(= (localCommandSet $child $parentChildren $parentGuardSet $commandSet)
   (case ($parentChildren $parentGuardSet)
     (((() ()) $commandSet)
      ($else
        (let* (($siblings (if (not (== $parentChildren ())) (removeElement ($child) $parentChildren) ()))
               ($filteredGuardSet (if (not (== $parentGuardSet ())) (removeElement ($child) $parentGuardSet) ()))
               ($filteredSiblings (if (not (== $siblings ())) (filtP $siblings isTerminalAndNode) ()))
               ($siblingsGuardSet (if (not (== $filteredSiblings ())) (map-atom $filteredSiblings $fs (getGuardSet $fs)) ()))
               ($siblingsGuardSetF (foldl-atom $siblingsGuardSet () $acc $x (concatT $acc $x)))
               ($totalGuardSet (concatTuple $filteredGuardSet $siblingsGuardSetF))
               ($localCommandSet (unique-atom (union-atom $totalGuardSet $commandSet))))
          $localCommandSet)))))

;; isTerminalAndNode — a terminal AND node ((AND lit) or (AND (NOT x))) — predicate
;; form of upstream's partial filterTerminalAndNode.
(= (isTerminalAndNode $node)
   (case $node
     (((AND (NOT $x)) True)
      ((AND $x) (if (== (get-metatype $x) Symbol) True False))
      ($else False))))

;; ── until predicates ─────────────────────────────────────────────────────────
(= (hasNoNextChild ($parent $bool ($child $remainingChildren))) (== $child ()))
(= (hasNoNextChild ($dominantSet' $commandSet' ($finalUpdatedParent $finalUpdatedCurrent $bool) ($nextChild $remainingChildren))) (== $nextChild ()))

(= (reduceNotApplied ($parent $current $applied)) (not $applied))

;; ── applyReduce — one normalize+RTE pass ─────────────────────────────────────
(= (applyReduce ($parent $current $applied))
   (let* (($propNotExpr       (propagateNot $current))
          ($gatherJunctorExpr (gatherJunctors $propNotExpr))
          ($initAdd           (addAND $gatherJunctorExpr))
          ($finalAdd          (addAND $initAdd True))
          ($finalParent       (findAndReplace $current $finalAdd $parent)))
     (reduceToElegance $finalParent $finalAdd () ())))

;; removeAndNodesFromGuards — strip the wrapping ANDs left around single guard sets.
(= (removeAndNodesFromGuards $expr)
   (if (or (== (get-metatype $expr) Symbol) (== $expr ()))   ; empty () is an Expression — guard decons-atom
       $expr
       (let* ((($head $rest) (decons-atom $expr)))
         (if (and (== $head AND) (== (size-atom $rest) 1))
             (let $x (car-atom $rest)
               (if (or (nonExprOrNot $x) (== (get-metatype $x) Symbol))
                   $x
                   (let $r (removeAndNodesFromGuards $x) (AND $r))))
             (let $updatedRest (map-atom $rest $exp (removeAndNodesFromGuards $exp))
               (cons-atom $head $updatedRest))))))
(= (nonExprOrNot $x)
   (if (== (get-metatype $x) Expression) (== (car-atom $x) NOT) False))

;; ── reduce-to — the entry point (repeat applyReduce to a fixpoint) ───────────
(= (reduce-to $expr)
   (let* ((($parent $uwnt $uwnt2) (until reduceNotApplied applyReduce ($expr $expr True)))
          (($newParent $u3 $u4) (applyReduce ($parent $parent True)))
          ($cutv (cut)))
     (if (== $newParent $parent)
         (removeAndNodesFromGuards $parent)
         (reduce-to $newParent))))
