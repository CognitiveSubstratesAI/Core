;;;; delete_inconsistent_handle.metta — deleteInconsistentHandle (port of metta-moses
;;;; reduct/boolean-reduct/delete-inconsistent-handle.metta). Removes a POA whose
;;;; handle set (dominant ∪ guard set) contains a literal and its negation.
;;;;   POA (AND (NOT A) (OR B C)), dominantSet (A), parent (OR B (AND (NOT A) (OR B C)))
;;;;     → (OR B)
;;;;
;;;; CORE-DIALECT: the ONE genuinely-cartesian reduct pattern lives here —
;;;; isConsistentExp paired every literal with every other via
;;;; `((superpose $h) (superpose $h))` (double-superpose, which Core CANNOT fan out).
;;;; Rewritten deterministically as "does any literal have its negation present"
;;;; (negate-lit via 4-arg unify + is-member). Plain `let` tuple-destructures → let*.

;; negate-lit — strip a NOT, or add one (the literal's complement).
(= (negate-lit $lit) (unify $lit (NOT $x) $x (NOT $lit)))

;; hasNegationPair — does any literal in $xs have its negation present in $full?
(= (hasNegationPair $xs $full)
   (if (== $xs ())
       False
       (if (is-member (negate-lit (car-atom $xs)) $full)
           True
           (hasNegationPair (cdr-atom $xs) $full))))

;; isConsistentExp — True unless the set holds both a literal and its negation.
(= (isConsistentExp $handleSet)
   (if (== $handleSet ())
       True
       (not (hasNegationPair $handleSet $handleSet))))

;; deleteInconsistentHandle — drop the POA if its handle set is inconsistent. The
;; root special-case (parent==current) keeps a top-level (AND) rather than vanishing.
(= (deleteInconsistentHandle $parent $current $dominantSet)
   (let* (($guardSet     (getGuardSet $current))
          ($handleSet     (concatTuple $dominantSet $guardSet))
          ($isConsistent  (isConsistentExp $handleSet)))
     (if $isConsistent
         ($parent $current False)
         (if (== $parent $current)
             ((AND) () True)
             (let $up (subtraction-atom $parent ($current))
               ($up () True))))))

;; ── nested-traversal wrappers (used by the orchestrator's applyAndTransformations) ──
(= (applyDeleteIncons $parent $current $dominantSet)
   (let* ((($newParent $newCurrent $applied) (deleteInconsistentHandle $parent $current $dominantSet))
          ($children (getChildrenExp $newCurrent)))
     (if (== $children ())
         ($newParent $newCurrent $applied)
         (let* ((($child $rest) (decons-atom $children))
                ($grandChild (getChildrenExp $child))
                (($UpdatedChildren $unwt $appliedOnChild)
                   (if (== $grandChild ())
                       ($child () False)
                       (let* ((($h $t) (decons-atom $grandChild)))
                         (applyDeleteIncons6 $child $h $dominantSet $t $applied True))))
                (($updatedCurrent $updatedchild $appliedOnCurrent)
                   (if (=== $child $UpdatedChildren)
                       (deleteInconsistentHandle $newCurrent $child $dominantSet)
                       (let $fr (findAndReplace $child $UpdatedChildren $newCurrent)
                         ($fr $UpdatedChildren $appliedOnChild))))
                ($updatedParent (findAndReplace $newCurrent $updatedCurrent $newParent)))
           (applyDeleteIncons5 $updatedParent $updatedCurrent $dominantSet $appliedOnCurrent $rest)))))

(= (applyDeleteIncons5 $parent $current $dominantSet $applied $children)
   (if (== $children ())
       ($parent $current $applied)
       (let* ((($child $rest) (decons-atom $children))
              (($updatedCurrent $_ $bool) (deleteInconsistentHandle $current $child $dominantSet))
              ($updatedParent (findAndReplace $current $updatedCurrent $parent)))
         (applyDeleteIncons5 $updatedParent $updatedCurrent $dominantSet $applied $rest))))

(= (applyDeleteIncons6 $parent $current $dominantSet $children $appliedToParent $checkingChild)
   (if (== $children ())
       (deleteInconsistentHandle $parent $current $dominantSet)
       (let* ((($child $rest) (decons-atom $children))
              (($updatedCurrent $_ $bool) (deleteInconsistentHandle $current $child $dominantSet))
              ($updatedParent (findAndReplace $current $updatedCurrent $parent)))
         (applyDeleteIncons5 $updatedParent $updatedCurrent $dominantSet $bool $rest))))
