;;;; lsk.metta — Logical/Strategy Subtree Knob construction (port of metta-moses
;;;; representation/lsk.metta, the knob-CONSTRUCTION half). logicalSubtreeKnob decides,
;;;; for a candidate subtree at a target node, whether it already exists (present knob),
;;;; its reduced form exists, or it must be appended under a null-vertex placeholder —
;;;; producing an LSK (multiplicity-3: absent / present / negated). This is the function
;;;; that USES cleanTree (M6), now available.
;;;;
;;;; CORE-DIALECT: the (updateID …) calls embedded in the returned knob are let*-bound
;;;; first (data construction does not evaluate nested calls); getDiscSpec's `let`
;;;; tuple-destructure → let*; Cons/Nil → native ()-lists. getNodeId here is the
;;;; 1-arg LSK/SSK accessor (distinct by arity from tree.metta's 2/3-arg reverse lookup).
;;;;
;;;; DEFERRED to M1c-3 (getCandidate): appendTo / appendToLSK / appendToSSK (the
;;;; Instance→Tree knob-application machinery).

;; ── accessors ────────────────────────────────────────────────────────────────
(= (getNodeId (mkLSK (mkDiscKnob (mkKnob $nodeId) $multi $default $current $discSpecList))) $nodeId)
(= (getNodeId (mkSSK (mkDiscKnob (mkKnob $nodeId) $multi $default $current $discSpecList))) $nodeId)

(= (getDiscSpec (mkLSK (mkDiscKnob (mkKnob $nodeId) $multi $default $current $discSpecList)))
   (let* ((((mkDiscSpec $def) (mkDiscSpec $cur)) ($default $current)))
     ($def $cur)))

;; ── logicalSubtreeKnob — build an LSK for $subtree at target node ────────────
(= (logicalSubtreeKnob $tree (mkNodeId $target) $subtree)
   (let* (($negatedSubtree   (insertAbove $subtree (mkNode NOT)))
          ($reducedSubtree   (cleanTree $negatedSubtree))
          ($childrenOfTarget (getChildrenById $tree (mkNodeId $target))))
     (if (== True (List.contains $subtree $childrenOfTarget))
         (let* (($idOfSubtree (getSubtreeId $tree (mkNodeId $target) $subtree 0))
                ($uid         (updateID $idOfSubtree)))
           ($tree (mkLSK (mkDiscKnob (mkKnob $uid) (mkMultip 3) (mkDiscSpec 1) (mkDiscSpec 1) ()))))
         (if (== True (List.contains $reducedSubtree $childrenOfTarget))
             (let* (($idOfReducedSubtree (getSubtreeId $tree (mkNodeId $target) $reducedSubtree 0))
                    ($uid                (updateID $idOfReducedSubtree)))
               ($tree (mkLSK (mkDiscKnob (mkKnob $uid) (mkMultip 3) (mkDiscSpec 1) (mkDiscSpec 1) ()))))
             (let* ((($nullVexAppendedTree $nullVexId) (appendChild $tree (mkNodeId $target) (mkNullVex ())))
                    (($subtreeAppendedTree $subtreeId) (appendChild $nullVexAppendedTree $nullVexId $subtree))
                    ($uid                               (updateID $nullVexId)))
               ($subtreeAppendedTree (mkLSK (mkDiscKnob (mkKnob $uid) (mkMultip 3) (mkDiscSpec 0) (mkDiscSpec 0) ()))))))))

;; ── strategySubtreeKnob — build an SSK (multiplicity-2: absent/present, no negation) ──
(= (strategySubtreeKnob $tree (mkNodeId $target) $subtree)
   (let* (($childrenOfTarget (getChildrenById $tree (mkNodeId $target))))
     (if (== True (List.contains $subtree $childrenOfTarget))
         (let* (($idOfSubtree (getSubtreeId $tree (mkNodeId $target) $subtree 0))
                ($uid         (updateID $idOfSubtree)))
           ($tree (mkSSK (mkDiscKnob (mkKnob $uid) (mkMultip 2) (mkDiscSpec 1) (mkDiscSpec 1) ()))))
         (let* ((($nullVexAppendedTree $nullVexId) (appendChild $tree (mkNodeId $target) (mkNullVex ())))
                (($subtreeAppendedTree $subtreeId) (appendChild $nullVexAppendedTree $nullVexId $subtree))
                ($uid                               (updateID $nullVexId)))
           ($subtreeAppendedTree (mkSSK (mkDiscKnob (mkKnob $uid) (mkMultip 2) (mkDiscSpec 0) (mkDiscSpec 0) ())))))))
