;;;; add_logical_knobs.metta — addLogicalKnobs (port of metta-moses representation/
;;;; add-logical-knobs.metta). For one node of the exemplar: generate candidate
;;;; permutations (sampleLogicalPerms), build a knob per candidate (logicalProbe), pair
;;;; each knob with its disc spec, and fold them into the running knob MultiMap.
;;;; Returns (updatedTree mmap).
;;;;
;;;; CORE-DIALECT: the pair template `((getKnobSpec $knob) $knob)` has a non-symbol head
;;;; (a call) so Core won't evaluate the spec in a map-atom body — extracted into pairOne
;;;; (let-bound spec). The PRIORITIZED-OR game branch (sampleStrategyPerms) sits in an
;;;; untaken `if` for boolean AND/OR nodes, so it stays DEFERRED (sampleStrategyPerms /
;;;; getAllGameMoves not yet ported — strategyProbe IS).

;; pairOne / pairKnobWithSpec — tag each knob with its disc spec: knob → (spec knob).
(= (pairOne $knob) (let $spec (getKnobSpec $knob) ($spec $knob)))
(= (pairKnobWithSpec $tuple) (map-atom $tuple $knob (pairOne $knob)))

;; getAllGameMoves — the strategy-move alphabet (game path; here for completeness).
(= (getAllGameMoves) (playcenter playblock playwin playcorner playside))

;; addLogicalKnobs — build + collect the knobs for the node at $nodeId.
(= (addLogicalKnobs $exemplar $nodeId $addIfInExemplar $map $argLabels)
   (let* (((mkTree (mkNode $op) $children) (getNodeById $exemplar $nodeId))
          ($labels        (if (== $op PRIORITIZED-OR) (getAllGameMoves) $argLabels))
          ($lengthOfArgs  (length $labels))
          ($perms         (if (== $op PRIORITIZED-OR)
                              (sampleStrategyPerms $op $lengthOfArgs $labels)
                              (sampleLogicalPerms $op $lengthOfArgs $labels)))
          ($treePerms     (map-atom $perms $perm (buildTree $perm)))
          (($knobs $updatedTree)
                          (if (== $op PRIORITIZED-OR)
                              (strategyProbe $exemplar $nodeId $treePerms $addIfInExemplar ())
                              (logicalProbe  $exemplar $nodeId $treePerms $addIfInExemplar ())))
          ($pairs         (pairKnobWithSpec $knobs))
          ($mmp           (expToMMap $pairs $map discSpec<))
          ($temp          (cut)))
     ($updatedTree $mmp)))
