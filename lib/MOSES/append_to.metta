;;;; append_to.metta — appendTo / appendToLSK / appendToSSK (port of metta-moses
;;;; representation/lsk.metta's knob-APPLICATION half, deferred from M1c-2b). Given a knob
;;;; and a setting $d, append the corresponding node into the candidate tree being built:
;;;;   d=2 → negated subtree (NOT …); d=1 → the subtree (present); d=0 → null-vertex (absent).
;;;; Returns (updatedCandidate newSrcId newDstId). Used by getCandidateRec (M1c-3).
;;;;
;;;; CORE-DIALECT fixes (vs upstream):
;;;;   • `(= (mkNodeId (0)) $parentId)` (=-as-equality) → `==`.
;;;;   • NodeId path-append uses concatT, NOT upstream union-atom — union-atom DEDUPLICATES,
;;;;     which corrupts a path that ends in the appended index ((1) ∪ (1) = (1), not (1 1)).
;;;;     concatT is the correct append.
;;;;   • every call nested inside a returned constructor (mkNodeId (concatT …)), (mkTree
;;;;     (getNodeValue …) …)) is let*-bound first — construction does not evaluate elements.
;;;;   • `(let (mkNullVex (Cons $c Nil)) …)` → let*; Cons/Nil → native ().

(= (appendTo $updatedTree (mkLSK $discKnob) $tree $parentId $d)
   (appendToLSK $updatedTree (mkLSK $discKnob) $tree $parentId $d))
(= (appendTo $updatedTree (mkSSK $discKnob) $tree $parentId $d)
   (appendToSSK $updatedTree (mkSSK $discKnob) $tree $parentId $d))

;; ── appendToLSK (boolean: d ∈ {0 absent, 1 present, 2 negated}) ──────────────
(= (appendToLSK $updatedTree $lsk $tree $parentId $d)
   (let* (((mkNodeId $targetId) (getNodeId $lsk))
          ((mkNodeId $dstId)    (if (== (mkNodeId (0)) $parentId) (mkNodeId ()) $parentId))
          ($targetTree (getNodeById $updatedTree (mkNodeId $targetId)))
          ($newPosition (+ (List.length (getChildren (getNodeById $tree $parentId))) 1))
          (($subtree $newSrcId)
             (if (== True (isNullVertex $targetTree))
                 (let* (((mkNullVex ($child)) $targetTree)
                        ($cid (concatT $targetId (1))))
                   ($child (mkNodeId $cid)))
                 ($targetTree (mkNodeId $targetId))))
          ($nodeVal (getNodeValue $subtree)))
     (if (> $d 2)
         (Error $d "Invalid disc specification:- cannot exceed 2.")
         (let* ((($treeToAppend $newDstId)
                   (case $d
                     ((2 (let $dst (mkNodeId (concatT $dstId ($newPosition 1)))
                           ((mkTree (mkNode NOT) ((mkTree $nodeVal ()))) $dst)))
                      (1 (let $dst (mkNodeId (concatT $dstId ($newPosition)))
                           ((mkTree $nodeVal ()) $dst)))
                      (0 ((mkNullVex ($subtree)) $parentId))))))
           (if (isNullVertex $treeToAppend)
               ($tree $parentId $parentId)
               (chain (appendChild $tree $parentId $treeToAppend) $treeChIdPair
                 (let* (($newTree  (first $treeChIdPair))
                        ($finalDst (if (== $parentId $newDstId) (second $treeChIdPair) $newDstId)))
                   ($newTree $newSrcId $finalDst))))))))

;; ── appendToSSK (strategy: d ∈ {0 absent, 1 present}, no negation) ───────────
(= (appendToSSK $updatedTree $ssk $tree $parentId $d)
   (let* (((mkNodeId $targetId) (getNodeId $ssk))
          ((mkNodeId $dstId)    (if (== (mkNodeId (0)) $parentId) (mkNodeId ()) $parentId))
          ($targetTree (getNodeById $updatedTree (mkNodeId $targetId)))
          ($newPosition (+ (List.length (getChildren (getNodeById $tree $parentId))) 1))
          (($subtree $newSrcId)
             (if (== True (isNullVertex $targetTree))
                 (let* (((mkNullVex ($child)) $targetTree)
                        ($cid (concatT $targetId (1))))
                   ($child (mkNodeId $cid)))
                 ($targetTree (mkNodeId $targetId))))
          ($nodeVal (getNodeValue $subtree)))
     (if (> $d 1)
         (Error $d "Invalid disc specification for strategy:- cannot exceed 1.")
         (let* ((($treeToAppend $newDstId)
                   (case $d
                     ((1 (let $dst (mkNodeId (concatT $dstId ($newPosition)))
                           ((mkTree $nodeVal ()) $dst)))
                      (0 ((mkNullVex ($subtree)) $parentId))))))
           (if (isNullVertex $treeToAppend)
               ($tree $parentId $parentId)
               (chain (appendChild $tree $parentId $treeToAppend) $treeChIdPair
                 (let* (($newTree  (first $treeChIdPair))
                        ($finalDst (if (== $parentId $newDstId) (second $treeChIdPair) $newDstId)))
                   ($newTree $newSrcId $finalDst))))))))
