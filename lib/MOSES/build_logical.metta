;;;; build_logical.metta — buildLogical + siblingit (port of metta-moses representation/
;;;; build-logical.metta). The recursive walk that builds logical knobs across a whole
;;;; canonized exemplar: at each AND/OR node add its knobs (addLogicalKnobs), recurse
;;;; into junctor children, and for argument children insert the swapped operator above
;;;; them and add knobs there; finally append a swapped-op child and add knobs to it too.
;;;; Returns (updatedTree mmap).
;;;;
;;;; CORE-DIALECT: siblingit's base `Nil` + recursive `(Cons …)` clauses OVERLAP → folded
;;;; into one guarded clause + decons; tuple-destructures via let*; Cons/Nil → native ().
;;;; buildStrategy (PRIORITIZED-OR game path) sits in an untaken `if` branch for boolean
;;;; nodes, so it stays DEFERRED.

;; siblingit — iterate a node's children, building knobs for each.
(= (siblingit $tree $childrens (mkNodeId $parentId) $childNum $swapedOp $MMap $argLabels)
   (if (== $childrens ())
       ($tree $MMap)
       (let* (($curId (if (== $parentId (0)) ($childNum) (concatT $parentId ($childNum))))
              ($head  (car-atom $childrens))
              ($tail  (cdr-atom $childrens))
              ((mkTree (mkNode $node) $childern) $head)
              (($tNew $mNew)
                 (if (is-member $node (AND OR PRIORITIZED-OR))
                     (if (== $node PRIORITIZED-OR)
                         (buildStrategy $tree (mkNodeId $curId) $MMap $argLabels)
                         (buildLogical  $tree (mkNodeId $curId) $MMap $argLabels))
                     (if (== $swapedOp PRIORITIZED-OR)
                         ($tree $MMap)
                         (let $itree (insertNodeAtPosition $tree (mkNodeId $curId) (mkNode $swapedOp))
                           (if (isAnArgument $node)
                               (addLogicalKnobs $itree (mkNodeId $curId) False $MMap $argLabels)
                               (addLogicalKnobs $itree (mkNodeId $curId) True  $MMap $argLabels))))))
              (($tailT $tailM)
                 (siblingit $tNew $tail (mkNodeId $parentId) (+ $childNum 1) $swapedOp $mNew $argLabels)))
         ($tailT $tailM))))

;; buildLogical — build knobs for the node at $nodeId and (recursively) its subtree.
(= (buildLogical $tree (mkNodeId $nodeId) $MMap $argLabels)
   (let $subtree (getNodeById $tree (mkNodeId $nodeId))
     (if (== True (isNullVertex $subtree))
         ($tree $MMap)
         (let* (((mkTree (mkNode $op) $childrens) $subtree)
                ($swapped (swapAndOr $op))
                (($t1 $mp1) (addLogicalKnobs $tree (mkNodeId $nodeId) True $MMap $argLabels))
                (($updatedTree $updatedMMap)
                   (siblingit $t1 $childrens (mkNodeId $nodeId) 1 $swapped $mp1 $argLabels))
                (($appendedTree $newId)
                   (appendChild $updatedTree (mkNodeId $nodeId) (mkTree (mkNode $swapped) ())))
                (($lastUpdatedTree $lastMp1)
                   (addLogicalKnobs $appendedTree $newId True $updatedMMap $argLabels)))
           ($lastUpdatedTree $lastMp1)))))
