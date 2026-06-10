;;;; tree.metta — program-representation Tree substrate (port of metta-moses
;;;; utilities/tree.metta + utilities/nodeId.metta) into Core's native-list dialect.
;;;;
;;;; A Tree is  (mkTree (mkNode $value) $children)  or  (mkNullVex $children),
;;;; where $children is a Core-NATIVE ()-list of Trees: the empty child-list is `()`
;;;; (upstream `Nil`) and a populated one is `(t1 t2 …)` (upstream `(Cons t1 (Cons t2 …))`).
;;;; A NodeId is  (mkNodeId $path)  where $path is a native ()-tuple of 1-based child
;;;; indices; `(0)` denotes the root.
;;;;
;;;; CORE-DIALECT adaptations vs upstream:
;;;;   • children Cons/Nil → native ()-list; List.listToExpr DROPPED (it is identity here).
;;;;   • (compose not isUnit) → named predicate isNotUnit (Core does not auto-curry).
;;;;   • LIST-structure clause splits (… Nil) vs (… (Cons …)) folded into ONE guarded
;;;;     clause + `if (== $children ())`; CONSTRUCTOR splits (mkTree vs mkNullVex) kept
;;;;     as separate clauses (Core dispatches mutually-exclusive constructors fine).
;;;;   • applyGetNodeId arg order flipped to (state elem) to match Core's List.foldl
;;;;     (accumulator-first), vs upstream's (elem acc) foldl.
;;;;   • cleanTree NOW WIRED (M6-5): preOrder → reduce-to (boolean ENF) → buildTree.
;;;;     reduce-to lives in reduce_to_elegance.metta (loaded after this file; resolved at
;;;;     call time). Still DEFERRED: preOrderDebug; extractArgs / treeFtsIndices /
;;;;     pruneExemplar / removeLiteral / alphabetSize (feature-selection + ITable, M1c-FS / M7).

;; ── node value / children accessors ──────────────────────────────────────────
(= (getNodeValue (mkNullVex $xs)) (Error (mkNullVex $xs) "Null Vertex has no value"))
(= (getNodeValue (mkTree $nodeValue $chl)) $nodeValue)

(= (getChildren (mkTree (mkNode $r) $children)) $children)
(= (getChildren (mkNullVex $children)) $children)

(= (updateChildren (mkTree (mkNode $r) $oldChildren) $newChildren)
   (mkTree (mkNode $r) $newChildren))
(= (updateChildren (mkNullVex $oldChildren) $newChildren)
   (mkNullVex $newChildren))

;; ── preOrder: Tree → native S-expression program ─────────────────────────────
;; Leaf AND/OR is wrapped as (AND)/(OR) (an empty junctor application); other leaves
;; stay bare. () results from null vertices are filtered out of a node's child list.
(= (preOrder (mkNullVex $knobs)) ())
(= (preOrder (mkTree (mkNode $r) $children))
   (if (== $children ())
       (if (is-member $r (AND OR)) ($r) $r)
       (let* (($lc  (map-atom $children $c (preOrder $c)))
              ($lc' (filter-atom $lc $e (isNotUnit $e)))
              ($exp (cons-atom $r $lc')))
         $exp)))

;; ── buildTree: native S-expression program → Tree ────────────────────────────
(= (buildTree $expr)
   (if (== (get-metatype $expr) Expression)
       (let* ((($head $tail) (decons-atom $expr))
              ($children (map-atom $tail $t (buildTree $t))))
         (mkTree (mkNode $head) $children))
       (mkTree (mkNode $expr) ())))

;; ── NodeId traversal (nodeId.metta) ──────────────────────────────────────────
;; getLevelById — the subtree one level down: 0 = the node itself, k = its (k-1)-th child.
(= (getLevelById (mkTree (mkNode $r) $children) $levelId)
   (if (== $levelId 0)
       (mkTree (mkNode $r) $children)
       (List.getByIdx $children (- $levelId 1))))
(= (getLevelById (mkNullVex $children) $levelId)
   (if (== $levelId 0)
       (mkNullVex $children)
       (List.getByIdx $children (- $levelId 1))))
(= (getLevelById () $levelId) ())

;; getNodeById — walk a NodeId path to its subtree. Single guarded clause (the
;; upstream (mkNodeId ()) base case is folded in via `if (== $id ())` to avoid the
;; (mkNodeId ()) / (mkNodeId $id) clause overlap that Core's rewriter would double-fire).
(= (getNodeById $tree (mkNodeId $id))
   (if (== $id ())
       $tree
       (let* ((($head $tail) (decons-atom $id))
              ($level (getLevelById $tree $head)))
         (if (== $tail ())
             $level
             (let* ((($nextHead $nextTail) (decons-atom $tail))
                    ($nextLevel (getLevelById $level $nextHead)))
               (getNodeById $nextLevel (mkNodeId $nextTail)))))))

;; ── reverse lookup: Tree → NodeId ────────────────────────────────────────────
(= (getNodeId $tree $targetTree) (getNodeId $tree $targetTree (mkNodeId (0))))
(= (getNodeId $tree $targetTree (mkNodeId $parentIdx))
   (if (== $tree $targetTree)
       (mkNodeId $parentIdx)
       (let* (($children (getChildren $tree))
              ($targetIdx (List.index $children $targetTree)))
         (if (== $targetIdx -1)
             (let* (($init  ($targetTree (mkNodeId $parentIdx) (mkNodeId (-1)) 1))
                    ($state (foldl-atom $children $init $st $ct (applyGetNodeId $st $ct)))
                    (($_ $__ $nodeId $iter) $state))
               $nodeId)
             (let $pos (+ 1 $targetIdx)
               (if (== $parentIdx (0))
                   (mkNodeId ($pos))
                   (mkNodeId (concatT $parentIdx ($pos)))))))))

;; applyGetNodeId — foldl step (state-first, to match Core's List.foldl). Once a
;; non-(-1) id is found it is carried unchanged; otherwise it recurses into the
;; current child at depth $iter and prefixes the parent path.
;; $iter1 is bound via let* (which evaluates) so the iteration counter stays a clean
;; number across fold steps — placing (+ 1 $iter) directly in a result tuple would
;; accumulate as unevaluated (+ 1 (+ 1 …)) (list construction does not evaluate elements).
(= (applyGetNodeId ($targetTree (mkNodeId $parentIdx) $accId $iter) $currTree)
   (let* (($iter1 (+ 1 $iter)))
     (if (== $accId (mkNodeId (-1)))
         (chain (getNodeId $currTree $targetTree (mkNodeId ($iter))) $nodeId
           (let* (((mkNodeId $idx) $nodeId))
             (if (== $idx (-1))
                 ($targetTree (mkNodeId $parentIdx) $nodeId $iter1)
                 (let* (($newId (if (== $parentIdx (0))
                                    (mkNodeId $idx)
                                    (mkNodeId (concatT $parentIdx $idx)))))
                   ($targetTree $nodeId $newId $iter1)))))
         ($targetTree (mkNodeId $parentIdx) $accId $iter1))))

;; getSubtreeId — id of $subtree among the children of the node at $targetId.
(= (getSubtreeId $tree (mkNodeId $targetId) $subtree $iter)
   (let* (($targetNode (getNodeById $tree (mkNodeId $targetId)))
          ($children   (getChildren $targetNode))
          ($currNode   (List.getByIdx $children $iter)))
     (if (== $currNode $subtree)
         (let* (($pos         (+ $iter 1))
                ($idOfSubtree (concatT $targetId ($pos))))
           (mkNodeId $idOfSubtree))
         (getSubtreeId $tree (mkNodeId $targetId) $subtree (+ $iter 1)))))

;; getChildrenById — children of the node at a given NodeId.
(= (getChildrenById $tree (mkNodeId $id))
   (let $targetNode (getNodeById $tree (mkNodeId $id))
     (getChildren $targetNode)))

;; insertAbove — wrap $tree under a new root $node (as its only child).
(= (insertAbove $tree $node) (mkTree $node ($tree)))

;; replaceNodeById — replace the subtree at $id with $newSubtree.
(= (replaceNodeById $tree (mkNodeId $id) $newSubtree)
   (if (or (== $id ()) (== (mkNodeId $id) (mkNodeId (0))))
       $newSubtree
       (let* (($headId       (car-atom $id))
              ($tailId       (cdr-atom $id))
              ($children     (getChildren $tree))
              ($childToUpdate (List.getByIdx $children (- $headId 1)))
              ($updatedChild (if (== $tailId ())
                                 $newSubtree
                                 (replaceNodeById $childToUpdate (mkNodeId $tailId) $newSubtree)))
              ($newChildren  (List.replaceAt $children (- $headId 1) $updatedChild)))
         (updateChildren $tree $newChildren))))

;; appendChild — append $child under the node at $target; returns (updatedTree childId).
(= (appendChild (mkNullVex $nvch) $targetId $child)
   (if (== $nvch ())
       ($child (mkNodeId (0)))
       (Error (mkNullVex $nvch) "Null vertex can't have more than one child")))
(= (appendChild (mkTree $node $children) (mkNodeId $target) $child)
   (let* (($tree               (mkTree $node $children))
          ($targetNode         (getNodeById $tree (mkNodeId $target)))
          ($childrenTgt        (getChildren $targetNode))
          ($updatedChildrenTgt (List.append $child $childrenTgt))
          ($childIndex         (List.length $updatedChildrenTgt))
          ($idOfChild          (if (== (mkNodeId $target) (mkNodeId (0)))
                                   ($childIndex)
                                   (concatT $target ($childIndex))))
          ($newTargetSubtree   (updateChildren $targetNode $updatedChildrenTgt))
          ($updatedTree        (replaceNodeById $tree (mkNodeId $target) $newTargetSubtree)))
     ($updatedTree (mkNodeId $idOfChild))))

;; getChildrenByIdx — the $idx-th child of a node.
(= (getChildrenByIdx $tree $idx)
   (case $tree
     (((mkTree (mkNode $r) $childrenTgt) (List.getByIdx $childrenTgt $idx))
      ((mkNullVex $childrenTgt)          (List.getByIdx $childrenTgt $idx))
      ($else (Error (Node not found or invalid))))))

;; insertNodeAtPosition — splice a new node above the node at $id.
(= (insertNodeAtPosition $tree (mkNodeId $id) $newNode)
   (if (or (== $id ()) (== (mkNodeId $id) (mkNodeId (0))))
       (mkTree $newNode ($tree))
       (let* (($oldNode    (getNodeById $tree (mkNodeId $id)))
              ($newSubtree (mkTree $newNode ($oldNode))))
         (replaceNodeById $tree (mkNodeId $id) $newSubtree))))

;; ── predicates / complexity ──────────────────────────────────────────────────
(= (isEmpty $tree)
   (case $tree (((mkNullVex ()) True) ($else False))))

(= (isNullVertex $tree)
   (case $tree (((mkNullVex $children) True) ($else False))))

;; an argument is anything that is neither a junctor nor a null vertex.
(= (isArgument (mkNullVex $x)) False)
(= (isArgument (mkTree (mkNode $x) $children))
   (and (not (is-member $x (AND OR NOT PRIORITIZED-OR))) (== $children ())))

;; treeComplexity — count of argument leaves (junctors/null-vertices cost 0).
(= (treeComplexity (mkNullVex $x)) 0)
(= (treeComplexity (mkTree (mkNode $a) $children))
   (if (isArgument (mkTree (mkNode $a) $children))
       1
       (List.sum (map-atom $children $c (treeComplexity $c)))))

;; cleanTree — reduce a program Tree to elegant normal form: serialize to an
;; S-expression (preOrder), run the boolean-reduct engine (reduce-to), rebuild the
;; Tree (buildTree). reduce-to is defined in reduce_to_elegance.metta (loaded after
;; this file; resolved at call time). [M6-5 — un-deferred now the reduct engine exists.]
(= (cleanTree $tree)
   (let* (($preordered (preOrder $tree))
          ($reduced    (reduce-to $preordered)))
     (buildTree $reduced)))
