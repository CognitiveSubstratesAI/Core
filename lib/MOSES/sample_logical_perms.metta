;;;; sample_logical_perms.metta — candidate-permutation sampling (port of metta-moses
;;;; representation/sample-logical-perms.metta, logical path). Generates the candidate
;;;; subtree expressions that addLogicalKnobs turns into knobs for an AND/OR node.
;;;;
;;;; 🔶 DELIBERATE DIVERGENCE (documented): upstream selects which pairs become knobs with
;;;; `lazyRandomSelector` (RNG via `py-call random.randint`). This port has NO py-call and
;;;; keeps every test DETERMINISTIC, so selection is the ENUMERATED first $nPairs pairs.
;;;; MOSES correctness does not depend on the randomness (it is a search-DIVERSITY
;;;; heuristic). Core's grounded `random-int` is available if stochastic sampling is
;;;; wanted later — swap it into the $picked binding. The cartesian genPairs
;;;; (`(superpose $list)`×2, which Core cannot fan out) is likewise rewritten as a
;;;; deterministic nested recursion.

;; genPairs — all ordered pairs (x y) with x ≠ y (deterministic; upstream double-superpose).
(= (genPairs $list) (genPairsOuter $list $list))
(= (genPairsOuter $xs $full)
   (if (== $xs ())
       ()
       (concatT (genPairsInner (car-atom $xs) $full) (genPairsOuter (cdr-atom $xs) $full))))
(= (genPairsInner $x $ys)
   (if (== $ys ())
       ()
       (let* (($y (car-atom $ys)) ($rest (genPairsInner $x (cdr-atom $ys))))
         (if (== $x $y) $rest (cons-atom ($x $y) $rest)))))

;; getArgsOne — build one logical expr from the index-pair at position $idx of $PermPairs.
;; (Single-index form of upstream getArgs, which mapped over `(superpose $picked)`.)
(= (getArgsOne $swapedOp $PermPairs $idx $argLabels)
   (let* ((($a $b) (index-atom $PermPairs $idx))
          ($l1 (index-atom $argLabels $a))
          ($l2 (index-atom $argLabels $b)))
     (if (< $b $a) ($swapedOp $l2 $l1) ($swapedOp (NOT $l1) $l2))))

;; sampleLogicalPerms — argLabels ∪ the generated 2-literal permutation expressions.
(= (sampleLogicalPerms $op $arity $argLabels)
   (let* (($swapedOp (swapAndOr $op))
          ($list     (genList (- $arity 1)))
          ($idxPairs (genPairs $list))
          ($nPairs   $arity))
     (if (<= $nPairs 1)
         (let $arg (car-atom $argLabels) ($arg (NOT $arg)))
         (let* (($picked (genList (- $nPairs 1)))
                ($perms  (map-atom $picked $i (getArgsOne $swapedOp $idxPairs $i $argLabels))))
           (concatTuple $argLabels $perms)))))
