;;;; get_candidate.metta — getCandidate / getCandidateRec / applyGetCandidateRec
;;;; (port of metta-moses representation/representation.metta). THE genotype→phenotype
;;;; keystone: convert a genotype Instance (knob settings) into a candidate program Tree by
;;;; walking the representation's exemplar tree and, at each knob-anchored node, applying the
;;;; instance's setting (present / negated / absent) via appendTo; nodes without a knob are
;;;; copied. The boolean result is run through cleanTree (M6 reduct); the game result through
;;;; preOrder∘buildTree.
;;;;
;;;; CORE-DIALECT: the applyGetCandidateRec fold uses foldl-atom (so applyGetCandidateRec is
;;;; state-first, not upstream's elem-first List.foldl); `(+ 1 $chIdx)` is let*-bound because it
;;;; sits in a result tuple whose head is a non-symbol var (Core won't evaluate such a tuple's
;;;; elements). (mkTree (getNodeValue …) …) IS fine — mkTree is a symbol head. Cons/Nil → ().

(= (getCandidate $repObj $inst)
   (let* (($parentid (mkNodeId (0)))
          ($srcid    (mkNodeId (0)))
          ((mkRep $kmo $tr) $repObj)
          ($candidate (getCandidateRec $repObj $inst $parentid $srcid $parentid (mkNullVex ())))
          ($rootNode  (getNodeById (getRepTree $repObj) $srcid))
          ($rootValue (getNodeValue $rootNode))
          ($rootSymbol (if (== (get-metatype $rootValue) Expression)
                           (car-atom (cdr-atom $rootValue))
                           $rootValue))
          ($isGameStrategy (== $rootSymbol PRIORITIZED-OR)))
     (if $isGameStrategy
         (buildTree (preOrder $candidate))
         (cleanTree $candidate))))

;; getCandidateRec — walk the rep's exemplar from $srcId, threading the candidate built so far.
(= (getCandidateRec (mkRep $knobMapObj $tree) (mkInst $inst) $parentId $srcId $dstId $candidate)
   (let $knobIdxPair (findDiscKnob $knobMapObj $srcId)
      (if (not (== (second $knobIdxPair) -1))
          ;; KNOB at this node — apply the instance's setting.
          (let* (($d      (List.getByIdx $inst (second $knobIdxPair)))
                 ($result (appendTo $tree (first $knobIdxPair) $candidate $dstId $d))
                 (($updatedCnd $newSrcId $newDstId) $result))
             (if (== $updatedCnd $candidate)
                 $updatedCnd
                 (let* (($src1        (getNodeById $tree $newSrcId))
                        ($srcchildren1 (getChildren $src1))
                        ($init1       ((mkRep $knobMapObj $tree) (mkInst $inst) $newSrcId $newDstId $updatedCnd 1))
                        ($state1      (foldl-atom $srcchildren1 $init1 $acc $ct (applyGetCandidateRec $acc $ct)))
                        (((mkRep $kmo1 $tr1) (mkInst $i1) $p1 $dd1 $finalcnd1 $dx1) $state1))
                   $finalcnd1)))
          ;; NO KNOB — copy the exemplar node into the candidate, recurse into its children.
          ;; first/second of the append result are bound BEFORE the init tuple: the init's
          ;; head is a non-symbol (mkRep …), so Core would NOT evaluate (first …)/(second …)
          ;; inside it, and applyGetCandidateRec's (mkNodeId $dstId) pattern would then fail to
          ;; match the unevaluated (second …), making the fold nest unevaluated calls.
          (let* (($src        (getNodeById $tree $srcId))
                 ($cndchidpair (appendChild $candidate $dstId (mkTree (getNodeValue $src) ())))
                 ($cndFirst   (first $cndchidpair))
                 ($cndSecond  (second $cndchidpair))
                 ($srcchildren (getChildren $src))
                 ($init       ((mkRep $knobMapObj $tree) (mkInst $inst) $srcId $cndSecond $cndFirst 1))
                 ($state      (foldl-atom $srcchildren $init $acc $ct (applyGetCandidateRec $acc $ct)))
                 (((mkRep $kmo $tr) (mkInst $i) $np $nd $finalcnd $d) $state))
              $finalcnd))))

;; applyGetCandidateRec — foldl step (state-first): compute the next srcId from the child
;; index, recurse getCandidateRec, bump the index. The child tree itself is unused (the walk
;; addresses nodes by NodeId in the rep tree, not by the passed child).
(= (applyGetCandidateRec ($repObj $inst (mkNodeId $parentId) (mkNodeId $dstId) $candidate $chIdx) $tr)
   (let* (($srcId (if (== $parentId (0))
                      (mkNodeId ($chIdx))
                      (mkNodeId (concatT $parentId ($chIdx)))))
          ($updatedCnd1 (getCandidateRec $repObj $inst (mkNodeId $parentId) $srcId (mkNodeId $dstId) $candidate))
          ($nextIdx     (+ 1 $chIdx)))
     ($repObj $inst (mkNodeId $parentId) (mkNodeId $dstId) $updatedCnd1 $nextIdx)))
