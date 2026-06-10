;;;; build_knobs.metta — buildKnobs (port of metta-moses representation/build-knobs.metta).
;;;; The knob-building entry point: a PRIORITIZED-OR root takes the strategy path; any
;;;; other (boolean) root is logicalCanonize'd and handed to buildLogical. Returns
;;;; (updatedTree mmap).
;;;;
;;;; CORE-DIALECT: the `let` tree-destructure → let*. buildStrategy (game path) is in an
;;;; untaken branch for boolean roots → DEFERRED.

(= (buildKnobs $exemplar $mmp $argLabels)
   (let* (((mkTree (mkNode $rootOp) $children) $exemplar))
     (if (== $rootOp PRIORITIZED-OR)
         (buildStrategy $exemplar (mkNodeId (0)) $mmp $argLabels)
         (let $canonized (logicalCanonize $exemplar)
           (buildLogical $canonized (mkNodeId (0)) $mmp $argLabels)))))
