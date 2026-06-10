;;;; representation.metta — the representation constructor (port of metta-moses
;;;; representation/representation.metta, the SIMPLE exemplar→knobs variant). Builds a
;;;; Representation: (mkRep (mkKbMap (mkDscKbMp <Map NodeId→discIdx>) (mkDscMp <knob MultiMap>))
;;;; treeWithKnobs). buildKnobs produces the knob MultiMap + the knob-instrumented tree;
;;;; crtDiscKnobMap indexes each knob by its anchor NodeId.
;;;;
;;;; DEFERRED (later phases): the $nDeme game ctor (uses range/superpose/collapse) and the
;;;; feature-selection ctor (ITable / featureSelector / pruneExemplar — M1c-FS / M7).

;; crtDiscKnobMap — index the knob MultiMap as a NodeId→discIdx Map (ordered by nodeId<).
(= (crtDiscKnobMap (mkDscMp NilMMap) (mkDscKbMp $dkm) $index) (mkDscKbMp $dkm))
(= (crtDiscKnobMap (mkDscMp (ConsMMap ($kbSpec $kb) $tail)) (mkDscKbMp $dkm) $index)
   (let* (($loc        (getKnobLoc $kb))
          ($updatedDkm (Map.insert ($loc $index) $dkm == nodeId<)))
     (crtDiscKnobMap (mkDscMp $tail) (mkDscKbMp $updatedDkm) (+ $index 1))))

;; representation — build a Representation around an exemplar with the given arg labels.
(= (representation $exemplar $argLabels)
   (let* ((($updatedTree $dscMp) (buildKnobs $exemplar NilMMap $argLabels))
          ($dscKbMp (crtDiscKnobMap (mkDscMp $dscMp) (mkDscKbMp NilMap) 0)))
     (mkRep (mkKbMap $dscKbMp (mkDscMp $dscMp)) $updatedTree)))

;; getRepTree — the knob-instrumented exemplar tree of a Representation.
(= (getRepTree (mkRep $knobMapObj $tree)) $tree)
