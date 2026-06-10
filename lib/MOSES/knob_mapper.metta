;;;; knob_mapper.metta — findDiscKnob (port of metta-moses representation/knob-mapper.metta).
;;;; Looks up the knob anchored at a given NodeId in a representation's KnobMap.
;;;;
;;;; KnobMap shape:  (mkKbMap (mkDscKbMp <Map NodeId→discIdx>) (mkDscMp <MultiMap discIdx→(spec knob)>))
;;;; Returns (knob discIdx) if a knob is anchored at the node, else (() -1).
;;;;
;;;; CORE-DIALECT: the result tuple `((second $pair) $discIdx)` has a non-symbol head
;;;; (a call), so the knob is bound via `chain` before building the tuple.

(= (findDiscKnob (mkKbMap (mkDscKbMp $itDiscKnob) (mkDscMp $disc)) $nodeId)
   (if (== True (Map.contains $nodeId $itDiscKnob))
       (chain (Map.getByKey $nodeId $itDiscKnob) $discIdx
       (chain (MultiMap.getByIdx $discIdx $disc) $discKnobPair
       (chain (second $discKnobPair) $knob
         ($knob $discIdx))))
       (() -1)))
