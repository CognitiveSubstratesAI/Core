;;;; deme.metta — the deme layer foundation (port of metta-moses deme/expand-deme.metta's
;;;; instance-generation core). A Deme is (mkDeme representation scoredInstanceSet demeId) —
;;;; a population of program Instances sharing one representation. The starting genotype is
;;;; createInitialInstance: every knob at its default setting (= the exemplar itself).
;;;;
;;;; CORE-DIALECT: `(List.map getKnobDefault …)` → grounded `(map-atom … (getKnobDefault …))`
;;;; (the higher-order List.map idiom is dead in Core).
;;;;
;;;; DEFERRED: createDeme/createDemeIds (depend on the FS createRepresentation + py-call
;;;; numStr), and the expandDeme orchestrator (needs scoring + optimizer + metapopulation).

;; getKnobDefault — a knob's default disc setting (the 4th DiscSpec field).
(= (getKnobDefault (mkLSK (mkDiscKnob $knob $multip $curr (mkDiscSpec $def) $dis))) $def)
(= (getKnobDefault (mkSSK (mkDiscKnob $knob $multip $curr (mkDiscSpec $def) $dis))) $def)

;; createInitialInstance — the default genotype: each knob (from the knob MultiMap) at its
;; default. Maps to the exemplar program via getCandidate.
(= (createInitialInstance $dscMp)
   (let* (($knobs    (MultiMap.values $dscMp))
          ($defaults (map-atom $knobs $k (getKnobDefault $k))))
     $defaults))

;; repInitialInstance — convenience: the initial Instance for a representation.
(= (repInitialInstance (mkRep (mkKbMap $kb (mkDscMp $dscMp)) $tree))
   (mkInst (createInitialInstance $dscMp)))
