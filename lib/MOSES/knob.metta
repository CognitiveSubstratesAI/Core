;;;; knob.metta — knob data-structure layer (port of metta-moses representation/
;;;; knob-representation.metta). The genotype-to-phenotype machinery (build-knobs,
;;;; knob-mapper, representation, getCandidate) all sit on these shapes.
;;;;
;;;; Data shapes (plain constructors — no rules; Core dispatches them by structure):
;;;;   (mkKnob $loc)                                   — a knob located at a NodeId
;;;;   (mkMultip $n)  (mkDiscSpec $n)                  — multiplicity / disc spec wrappers
;;;;   (mkDiscKnob $knob $multip $curr $def $disAll)   — a discrete knob (5-field form;
;;;;       upstream's 2-field (mkDiscKnob $knob $multip) default-expander stays a literal,
;;;;       as it is commented out upstream)
;;;;   (mkLSK $discKnob)  (mkSSK $discKnob)            — logical / strategy subtree knob
;;;;
;;;; CORE-DIALECT notes: untyped (drop upstream `(: …)`); $disAll is a Core-native
;;;; ()-list (upstream Cons/Nil); nodeId< uses let* (not let) for tuple destructure.

;; inExemplar — a knob is OUTSIDE the exemplar iff its default specifier is non-zero.
(= (inExemplar (mkDiscKnob $knob $multiplicity (mkDiscSpec $curr) (mkDiscSpec $def) $dis))
   (not (== $def 0)))

;; getDiscKnob — unwrap the DiscreteKnob from a subtree knob.
(= (getDiscKnob (mkLSK $DiscKnob)) $DiscKnob)
(= (getDiscKnob (mkSSK $DiscKnob)) $DiscKnob)

;; getKnobMultip — the multiplicity of a discrete / logical / strategy knob.
(= (getKnobMultip (mkDiscKnob $knob $multiplicity $curr $def $disAll)) $multiplicity)
(= (getKnobMultip (mkLSK $discKnob)) (getKnobMultip $discKnob))
(= (getKnobMultip (mkSSK $discKnob)) (getKnobMultip $discKnob))

;; getKnobSpec — effective spec = multiplicity minus the count of disallowed specs.
(= (getKnobSpec (mkLSK (mkDiscKnob $knob (mkMultip $multip) $curr $def $dis)))
   (mkDiscSpec (- $multip (List.length $dis))))
(= (getKnobSpec (mkSSK (mkDiscKnob $knob (mkMultip $multip) $curr $def $dis)))
   (mkDiscSpec (- $multip (List.length $dis))))

;; getKnobLoc — the NodeId a knob is anchored at.
(= (getKnobLoc (mkDiscKnob (mkKnob $loc) $multip $curr $def $dis)) $loc)
(= (getKnobLoc (mkLSK $discKnob)) (getKnobLoc $discKnob))
(= (getKnobLoc (mkSSK $discKnob)) (getKnobLoc $discKnob))

;; discSpec< — order DiscSpecs by their wrapped number (a MultiMap comparator).
(= (discSpec< (mkDiscSpec $newKey) (mkDiscSpec $currKey)) (< $newKey $currKey))

;; nodeId< — lexicographic order on NodeId index paths; a prefix precedes its
;; extensions ((2 1) < (2 1 1)). Upstream's three clauses (empty-left → True;
;; empty-right → False; general) OVERLAP on (mkNodeId ()), which Core would
;; double-fire, so they are folded into ONE guarded clause that branches on
;; emptiness in upstream first-match order. The (== $id1 $id2) short-circuit is
;; essential: without it (3)<(3) would recurse to ()<() and wrongly return True.
(= (nodeId< (mkNodeId $id1) (mkNodeId $id2))
   (if (== $id1 ())
       True
       (if (== $id2 ())
           False
           (if (== $id1 $id2)
               False
               (let* ((($headId1 $tailId1) (decons-atom $id1))
                      (($headId2 $tailId2) (decons-atom $id2)))
                 (if (== $headId1 $headId2)
                     (nodeId< (mkNodeId $tailId1) (mkNodeId $tailId2))
                     (< $headId1 $headId2)))))))
