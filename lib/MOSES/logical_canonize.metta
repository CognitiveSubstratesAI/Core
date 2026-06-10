;;;; logical_canonize.metta — exemplar canonicalization (port of metta-moses
;;;; representation/logical-canonize.metta). buildKnobs canonizes a boolean exemplar
;;;; before building logical knobs: every node is wrapped so an AND sits under an OR
;;;; (and vice-versa), giving a uniform alternating-junctor shape for knob insertion.
;;;;
;;;; CORE-DIALECT: untyped; child lists are native ()-lists (upstream `(Cons x Nil)`
;;;; → `(x)`); `case` symbol-literal dispatch + `$_` default (first-match order).
;;;; Reduct-free — unlike the knob-CONSTRUCTION layer (lsk/logicalProbe/build-logical),
;;;; which needs cleanTree → the reduct engine (M6).

;; logicalCanonize — wrap a node's subtree under its dual junctor.
;;   AND/argument → wrapped under OR-of(…) is NOT it; per upstream: AND→OR, OR/NOT→AND,
;;   argument→AND, boolean→(OR (AND)), anything else → Error.
(= (logicalCanonize (mkTree (mkNode $it) $children))
   (case $it
     ((AND (mkTree (mkNode OR)  ((mkTree (mkNode $it) $children))))
      (OR  (mkTree (mkNode AND) ((mkTree (mkNode $it) $children))))
      (NOT (mkTree (mkNode AND) ((mkTree (mkNode $it) $children))))
      ($_ (if (isAnArgument $it)
              (mkTree (mkNode AND) ((mkTree (mkNode $it) $children)))
              (if (isBoolean $it)
                  (mkTree (mkNode OR) ((mkTree (mkNode AND) ())))
                  (Error InvalidTreeValueInsideLogicalCanonize)))))))

;; isAnArgument — a bare input literal: not a junctor, and a plain Symbol.
(= (isAnArgument $it) (and (not (is-member $it (AND OR NOT))) (== (get-metatype $it) Symbol)))

;; isBoolean — a boolean constant True / False.
(= (isBoolean $it) (is-member $it (True False)))
