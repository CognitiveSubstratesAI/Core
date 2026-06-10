;;;; multimap.metta — ordered MultiMap ADT (port of metta-moses utilities/ordered-multimap.metta).
;;;; Like map.metta, the ADT (NilMMap | (ConsMMap ($k $v) tail)) survives unchanged
;;;; (Core does multi-clause constructor dispatch); result lists (findAll/values/keys/
;;;; items) are built as Core-native ()-lists, not the upstream Cons/Nil ADT.
;;;; A MultiMap keeps DUPLICATE keys (ordered), unlike map.metta's Map.
;;;;
;;;; Higher-order note: MultiMap.insert takes a comparator BY NAME ($fn) and applies
;;;; ($fn k k'). This works in Core now that bare function symbols are no longer
;;;; eagerly reduced (eval fix 460e264) — grounded `<=` and MeTTa-defined `discSpec<`/
;;;; `nodeId<` (knob.metta) all pass through and reduce when applied to concrete args.

;; insert with a custom ordering predicate (insert before the first elem it precedes).
(= (MultiMap.insert ($key $value) NilMMap $fn) (ConsMMap ($key $value) NilMMap))
(= (MultiMap.insert ($key $value) (ConsMMap ($curKey $curVal) $tail) $fn)
   (if ($fn $key $curKey)
       (ConsMMap ($key $value) (ConsMMap ($curKey $curVal) $tail))
       (ConsMMap ($curKey $curVal) (MultiMap.insert ($key $value) $tail $fn))))

;; insert with default <= ordering.
(= (MultiMap.insert $newValue $mMap) (MultiMap.insert $newValue $mMap <=))

;; get the ($k $v) pair at 0-based index.
(= (MultiMap.getByIdx $idx NilMMap) (Error NilMMap (Can't find $idx)))
(= (MultiMap.getByIdx $idx (ConsMMap $x $xs))
   (if (== $idx 0) $x (MultiMap.getByIdx (- $idx 1) $xs)))

;; first / all values for a key.
(= (MultiMap.findOne $key NilMMap) (Error $key "not found"))
(= (MultiMap.findOne $key (ConsMMap ($curKey $curVal) $tail))
   (if (== $key $curKey) $curVal (MultiMap.findOne $key $tail)))

(= (MultiMap.findAll $key NilMMap) ())
(= (MultiMap.findAll $key (ConsMMap ($curKey $curVal) $tail))
   (if (== $key $curKey)
       (cons-atom $curVal (MultiMap.findAll $key $tail))
       (MultiMap.findAll $key $tail)))

;; membership / value-presence / element-presence.
(= (MultiMap.contains $key NilMMap) False)
(= (MultiMap.contains $key (ConsMMap ($curKey $curVal) $tail))
   (if (== $key $curKey) True (MultiMap.contains $key $tail)))

(= (MultiMap.checkValue $value NilMMap) False)
(= (MultiMap.checkValue $value (ConsMMap ($curKey $curVal) $tail))
   (if (== $value $curVal) True (MultiMap.checkValue $value $tail)))

(= (MultiMap.checkElement $element NilMMap) False)
(= (MultiMap.checkElement $element (ConsMMap $head $tail))
   (if (== $element $head) True (MultiMap.checkElement $element $tail)))

;; remove first / all pairs for a key.
(= (MultiMap.removeOne $key NilMMap) (Error $key "not found"))
(= (MultiMap.removeOne $key (ConsMMap ($curKey $curVal) $tail))
   (if (== $key $curKey)
       $tail
       (chain (MultiMap.removeOne $key $tail) $res
          (if-error $res $res (ConsMMap ($curKey $curVal) $res)))))

(= (MultiMap.removeAll $key NilMMap) NilMMap)
(= (MultiMap.removeAll $key (ConsMMap ($curKey $curVal) $tail))
   (if (== $key $curKey)
       (MultiMap.removeAll $key $tail)
       (ConsMMap ($curKey $curVal) (MultiMap.removeAll $key $tail))))

;; projections — native ()-lists.
(= (MultiMap.values NilMMap) ())
(= (MultiMap.values (ConsMMap ($key $value) $tail)) (cons-atom $value (MultiMap.values $tail)))

(= (MultiMap.keys NilMMap) ())
(= (MultiMap.keys (ConsMMap ($key $value) $tail)) (cons-atom $key (MultiMap.keys $tail)))

(= (MultiMap.items NilMMap) ())
(= (MultiMap.items (ConsMMap $pair $tail)) (cons-atom $pair (MultiMap.items $tail)))

(= (MultiMap.length NilMMap) 0)
(= (MultiMap.length (ConsMMap ($curKey $curVal) $tail)) (+ 1 (MultiMap.length $tail)))

;; order-independent equality (faithful 1:1 — only the empty-base pattern is adapted
;; from upstream's `()` to the NilMMap terminal that this ADT actually ends in).
(= (MultiMap.equals NilMMap $mm2) False)
(= (MultiMap.equals (ConsMMap $x $xs) $mm2)
   (if (== (MultiMap.length (ConsMMap $x $xs)) (MultiMap.length $mm2))
       (if (MultiMap.checkElement $x $mm2) True (MultiMap.equals $xs $mm2))
       False))
