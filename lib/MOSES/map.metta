;;;; map.metta — ordered assoc-Map ADT (port of metta-moses utilities/map.metta).
;;;; A Map is its own ADT: NilMap | (ConsMap ($k $v) tail). This ADT survives the
;;;; Core port unchanged because Core supports multi-clause CONSTRUCTOR dispatch
;;;; (NilMap vs (ConsMap …) are mutually exclusive — no overlap). What DOES change:
;;;; result lists (values/keys/items) are built as Core-native ()-lists via cons-atom,
;;;; not the upstream Cons/Nil ADT. Functions UNTYPED (Core dialect).

;; insertCounter — insert key with count 1, or bump an existing key's count.
(= (Map.insertCounter $key NilMap) (ConsMap ($key 1) NilMap))
(= (Map.insertCounter $key (ConsMap ($curKey $curVal) $tail))
   (if (== $key $curKey)
       (ConsMap ($curKey (+ $curVal 1)) $tail)
       (if (< $key $curKey)
           (ConsMap ($key 1) (ConsMap ($curKey $curVal) $tail))
           (ConsMap ($curKey $curVal) (Map.insertCounter $key $tail)))))

;; insert with custom (equality, less-than) comparators.
(= (Map.insert ($key $value) NilMap $fEq $fLt) (ConsMap ($key $value) NilMap))
(= (Map.insert ($key $value) (ConsMap ($curKey $curVal) $tail) $fEq $fLt)
   (if ($fEq $key $curKey)
       (ConsMap ($key $value) $tail)
       (if ($fLt $key $curKey)
           (ConsMap ($key $value) (ConsMap ($curKey $curVal) $tail))
           (ConsMap ($curKey $curVal) (Map.insert ($key $value) $tail $fEq $fLt)))))

;; insert with default ==/< ordering.
(= (Map.insert ($key $value) NilMap) (ConsMap ($key $value) NilMap))
(= (Map.insert ($key $value) (ConsMap ($curKey $curVal) $tail))
   (if (== $key $curKey)
       (ConsMap ($key $value) $tail)
       (if (< $key $curKey)
           (ConsMap ($key $value) (ConsMap ($curKey $curVal) $tail))
           (ConsMap ($curKey $curVal) (Map.insert ($key $value) $tail)))))

;; lookup value by key.
(= (Map.getByKey $key NilMap) (Error $key "not found"))
(= (Map.getByKey $key (ConsMap ($curKey $curVal) $tail))
   (if (== $key $curKey) $curVal (Map.getByKey $key $tail)))

;; get the ($k $v) pair at 0-based index.
(= (Map.getByIdx NilMap $i) (Error NilMap "Index out of bounds"))
(= (Map.getByIdx (ConsMap $x $xs) $i)
   (if (== $i 0) $x (Map.getByIdx $xs (- $i 1))))

;; membership / value-presence.
(= (Map.contains $key NilMap) False)
(= (Map.contains $key (ConsMap ($curKey $curVal) $tail))
   (if (== $key $curKey) True (Map.contains $key $tail)))

(= (Map.checkValue $value NilMap) False)
(= (Map.checkValue $value (ConsMap ($curKey $curVal) $tail))
   (if (== $value $curVal) True (Map.checkValue $value $tail)))

;; remove a key (Error if absent; propagated through the tail via if-error).
(= (Map.remove $key NilMap) (Error $key "not found"))
(= (Map.remove $key (ConsMap ($curKey $curVal) $tail))
   (if (== $key $curKey)
       $tail
       (chain (Map.remove $key $tail) $res
          (if-error $res $res (ConsMap ($curKey $curVal) $res)))))

;; projections — native ()-lists (upstream returned the Cons/Nil ADT).
(= (Map.values NilMap) ())
(= (Map.values (ConsMap ($key $value) $tail)) (cons-atom $value (Map.values $tail)))

(= (Map.keys NilMap) ())
(= (Map.keys (ConsMap ($key $value) $tail)) (cons-atom $key (Map.keys $tail)))

(= (Map.items NilMap) ())
(= (Map.items (ConsMap $pair $tail)) (cons-atom $pair (Map.items $tail)))

(= (Map.length NilMap) 0)
(= (Map.length (ConsMap ($curKey $curVal) $tail)) (+ 1 (Map.length $tail)))

;; find — 0-based index of a key, or -1.
(= (Map.find NilMap $k) -1)
(= (Map.find (ConsMap ($curKey $curVal) $xs) $k')
   (if (== $curKey $k')
       0
       (chain (Map.find $xs $k') $targetIdx
          (if (== $targetIdx -1) $targetIdx (+ 1 $targetIdx)))))
