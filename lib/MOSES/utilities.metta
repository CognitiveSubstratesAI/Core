;;;; utilities.metta — list helpers, ported from metta-moses utilities/list-methods.metta
;;;; into Core's NATIVE list idiom: a list is a `()`-expression; recursion is a single
;;;; guarded clause + `if (== $xs ())` over car-atom/cdr-atom (NOT the upstream Cons/Nil
;;;; ADT, which clashes with Core's `Nil = Expression`). Functions UNTYPED (Core dialect).

;; List.foldl f acc (x1 x2 …) = (f (… (f (f acc x1) x2) …) xn)
(= (List.foldl $f $acc $xs)
   (if (== $xs ())
       $acc
       (List.foldl $f ($f $acc (car-atom $xs)) (cdr-atom $xs))))

;; List.foldr f z (x1 … xn) = (f x1 (f x2 (… (f xn z))))
(= (List.foldr $f $z $xs)
   (if (== $xs ())
       $z
       ($f (car-atom $xs) (List.foldr $f $z (cdr-atom $xs)))))

;; List.length
(= (List.length $xs)
   (if (== $xs ())
       0
       (+ 1 (List.length (cdr-atom $xs)))))

;; NOTE — NO higher-order List.map / List.filter here. Core EAGERLY reduces a bare
;; MeTTa-defined function symbol passed as an argument (e.g. `dbl` → `(* $x 2)` with
;; $x unbound) AND does not apply a variable-headed `($f x)`. So the upstream
;; (List.map $f $xs) idiom is dead-on-arrival. Use Core's GROUNDED template ops at
;; the call site instead — they bind a fresh var per element and evaluate a template
;; whose function head is a concrete symbol:
;;     (map-atom    $xs $x (f $x))
;;     (filter-atom $xs $x (pred $x))
;;     (foldl-atom  $xs $init $acc $x (combine $acc $x))
;; (List.foldl/List.foldr below stay usable ONLY with GROUNDED combiners like + .)

;; List.getByIdx (0-based)
(= (List.getByIdx $xs $i)
   (if (== $i 0)
       (car-atom $xs)
       (List.getByIdx (cdr-atom $xs) (- $i 1))))

;; List.sum / List.member
(= (List.sum $xs) (List.foldl + 0 $xs))
(= (List.member $x $xs)
   (if (== $xs ())
       False
       (if (== $x (car-atom $xs)) True (List.member $x (cdr-atom $xs)))))

;; List.index — 0-based index of the first $target, or -1 if absent.
(= (List.index $xs $target)
   (if (== $xs ())
       -1
       (if (== (car-atom $xs) $target)
           0
           (chain (List.index (cdr-atom $xs) $target) $idx
              (if (< $idx 0) $idx (+ 1 $idx))))))

;; List.append — append a single element to the END of a list.
(= (List.append $val $xs)
   (if (== $xs ())
       (cons-atom $val ())
       (cons-atom (car-atom $xs) (List.append $val (cdr-atom $xs)))))

;; List.replaceAt — replace the element at 0-based index $n with $elem.
(= (List.replaceAt $xs $n $elem)
   (if (== $xs ())
       ()
       (if (== $n 0)
           (cons-atom $elem (cdr-atom $xs))
           (cons-atom (car-atom $xs) (List.replaceAt (cdr-atom $xs) (- $n 1) $elem)))))

;; concatT — concatenate two native ()-tuples (upstream general-helpers concatT).
(= (concatT $a $b)
   (if (== $a ())
       $b
       (cons-atom (car-atom $a) (concatT (cdr-atom $a) $b))))

;; is-member — membership in a native ()-list (PeTTa builtin in upstream; here an
;; alias of List.member so tree.metta's (is-member $r (AND OR)) ports unchanged).
(= (is-member $x $xs) (List.member $x $xs))

;; isUnit / isNotUnit — the named predicates that replace (compose not isUnit).
(= (isUnit    $e) (== $e ()))
(= (isNotUnit $e) (not (== $e ())))

;; concatTuple — SET-union concat (upstream general-helpers concatTuple = union-atom,
;; which DEDUPLICATES). Distinct from concatT above (plain order-preserving concat).
(= (concatTuple $x $y) (union-atom $x $y))

;; any — True iff any element is True (upstream general-helpers).
(= (any $bools) (is-member True $bools))

;; removeElement — remove the elements of $common from $tuple (set subtraction).
;; Upstream used (collapse (subtraction (superpose $tuple) (superpose $common)));
;; Core's grounded subtraction-atom does this deterministically.
(= (removeElement $common $tuple) (subtraction-atom $tuple $common))

;; swapAndOr — AND↔OR, anything else unchanged (the reduct's de Morgan dual).
(= (swapAndOr $op) (case $op ((AND OR) (OR AND) ($else $op))))

;; ~= / === — not-equal / strict-equal. Core lacks these (and `!=` even tokenizes as
;; `! =`); both reduce to ==.  (Upstream uses ~= for "not equal" and === as a strict ==.)
(= (~=  $a $b) (not (== $a $b)))
(= (=== $a $b) (== $a $b))

;; findAndReplace — replace the top-level child $old with $new inside $list. If $old
;; IS the whole $list, return $new (root replacement). Upstream used
;; (collapse (replace $old $new (superpose $list))); Core maps with map-atom.
(= (findAndReplace $old $new $list)
   (if (== $old $list)
       $new
       (map-atom $list $e (if (== $e $old) $new $e))))

;; first / second — bare 2-tuple accessors (upstream general-helpers; `first` was
;; commented out there but appendToLSK needs it).
(= (first  ($a $b)) $a)
(= (second ($a $b)) $b)

;; List.contains — membership (alias of List.member; upstream name used by lsk).
(= (List.contains $x $xs) (List.member $x $xs))

;; updateID — drop a leading 0 from a NodeId path ((0 1 1) → (1 1)); the (0) root
;; prefix is implicit elsewhere. Used when recording a knob's anchor node.
(= (updateID (mkNodeId $id))
   (if (== (car-atom $id) 0) (mkNodeId (cdr-atom $id)) (mkNodeId $id)))

;; Pair (utilities/pair.metta) — UNTYPED (Core dialect); constructor mkPair + accessors.
(= (Pair.first  (mkPair $a $b)) $a)
(= (Pair.second (mkPair $a $b)) $b)
