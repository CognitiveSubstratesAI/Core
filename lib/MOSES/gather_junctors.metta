;;;; gather_junctors.metta — flatten nested same-junctor nodes + normalize to an
;;;; AND-of-OR-of-AND shape (port of metta-moses reduct/boolean-reduct/
;;;; n-ary-gather-junctors.metta). gatherJunctors: (AND A (AND B C)) → (AND A B C).
;;;; addAND: wrap bare OR/literal children under AND so every level alternates.
;;;; Second + third stages of applyReduce (after propagateNot).
;;;;
;;;; CORE-DIALECT: upstream's `(collapse (f (superpose $expr) …))` element-map becomes
;;;; `(map-atom $expr $e (f $e …))`; the local fold/concat-tuple become foldl-atom and
;;;; concatT (plain order-preserving concat, NOT the dedup concatTuple).

;; ── addAND ──────────────────────────────────────────────────────────────────
;; final-pass wrapper: a top-level OR/NOT gets an AND parent.
(= (addAND $expr $isFinal)
   (if (and $isFinal (or (== (car-atom $expr) OR) (== (car-atom $expr) NOT)))
       (AND $expr)
       $expr))

;; entry: seed parent/prev from the head.
(= (addAND $expr)
   (if (== (get-metatype $expr) Expression)
       (addAND $expr (car-atom $expr) ())
       (addAND $expr () ())))

;; recursive wrapper tracking parent + previous junctor.
(= (addAND $expr $parent $prev)
   (case (get-metatype $expr)
     ((Symbol (if (or (or (or (== AND $expr) (== OR $expr)) (== NOT $expr))
                      (or (== $parent AND) (== $prev AND)))
                  $expr
                  (AND $expr)))
      (Expression
        (let* ((($h $t) (decons-atom $expr))
               ($parentIsAND (== AND $parent)))
          (case ($h $parentIsAND)
            (((NOT True)  $expr)
             ((NOT False) (AND $expr))
             ((OR True)   (map-atom $expr $e (addAND $e $h $h)))
             ((OR False)  (AND (map-atom $expr $e (addAND $e $h $h))))
             ((AND $_)    (map-atom $expr $e (addAND $e AND $h)))
             (($else $__) (if (== $t ()) (addAND $h () ()) (AND)))))))
      ($else $expr))))

;; ── gatherJunctors ──────────────────────────────────────────────────────────
(= (nary-gather-junctors $expr $prev)
   (if (== (get-metatype $expr) Expression)
       (let* (($op       (car-atom $expr))
              ($tuple     (cdr-atom $expr))
              ($mapped    (map-atom $tuple $e (nary-gather-junctors $e $op)))
              ($newTuple  (foldl-atom $mapped () $acc $x (concatT $acc $x)))
              ($tupleWithOp (cons-atom $op $newTuple)))
         (if (== $op $prev)
             $newTuple
             (if (== $prev ())
                 $tupleWithOp
                 ($tupleWithOp))))
       ($expr)))

(= (gatherJunctors $expr) (nary-gather-junctors $expr ()))
