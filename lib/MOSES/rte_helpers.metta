;;;; rte_helpers.metta — reduce-to-elegance helper layer (port of metta-moses
;;;; reduct/boolean-reduct/rte-helpers.metta). The boolean-reduct engine's set
;;;; operations over a node's literals/children.
;;;;
;;;; CORE-DIALECT (the key M6 adaptation): upstream expresses these as
;;;;   (collapse (filterLiterals (superpose $exp)))
;;;; i.e. fan a node's elements into nondeterministic branches, filter each, regather.
;;;; Core does NOT fan out (f (superpose x)) through application — but its GROUNDED
;;;; `filter-atom`/`map-atom` DO map element-wise (same primitives used in M1b to
;;;; replace the dead higher-order List.map). So every superpose/collapse/filter set-op
;;;; becomes a `filter-atom`/`map-atom` template, and set-difference/union are the
;;;; grounded subtraction-atom/union-atom. getGuardSet is inlined to avoid upstream's
;;;; if-decons-expr-custom (which defers `eval` of an Atom arg — unsupported for
;;;; custom fns in Core). Deterministic — no real nondeterminism needed.

;; ── element predicates (replace upstream filterLiterals/filterChildren) ──────
;; isLiteral — a symbol that is not a junctor, OR a (NOT …) negation.
(= (isLiteral $e)
   (if (== (get-metatype $e) Symbol)
       (if (or (== $e AND) (== $e OR)) False True)
       (if (== (car-atom $e) NOT) True False)))

;; isChild — a subexpression that is neither a bare symbol nor a (NOT …) literal.
(= (isChild $e)
   (if (== (get-metatype $e) Symbol)
       False
       (if (== (car-atom $e) NOT) False True)))

;; ── literals / children of a node ───────────────────────────────────────────
;; getLiterals — the literals of an AND/OR node ((NOT …) counts as a literal).
;; A bare (NOT x) or symbol returns itself; () returns ().
(= (getLiterals $exp)
   (if (== $exp ())
       ()
       (if (== (get-metatype $exp) Expression)
           (if (== (car-atom $exp) NOT)
               $exp
               (filtP $exp isLiteral))
           $exp)))

;; getChildrenExp — the non-literal subexpression children of a node.
(= (getChildrenExp $exp)
   (if (== $exp ())
       ()
       (if (== (get-metatype $exp) Expression)
           (if (== (car-atom $exp) NOT)
               ()
               (filtP $exp isChild))
           ())))

;; getGuardSet — the guard set (literals) of an AND node; OR nodes have none.
;; Inlined (no if-decons-expr-custom): Expression & non-empty & head≠OR → getLiterals.
(= (getGuardSet $exp)
   (if (== (get-metatype $exp) Expression)
       (if (== $exp ())
           $exp
           (if (== (car-atom $exp) OR)
               ()
               (getLiterals $exp)))
       $exp))

;; In Core the "ND" variants collapse to their deterministic counterparts (callers
;; that upstream mapped via superpose now map via map-atom over the returned list).
(= (getGuardSetND $exp) (getGuardSet $exp))
(= (getLiteralsND $exp) (getLiterals $exp))

;; getLiteralChildren — (literals children) of a node as a 2-tuple. The parts are
;; bound via let* first: a bare ((getLiterals …) (getChildrenExp …)) tuple would
;; keep the calls UNEVALUATED (list construction does not evaluate elements).
(= (getLiteralChildren $expr)
   (let* (($lits (getLiterals $expr))
          ($chld (getChildrenExp $expr)))
     ($lits $chld)))

;; ── mutation: add literals / children to a node ─────────────────────────────
(= (addLiterals $exp $elements)
   (let* (($op (car-atom $exp))
          ($guardSet (getLiterals $exp))
          ($newGuardSet (union-atom $guardSet $elements))
          ($updatedSubExpression (union-atom $newGuardSet (getChildrenExp $exp)))
          ($newExp (cons-atom $op $updatedSubExpression)))
     $newExp))

(= (addChildren $exp $children)
   (let* (($op (car-atom $exp))
          ($oldChildren (getChildrenExp $exp))
          ($newChildren (concatTuple $oldChildren $children))
          ($updatedSubExpression (concatTuple (getLiterals $exp) $newChildren))
          ($newExp (cons-atom $op $updatedSubExpression)))
     $newExp))

;; ── common-literal queries ──────────────────────────────────────────────────
;; findCommonLiterals — intersection of $tuple with every member of a nested tuple.
(= (findCommonLiterals $tuple $nestedTuple)
   (if (or (== $nestedTuple ()) (== $tuple ()))
       ()
       (let* (($first  (car-atom $nestedTuple))
              ($tail   (cdr-atom $nestedTuple))
              ($common (intersection-atom $tuple $first)))
         (if (== $tail ())
             $common
             (findCommonLiterals $common $tail)))))

;; findCommon — common literals across a nested tuple of guard sets.
(= (findCommon $nestedTuple)
   (case $nestedTuple
     ((() $nestedTuple)
      ($else
        (if (== (cdr-atom $nestedTuple) ())
            (car-atom $nestedTuple)
            (let* (($first (car-atom $nestedTuple))
                   ($tail  (cdr-atom $nestedTuple)))
              (findCommonLiterals $first $tail)))))))
