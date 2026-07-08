; Standard MeTTa stdlib (subset) — ported VERBATIM from hyperon-experimental
;   lib/src/metta/runner/stdlib/stdlib.metta
; and loaded by Core's StandardMeTTa evaluator. The grounded set (+,-,*,/,<,>,and,
; or,not,id,==) and the minimal instructions (unify/chain/decons-atom/…) are provided
; by the evaluator; everything below is plain MeTTa `=` rules on top of them.
;
; switch/case are intentionally omitted from this subset (they additionally need the
; if-equal / context-space / metta grounded ops) — a follow-on.

; ── assertEqual / assertEqualToResult (Atom-typed args: not pre-evaluated) ────
(: assertEqual (-> Atom Atom (->)))
(: assertEqualToResult (-> Atom Atom (->)))
(: assertAlphaEqualToResult (-> Atom Atom (->)))
; ── assertIncludes (hyperon stdlib.metta:691, VERBATIM) — additive, hang-safe ──
; Cross-checked: hyperon defines it as a light rule over collapse/subtraction-atom/if/== (NOT the heavy
; metta-3-arg path); CeTTa has no rule form (grounded). All ops present in Core, so port verbatim.
(: assertIncludes (-> Atom Expression (->)))
(= (assertIncludes $atom $content)
    (let $eval_atom (collapse $atom)
        (let $diff (subtraction-atom $content $eval_atom)
            (if (== $diff ())
                ()
                (Error (assertIncludes $atom $content)
                  (assertIncludes error: $diff not included in result: $eval_atom))))))
; ── the rest of the hyperon assert family (stdlib.metta:1101-1190): assertAlphaEqual + the `*Msg`
;    variants. Written MeTTa-first — RULES composing existing primitives (collapse / subtraction-atom /
;    union-atom / if / ==), the same compose-from-primitives idiom as assertIncludes above (NO new
;    grounded ops). Two collapsed result sets are equal iff their two-way multiset difference is empty;
;    on failure the `Msg` forms surface the caller's $msg (hyperon @return "input message - otherwise"),
;    yielding the exact `(Error (op $actual $expected) $msg)` shape the corpus asserts (test_stdlib:114-124).
;    A NON-ERRORING comparison is required: delegating to the grounded assertEqual would let its
;    `(Error … AssertionFailed)` propagate through ==/case and clobber the custom message (verified).
;    subtraction-atom's element identity is α-equivalence (Interpreter.jl:1868), so these rule-composed
;    variants are α-tolerant; the exact grounded floor (assertEqual/assertEqualToResult) is unchanged.
;    That distinction is invisible to the (ground) corpus cases. `*ToResult*` do NOT collapse the expected
;    arg (it is already a literal result-set tuple); the others collapse both sides.
(: assertEqualMsg (-> Atom Atom Atom (->)))
(= (assertEqualMsg $actual $expected $msg)
   (let $a (collapse $actual)
     (let $e (collapse $expected)
       (if (== (union-atom (subtraction-atom $a $e) (subtraction-atom $e $a)) ())
           ()
           (Error (assertEqualMsg $actual $expected) $msg)))))

(: assertEqualToResultMsg (-> Atom Atom Atom (->)))
(= (assertEqualToResultMsg $actual $expected $msg)
   (let $a (collapse $actual)
       (if (== (union-atom (subtraction-atom $a $expected) (subtraction-atom $expected $a)) ())
           ()
           (Error (assertEqualToResultMsg $actual $expected) $msg))))

(: assertAlphaEqual (-> Atom Atom (->)))
(= (assertAlphaEqual $actual $expected)
   (let $a (collapse $actual)
     (let $e (collapse $expected)
       (if (== (union-atom (subtraction-atom $a $e) (subtraction-atom $e $a)) ())
           ()
           (Error (assertAlphaEqual $actual $expected) AssertionFailed)))))

(: assertAlphaEqualMsg (-> Atom Atom Atom (->)))
(= (assertAlphaEqualMsg $actual $expected $msg)
   (let $a (collapse $actual)
     (let $e (collapse $expected)
       (if (== (union-atom (subtraction-atom $a $e) (subtraction-atom $e $a)) ())
           ()
           (Error (assertAlphaEqualMsg $actual $expected) $msg)))))

(: assertAlphaEqualToResultMsg (-> Atom Atom Atom (->)))
(= (assertAlphaEqualToResultMsg $actual $expected $msg)
   (let $a (collapse $actual)
       (if (== (union-atom (subtraction-atom $a $expected) (subtraction-atom $expected $a)) ())
           ()
           (Error (assertAlphaEqualToResultMsg $actual $expected) $msg))))
; ── noeval / empty (hyperon stdlib.metta:270/622 ; CeTTa lib/stdlib.metta:360/462 — both upstreams AGREE) ──
; noeval: Atom-typed so the arg is NOT pre-evaluated; returns it unreduced (evaluation control).
(: noeval (-> Atom Atom))
(= (noeval $x) $x)
; empty: nullary → the `Empty` no-results marker (CeTTa types it `(-> Atom)`; hyperon omits the decl).
(: empty (-> Atom))
(= (empty) Empty)
(: match (-> Atom Atom Atom %Undefined%))
; ── quote / unquote (hyperon stdlib.metta:597) — evaluation control ──────────
; quote = a CONSTRUCTOR: `(-> Atom Atom)` (arg raw, unevaluated) with NO equalities, so `(quote X)`
; keeps X unreduced and is itself non-reducible (the docs' canonical "symbol without equalities" form).
; (hyperon's stdlib also has `(= (quote $atom) NotReducible)`, but Minimal doesn't treat a NotReducible
; rule-body specially — it'd reduce to the bare symbol — so the equivalent constructor form is used.)
(: quote (-> Atom Atom))
(: unquote (-> %Undefined% %Undefined%))
(= (unquote (quote $atom)) $atom)
(: get-type (-> Atom %Undefined%))
(: get-metatype (-> Atom Atom))
(: = (-> $t $t %Undefined%))
(: superpose (-> Expression %Undefined%))
(: collapse (-> Atom Atom))
(: foldl-atom (-> Expression Atom Variable Variable Atom %Undefined%))
(: case (-> Atom Expression %Undefined%))
; arithmetic types (so wrong-typed args yield BadArgType)
(: + (-> Number Number Number))
(: - (-> Number Number Number))
(: * (-> Number Number Number))
(: / (-> Number Number Number))
(: % (-> Number Number Number))
; comparison ops → Bool (CeTTa/PeTTa type these; Core had them %Undefined%)
(: < (-> Number Number Bool))
(: <= (-> Number Number Bool))
(: > (-> Number Number Bool))
(: >= (-> Number Number Bool))
; math grounded ops (CoreExtensions.jl): unary Number→Number, binary Number Number→Number
(: sqrt (-> Number Number))
(: log (-> Number Number))
(: exp (-> Number Number))
(: abs (-> Number Number))
(: floor (-> Number Number))
(: ceil (-> Number Number))
(: max (-> Number Number Number))
(: min (-> Number Number Number))
(: pow (-> Number Number Number))
(: clamp (-> Number Number Number Number))

; ── if (stdlib.metta:512) ─────────────────────────────────────────────────────
(= (if True $then $else) $then)
(= (if False $then $else) $else)
(: if (-> Bool Atom Atom $t))

; ── let (stdlib.metta:543) ────────────────────────────────────────────────────
(: let (-> Atom %Undefined% Atom %Undefined%))
(= (let $pattern $atom $template)
  (unify $atom $pattern $template Empty))

; ── let* (stdlib.metta:553) ───────────────────────────────────────────────────
(: let* (-> Expression Atom %Undefined%))
(= (let* $pairs $template)
  (chain (decons-atom $pairs) $ht
    (unify ($head $tail) $ht
      (unify ($pattern $atom) $head
        (let $pattern $atom (let* $tail $template))
        (Error (let* $pairs $template) "List of (<pattern> <atom>) pairs is expected as a second argument"))
      $template )))

; ── car-atom / cdr-atom (stdlib.metta:576 / 587) ─────────────────────────────
(= (car-atom $atom)
  (chain (decons-atom $atom) $ht (unify ($head $_) $ht
    $head
    (Error (car-atom $atom) "car-atom expects a non-empty expression as an argument") )))
(= (cdr-atom $atom)
  (chain (decons-atom $atom) $ht (unify ($_ $tail) $ht
    $tail
    (Error (cdr-atom $atom) "cdr-atom expects a non-empty expression as an argument") )))

; ── map-atom / filter-atom (stdlib.metta:475 / 455) ──────────────────────────
(: map-atom (-> Expression Variable Atom Expression))
(: filter-atom (-> Expression Variable Atom Expression))
(= (map-atom $list $var $map)
  (function (chain (decons-atom $list) $ht
    (unify ($head $tail) $ht
      (chain (eval (sealed ($var) $map)) $sealedmap
        (chain (eval (map-atom $tail $var $sealedmap)) $tail-mapped
          (chain (eval (atom-subst $head $var $sealedmap)) $map-expr
            (chain $map-expr $head-mapped
              (chain (cons-atom $head-mapped $tail-mapped) $res (return $res)) ))))
      (return ()) ))))

(= (filter-atom $list $var $filter)
  (function (chain (decons-atom $list) $ht
    (unify ($head $tail) $ht
        (chain (eval (sealed ($var) $filter)) $sealedfilter
          (chain (eval (filter-atom $tail $var $sealedfilter)) $tail-filtered
            (chain (eval (atom-subst $head $var $sealedfilter)) $filter-expr
              (chain $filter-expr $is-filtered
                (eval (if $is-filtered
                  (chain (cons-atom $head $tail-filtered) $res (return $res))
                  (return $tail-filtered) ))))))
      (return ()) ))))

; ── switch / switch-internal (stdlib.metta:346 / 362) ────────────────────────
(: switch (-> %Undefined% Expression %Undefined%))
(= (switch $atom $cases)
   (id (switch-minimal $atom $cases)))
(: switch-minimal (-> Atom Expression Atom))
(= (switch-minimal $atom $cases)
  (function (chain (decons-atom $cases) $list
    (chain (eval (switch-internal $atom $list)) $res
      (chain (eval (if-equal $res NotReducible Empty $res)) $x (return $x)) ))))
(: switch-internal (-> Atom Expression Atom))
(= (switch-internal $atom (($pattern $template) $tail))
  (function (unify $atom $pattern
    (return $template)
    (chain (eval (switch-minimal $atom $tail)) $ret (return $ret)) )))

; ── is-function (stdlib.metta:376) ───────────────────────────────────────────
(: is-function (-> Type Bool))
(= (is-function $type)
  (let $mtype (get-metatype $type)
    (unify $mtype Expression
      (let $size (size-atom $type)
        (unify $size 0
          False
          (let ($h $t) (decons-atom $type)
            (unify $h -> True False))))
      False)))

; ── documentation system (get-doc — 1-arg over &self; Empty when undocumented) ─
; Ported from hyperon stdlib.metta:796-875 (the @doc/@doc-formal model). The space arg
; is dropped (these query &self); get-type-space → get-type. `unify &self <pat> …` queries
; the space (the Grounded Space implements custom match_, like hyperon).
(: get-doc (-> Atom %Undefined%))
(= (get-doc $atom)
  (let $meta-type (get-metatype $atom)
    (case $meta-type (
      (Expression (get-doc-atom $atom))
      ($_ (get-doc-single-atom $atom)) ))))

(: get-doc-single-atom (-> Atom %Undefined%))
(= (get-doc-single-atom $atom)
  (let $type (get-type $atom)
    (if (is-function $type)
      (get-doc-function $atom $type)
      (get-doc-atom $atom) )))

(: get-doc-function (-> Atom Type %Undefined%))
(= (get-doc-function $name $type)
  (unify &self (@doc $name $desc (@params $params) $ret)
    (let $type' (if (== $type %Undefined%) (undefined-doc-function-type $params) (cdr-atom $type))
    (let ($params' $ret') (get-doc-params $params $ret $type')
      (@doc-formal (@item $name) (@kind function) (@type $type) $desc (@params $params') $ret')))
    Empty ))

(: undefined-doc-function-type (-> Expression Type))
(= (undefined-doc-function-type $params)
  (if (== () $params) (%Undefined%)
    (let $params-tail (cdr-atom $params)
    (let $tail (undefined-doc-function-type $params-tail)
      (cons-atom %Undefined% $tail) ))))

(: get-doc-params (-> Expression Atom Expression (Expression Atom)))
(= (get-doc-params $params $ret $types)
  (let $head-type (car-atom $types)
  (let $tail-types (cdr-atom $types)
    (if (== () $params)
      (let (@return $ret-desc) $ret
        (() (@return (@type $head-type) (@desc $ret-desc))) )
      (let (@param $param-desc) (car-atom $params)
        (let $tail-params (cdr-atom $params)
        (let ($params' $result-ret) (get-doc-params $tail-params $ret $tail-types)
        (let $result-params (cons-atom (@param (@type $head-type) (@desc $param-desc)) $params')
          ($result-params $result-ret) ))))))))

(: get-doc-atom (-> Atom %Undefined%))
(= (get-doc-atom $atom)
  (let $type (get-type $atom)
    (unify &self (@doc $atom $desc)
      (@doc-formal (@item $atom) (@kind atom) (@type $type) $desc)
      (unify &self (@doc $atom $desc' (@params $params) $ret)
        (get-doc-function $atom %Undefined%)
        Empty ))))

; ── multiset set operations (hyperon stdlib.metta:629-668) ───────────────────
; collapse the non-deterministic arg → call the grounded *-atom multiset op
; (unique-atom/union-atom/intersection-atom/subtraction-atom, provided by the
; evaluator, alpha-equivalence element identity) → superpose back to ND.
(: unique (-> Atom %Undefined%))
(= (unique $arg) (let $c (collapse $arg) (let $u (unique-atom $c) (superpose $u))))
(: union (-> Atom Atom %Undefined%))
(= (union $arg1 $arg2)
   (let $c1 (collapse $arg1) (let $c2 (collapse $arg2)
     (let $u (union-atom $c1 $c2) (superpose $u)))))
(: intersection (-> Atom Atom %Undefined%))
(= (intersection $arg1 $arg2)
   (let $c1 (collapse $arg1) (let $c2 (collapse $arg2)
     (let $u (intersection-atom $c1 $c2) (superpose $u)))))
(: subtraction (-> Atom Atom %Undefined%))
(= (subtraction $arg1 $arg2)
   (let $c1 (collapse $arg1) (let $c2 (collapse $arg2)
     (let $u (subtraction-atom $c1 $c2) (superpose $u)))))

; ── noreduce-eq / for-each-in-atom (hyperon stdlib.metta:951-967) ────────────
(: noreduce-eq (-> Atom Atom Bool))
(= (noreduce-eq $a $b) (== (quote $a) (quote $b)))
(: for-each-in-atom (-> Expression Atom (->)))
(= (for-each-in-atom $expr $func)
  (if (noreduce-eq $expr ())
    ()
    (let $head (car-atom $expr)
      (let $tail (cdr-atom $expr)
      (let $_ ($func $head)
      (for-each-in-atom $tail $func) )))))

; ── if-decons-expr / if-error / return-on-error / first-from-pair (290-432) ──
(: if-decons-expr (-> Expression Variable Variable Atom Atom %Undefined%))
(= (if-decons-expr $atom $head $tail $then $else)
  (function (eval (if-equal $atom ()
    (return $else)
    (chain (decons-atom $atom) $list
      (unify $list ($head $tail) (return $then) (return $else)) )))))
(: if-error (-> Atom Atom Atom %Undefined%))
(= (if-error $atom $then $else)
  (function (chain (eval (get-metatype $atom)) $meta
    (eval (if-equal $meta Expression
      (eval (if-equal $atom ()
        (return $else)
        (chain (decons-atom $atom) $list
          (unify $list ($head $tail)
            (eval (if-equal $head Error (return $then) (return $else)))
            (return $else) ))))
      (return $else) )))))
(: return-on-error (-> Atom Atom %Undefined%))
(= (return-on-error $atom $then)
  (function (eval (if-equal $atom Empty (return (return Empty))
    (eval (if-error $atom (return (return $atom))
      (return $then) ))))))
(= (first-from-pair $pair)
  (function
    (unify $pair ($first $second)
      (return $first)
      (return (Error (first-from-pair $pair) "incorrect pair format")))))

; ── add-reduct / add-reducts / add-atoms (hyperon stdlib.metta:567-683) ───────
; VERBATIM port. The "reduce" in add-reduct/add-reducts is TYPE-DRIVEN, not body-driven:
; the %Undefined%-typed arg is EVALUATED before the rule fires (verified Core evaluates
; %Undefined% args), then add-atom stores it; add-atoms' Expression-typed arg is stored
; unreduced. Bodies build on add-atom + foldl-atom, both already present in Minimal.
(: add-reduct (-> SpaceType %Undefined% (->)))
(= (add-reduct $dst $atom) (add-atom $dst $atom))
(: add-reducts (-> SpaceType %Undefined% (->)))
(= (add-reducts $space $tuple)
    (foldl-atom $tuple () $a $b (add-atom $space $b)))
(: add-atoms (-> SpaceType Expression (->)))
(= (add-atoms $space $tuple)
    (foldl-atom $tuple () $a $b (add-atom $space $b)))
