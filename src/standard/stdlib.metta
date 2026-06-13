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
