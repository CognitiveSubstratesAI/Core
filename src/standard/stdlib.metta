; Standard MeTTa stdlib (subset) — ported VERBATIM from hyperon-experimental
;   lib/src/metta/runner/stdlib/stdlib.metta
; and loaded by Core's StandardMeTTa evaluator. The grounded set (+,-,*,/,<,>,and,
; or,not,id,==) and the minimal instructions (unify/chain/decons-atom/…) are provided
; by the evaluator; everything below is plain MeTTa `=` rules on top of them.
;
; switch/case are intentionally omitted from this subset (they additionally need the
; if-equal / context-space / metta grounded ops) — a follow-on.

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
