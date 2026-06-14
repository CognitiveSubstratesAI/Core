; UNIT corpus — control/eval stdlib functions. Cross-checked BOTH upstreams (hyperon + CeTTa AGREE).
; result == () ⇒ pass.
;
; noeval (hyperon stdlib.metta:270 / CeTTa lib/stdlib.metta:360): `(: noeval (-> Atom Atom))` — Atom-typed,
;   so the arg is NOT pre-evaluated; returns it UNREDUCED.
!(assertEqualToResult (noeval (+ 1 2)) ((+ 1 2)))      ; stays (+ 1 2), not 3
!(assertEqual (noeval foo) foo)                         ; symbol passes through
!(assertEqualToResult (noeval (foo (+ 1 2))) ((foo (+ 1 2))))  ; whole expr unreduced
; empty (hyperon stdlib.metta:622 / CeTTa lib/stdlib.metta:462): nullary → `Empty` (no-results marker).
!(assertEqualToResult (empty) ())                       ; Empty filtered to no-results
