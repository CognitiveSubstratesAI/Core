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
; ── resolve-vs-shape regression guard (project_core_bare_var_atom_bug) ─────────
; The bare-var resolve-filter must key on "rewrite-RHS X is UNBOUND", NOT "X substitutes to a Var".
; A rewrite whose RHS RESOLVES to a variable (X bound to a var) must SURVIVE — a shape-filter would
; wrongly drop it and break every id-style rule. Passes now (no bug in a clean space); must still pass post-fix.
(= (rvid $x) $x)
!(assertEqualToResult (rvid A) (A))                     ; RHS resolves to a value
!(assertAlphaEqualToResult (rvid $z) ($z))              ; RHS resolves to a VARIABLE — THE discriminator
