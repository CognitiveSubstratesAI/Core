; UNIT corpus — hyperon's debug.rs assert-family OWN-behavior #[test] cases (lib/src/metta/runner/stdlib/debug.rs).
; These gate the HARNESS VERBS at their edges (assertEqual / assertEqualToResult / assertAlphaEqualToResult) —
; the asserts the rest of the corpus is WRITTEN IN, so their own edge semantics were never adopted by 0c51e87.
; Distinct fn names (one shared space; debug.rs uses a separate program per #[test]). result == () ⇒ pass.
;
; SUCCESS cases are faithful and pass today. The DIVERGENCE cases are written to hyperon's FAITHFUL output and
; are EXPECTED-FAIL on Core now — they are the gate the grounded-assert `.jl` fix must flip green:
;   • MULTIPLICITY: Core's compare is multiplicity-insensitive SET-equality; hyperon is MULTISET.
;   • MESSAGE: Core emits bare `AssertionFailed`; hyperon emits `\nExpected:…\nGot:…\nMissed…\nExcessive…`.
; collapse is verified faithful (`collapse (mult)`→`(D D D)`), so the fix is contained to the assert ops.
; (=alpha cases omitted — =alpha not yet implemented in Core; grounded per debug.rs, deferred behind the hang.)

; ── programs ──────────────────────────────────────────────────────────────────
(= (eqf $x) $x)                          ; assertEqual: (foo $x)=$x and (bar $x)=$x — eqf serves both sides
(= (nd) A) (= (nd) B)                    ; nondeterministic, distinct results {A,B}
(= (mult) D) (= (mult) D) (= (mult) D)   ; multiplicity {D,D,D}
(= (av) $x)                              ; assertAlphaEqualToResult: (foo)=$x

; ── SUCCESS (faithful, pass today) ─────────────────────────────────────────────
!(assertEqual (eqf A) (eqf A))                        ; match → ()
!(assertEqualToResult (nd) (A B))                     ; distinct nondeterm collapses & matches → ()
!(assertAlphaEqualToResult (av) ($x))                 ; alpha-equal up to var rename → ()

; ── DIVERGENCE: error message form (Core bare AssertionFailed vs hyperon detailed) — EXPECTED-FAIL ──
!(assertEqualToResult
   (assertEqual (eqf A) (eqf B))
   ((Error (assertEqual (eqf A) (eqf B)) "\nExpected: [B]\nGot: [A]\nMissed results: B\nExcessive results: A")))

; ── DIVERGENCE: MULTIPLICITY (Core () set-equality vs hyperon Error multiset) — EXPECTED-FAIL ──
!(assertEqualToResult
   (assertEqualToResult (mult) (D))
   ((Error (assertEqualToResult (mult) (D)) "\nExpected: [D]\nGot: [D, D, D]\nExcessive results: D, D")))
