; UNIT corpus — assertIncludes (hyperon stdlib.metta:691, verbatim rule). Cross-checked hyperon + CeTTa.
; Each !(assert…) returns () on success = the unit harness's pass-marker (run_unit_file: result == () ⇒ pass).
; (assertAlphaEqual / *Msg / =alpha intentionally NOT here — deferred to the grounded-vs-rules decision
;  for the assert family; see CORELIB_COVERAGE.md.)
;
; ── assertIncludes: content ⊆ collapsed results of the first arg ──────────────
!(assertIncludes (superpose (1 2 3)) (1 2))
!(assertIncludes (superpose (A B C)) (C))
!(assertIncludes (superpose (1 2 3)) ())            ; vacuous: () ⊆ anything (0-cardinality edge)
