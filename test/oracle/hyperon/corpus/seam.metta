; seam.metta — the Int/Float boundary, run on BOTH engines and diffed.
;
; Every directive here was MEASURED to differ (or to agree, deliberately) between Core and
; hyperon-experimental 0.2.10 on 2026-08-05/06. This file is the executable form of
; docs/NUMERIC_SEAM_DIVERGENCES_2026-08-05.md — the .md records WHY, this records WHAT, and the
; harness makes the difference fail a test instead of sitting in prose.
;
; WHY IT CANNOT LIVE IN test/oracle/leatta/: that corpus is vendored VERBATIM from upstream and
; must not be edited. Its 270 directives touch `/` once with a Float operand and `%` once with a
; non-zero divisor, which is exactly why none of this was caught.

; ── integer division: hyperon returns Number::Integer(a/b); Core promotes to Float ──
! (/ 7 2)
! (/ 4 2)
! (/ -7 2)

; ── division by zero: hyperon guards; Core throws a raw host DivideError for %, Inf/NaN for / ──
! (% 7 0)
! (/ 7 0)
! (/ 0 0)

; ── float division IS IEEE on both — the correct half, pinned so a fix cannot over-reach ──
! (/ 7.0 0.0)
! (/ 4 6.4)

; ── i64 wraparound: CONFORMANT. hyperon ships overflow-checks=false and wraps identically. ──
! (+ 9223372036854775807 1)
! (* 99999999999 99999999999)

; ── out-of-range literal: hyperon = hard parse error; Core falls through to tryparse(Float64) ──
! (+ 9223372036854775808 0)

; ── ordinary arithmetic: must agree, and does — the control ──
! (+ 2 3)
! (- 8 3)
! (* 6 7)
! (% 21 17)

; ── trace!'s declared type: BOTH give %Undefined%; the docs claim Number. Pinned so a future
;    reader "fixing" Core toward the docs breaks a test instead of conformance. ──
! (get-type (trace! (Expecting 3) (+ 1 2)))
! (get-type (+ 1 2))
