; int64_boundary.metta — the arithmetic overflow boundary, as a CORPUS CASE.
;
; Run:  bash workflows/metta_xcheck.sh Core/test/corpus/int64_boundary.metta
;
; MEASURED 2026-09-03 across five engines. Core matches hyperon-experimental BIT-FOR-BIT on both
; lanes; wrapping at 2^63 is the REFERENCE behaviour, not a Core defect:
;
;   hyperon-experimental  fib(93) = -6246583658587674878   i64, wraps
;   Core (interpreter)    fib(93) = -6246583658587674878   i64, wraps   <- conformant
;   Core (compiled lane)  fib(93) = -6246583658587674878   i64, wraps   <- conformant
;   CeTTa                 fib(93) =  12200160415121876738  UNBOUNDED
;   PeTTa                 fib(93) =  12200160415121876738  UNBOUNDED (SWI host)
;   JeTTa                 fib(93) =  572466946             i32 — breaks around fib(46)
;
; fib(92) = 7540113804746346429 is the LAST value that fits i64 (max 9223372036854775807).
;
; ⚠️ ITERATIVE, DELIBERATELY. Naive-recursive fib(92) is ~2^92 calls; every engine timed out and
; metta_xcheck correctly refused to certify the reduced quorum. The iterative form also isolates
; the ARITHMETIC boundary from tabling — otherwise this conflates "does it wrap" with "does it
; memoise", and only the former is NumericSeam's question.
;
; The boundary is SILENT in every engine that has one: no error, no flag, a negative Fibonacci
; number. This file exists so it cannot drift unnoticed.

(= (fibi $n $a $b) (if (< $n 1) $a (fibi (- $n 1) $b (+ $a $b))))
(= (fib $n) (fibi $n 0 1))
!(fib 92)
!(fib 93)
