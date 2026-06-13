;;;; unit/stdlib_space_sugar.metta — behavioral gate for add-reduct / add-reducts / add-atoms
;;;; (hyperon stdlib.metta:567-683, ported VERBATIM into Core's stdlib.metta).
;;;; hyperon's own #[test]s for these (runner/stdlib/mod.rs) only cover the arity-error case; these gate
;;;; the FAITHFUL semantics: add-reduct/add-reducts REDUCE the %Undefined%-typed arg before storing
;;;; ((+ 1 2)→3), while add-atoms stores its Expression-typed tuple elements unreduced.
;;;;
;;;; DELIBERATELY a standalone file with NO non-directive atoms: the unit harness runs each file's
;;;; directives in ONE shared space and add_atom!s any `(: …)`/`(= …)` into it; `get-atoms` then picks
;;;; those up. Keeping this file directive-only keeps `get-atoms &arN` clean. (Separate open finding,
;;;; recorded in CORELIB_COVERAGE.md: in a polluted shared space `get-atoms &arN` also returned &self's
;;;; own atoms — a new-space isolation / get-atoms-scope question, orthogonal to add-reduct.)

!(bind! &ar1 (new-space))
!(add-reduct &ar1 (+ 1 2))
!(assertEqualToResult (get-atoms &ar1) (3))

!(bind! &ar2 (new-space))
!(add-atoms &ar2 (a b c))
!(assertEqualToResult (get-atoms &ar2) (a b c))

!(bind! &ar3 (new-space))
!(add-reducts &ar3 ((+ 1 2) (* 2 3)))
!(assertEqualToResult (get-atoms &ar3) (3 6))
