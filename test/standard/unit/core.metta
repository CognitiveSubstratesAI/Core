;;;; unit/core.metta — hyperon UNIT-test corpus for core ops (superpose/collapse/case/
;;;; pragma!/sealed/let/let*/quote/unify/match/== etc.). EXTRACTED + TRANSLATED VERBATIM
;;;; (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/runner/stdlib/core.rs  (test mod, lines 365-557)
;;;; Method: each `run_program("PROG")` + `Ok(vec![vec![EXPECTED]])` becomes one self-checking
;;;;   directive. expr! → MeTTa surface: "X"→symbol X, bare x→$x (variable),
;;;;   {Number::Integer n}→n (Int), {Number::Float f}→f (Float) — numeric TYPE preserved;
;;;;   {Str::from_str "m"}→"m". GROUND expected → (assertEqual …). VARIABLE-containing expected →
;;;;   (assertAlphaEqualToResult … (R)) [alpha up to var-renaming; assertAlphaEqual NOT in Minimal].
;;;;   MULTIPLE results → (assertEqualToResult … (R1 R2 …)). UNIT_ATOM → (). PROG already
;;;;   `!(assertEqual …)`/`!(assertEqualToResult …)` → copied VERBATIM (self-checking already).
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   core.rs total #[test] fns = 13.
;;;;   run_program-based (translated here) = 8 fns:
;;;;     metta_superpose, metta_case_empty, metta_case_error, test_pragma_interpreter_bare_minimal,
;;;;     test_pragma_max_stack_depth, use_sealed_to_make_scoped_variable,
;;;;     let_op_variables_visibility_pr262, sealed_op_runner.
;;;;   RESIDUE — 5 fns NOT portable as a single run_program vec directive (gated by hand-written
;;;;     Julia/Rust-op tests instead, NEVER silently dropped):
;;;;     - metta_collapse (390): run_program BUT result is checked with assert_eq_NO_ORDER over the
;;;;         collapsed children (nondeterministic order) — not a plain ordered vec. The ordered
;;;;         (assertEqual (collapse (color)) (red green blue)) below is order-fragile, so it is
;;;;         given as a NOTE only, not a hard assert.
;;;;     - match_op (529), match_op_issue_530 (538): Rust-op-direct — call MatchOp.execute_bindings
;;;;         and inspect the returned (Atom, Option<Bindings>) iterator; no MeTTa program.
;;;;     - nop_op (547): Rust-op-direct — NopOp{}.execute(&mut vec![]) == unit_result().
;;;;     - sealed_op_execute (552): Rust-op-direct — SealedOp{}.execute(...) + atoms_are_equivalent.
;;;;     (sealed_op_runner IS translated: it run_programs then atoms_are_equivalent — the program
;;;;      string is portable; the equivalence check = our assertAlphaEqualToResult.)

; ── metta_superpose (core.rs:376-387) — superpose fans an expression into N results ──────────
!(assertEqualToResult (superpose (red yellow green)) (red yellow green))

(= (foo) FOO)
(= (bar) BAR)
!(assertEqualToResult (superpose ((foo) (bar) BAZ)) (FOO BAR BAZ))

; ── metta_collapse (core.rs:390-405) — RESIDUE (order-insensitive in Rust; NOTE only) ─────────
(= (color) red)
(= (color) green)
(= (color) blue)
; NOTE (not a hard assert — Rust uses assert_eq_no_order over the collapsed children):
;   (collapse (color)) ≡ {red green blue} as an unordered bag.
; !(assertEqual (collapse (color)) (red green blue))

; ── metta_case_empty (core.rs:407-417) — case default vs match-then on Empty/unify ────────────
!(assertEqual (case Empty ( (ok ok) (Empty nok) )) nok)
!(assertEqual (case (unify (C B) (C B) ok Empty) ( (ok ok) (Empty nok) )) ok)
!(assertEqual (case (unify (B C) (C B) ok nok) ( (ok ok) (nok nok) )) nok)
!(assertEqual (case (unify (B C) (C B) ok Empty) ( (ok ok) (Empty nok) )) nok)

; ── metta_case_error (core.rs:419-429) — case matches an Error pattern, returns Unit ──────────
(= (err) (Error (err) "Test error"))
!(assertEqual (case (err) (
  ((Error $a "Test error") ())
  ($_ (Error $_ "Error is expected"))
  )) ())

; ── test_pragma_interpreter_bare_minimal (core.rs:431-449) — pragma! flips interpreter mode ───
; Program runs 4 `!` directives sharing the (foo)/(bar) defs; the pragma! switches to
; bare-minimal so subsequent (foo) no longer reduces. Each `!` result asserted in order.
(= (bar2) baz)
(= (foo2) (bar2))
!(assertEqual (foo2) baz)
!(assertEqual (pragma! interpreter bare-minimal) ())
!(assertEqual (foo2) (foo2))
!(assertEqual (eval (foo2)) (bar2))

; ── test_pragma_max_stack_depth (core.rs:451-483) ─────────────────────────────────────────────
; First program is ALREADY a self-checking !(assertEqual …) — copied VERBATIM:
!(assertEqual (pragma! max-stack-depth -12) (Error (pragma! max-stack-depth -12) UnsignedIntegerIsExpected))

; Second program: two pragma! (Unit each) then fac 6 = 720.
!(assertEqual (pragma! max-stack-depth 21) ())
!(assertEqual (pragma! max-stack-depth 0) ())
(= (fac $n) (if (== $n 0) 1 (* $n (fac (- $n 1)))))
!(assertEqual (fac 6) 720)

; Third program: pragma! (Unit), fac 3 = 6, then a case that expects a StackOverflow Error → Unit.
!(assertEqual (pragma! max-stack-depth 200) ())
!(assertEqual (fac 3) 6)
!(assertEqual (case (fac 6) (
   ((Error $a StackOverflow) ())
   ($_ (Error (fac 6) "StackOverflow error is expected")) )) ())

; ── use_sealed_to_make_scoped_variable (core.rs:485-491) — let / sealed / quote scoping ───────
; First: let binds $x to (input $x) — self-referential, yields NO results (empty vec).
!(assertEqualToResult (let $x (input $x) (output $x)) ())
; Second: result contains free variable $y → alpha-equality.
!(assertAlphaEqualToResult (let $x (input $y) (output $x)) ((output (input $y))))
; Third: sealed makes the inner $x scoped so the outer let-binding survives.
!(assertAlphaEqualToResult (let (quote ($sv $st)) (sealed () (quote ($x (output $x))))
       (let $sv (input $x) $st)) ((output (input $x))))

; ── let_op_variables_visibility_pr262 (core.rs:493-518) — let* var visibility across match ────
(→ P Q)
(→ Q R)
(= (rule (→ $p $q) (→ $q $r)) (→ $p $r))
(= (query $kb)
   (let* (($pq (→ $p $q))
          ($qr (→ $q $r)))
     (match $kb
       (, $pq $qr)
       (rule $pq $qr))))
!(assertEqual (query &self) (→ P R))

; ── sealed_op_runner (core.rs:520-527) — sealed renames non-ignored vars (alpha-equivalent) ───
!(assertAlphaEqualToResult (sealed ($c) (quote (= ($a $x $c) ($b)))) ((quote (= ($a $b $c) ($z)))))
!(assertAlphaEqualToResult (sealed ($z $x) (quote (= ($y $z)))) ((quote (= ($y $z)))))
