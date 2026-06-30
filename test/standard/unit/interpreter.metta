;;;; unit/interpreter.metta — hyperon UNIT-test corpus for the MINIMAL MeTTa assembly
;;;; interpreter (eval / chain / unify / cons-atom / decons-atom / function /
;;;; collapse-bind / superpose-bind). EXTRACTED + TRANSLATED VERBATIM (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/interpreter.rs   (#[cfg(test)] mod tests, lines 1471-2170)
;;;;
;;;; Method: this file's tests call the Rust `interpret(space, atom)` / `call_interpret` directly
;;;;   on a hand-built space + a parsed minimal-MeTTa atom, then `assert_eq!(result, Ok(vec![EXP]))`.
;;;;   Each such case where the SPACE is built from a MeTTa string, the INTERPRETED atom is a
;;;;   parseable minimal-MeTTa atom, and the EXPECTED is a parseable atom (no Rust grounded structs)
;;;;   becomes one self-checking directive. The space `(= ...)` / `(: ...)` rules are emitted inline
;;;;   immediately before each group's directive(s) so they back the evaluation.
;;;;     expr! → MeTTa surface: "X"→symbol X, bare x→$x (variable), {Number::Integer n}→n (Int),
;;;;     {Number::Float f}→f (Float). GROUND expected → (assertEqual …). VARIABLE-containing
;;;;     expected → (assertAlphaEqualToResult … (R)). Multiple results → (assertEqualToResult … (R1 R2)).
;;;;     Error strings copied EXACTLY. (assertAlphaEqual is NOT in Minimal — only the 3 ops below.)
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   Total test fns in mod tests = 52.  (No `run_program` / `metta.run` helper exists in this file —
;;;;     every test calls the Rust `interpret(space, atom)` / `call_interpret` directly. "Portable" here
;;;;     = MeTTa-string space + parseable minimal-MeTTa atom + parseable expected, no Rust-only constructs.)
;;;;   PORTED = 36 of the 52 test fns (several yield >1 directive — smoketest yields 8 — for ~50 directives
;;;;     total across the groups below). This INCLUDES the 2 variable_operation fns, ported using their
;;;;     Minimal-default not(feature="variable_operation") branch (= NotReducible).
;;;;   RESIDUE — NOT portable, require Rust-only constructs (16 fns total, counted + named):
;;;;     (a) Custom grounded STRUCTS executed inside the program, or grounded numbers in op position —
;;;;         only testable in Rust (8 fns):
;;;;         interpret_atom_evaluate_grounded_value ({6} grounded int as op → NotReducible),
;;;;         interpret_atom_evaluate_grounded_expression (MulXUndefinedType → 42),
;;;;         interpret_atom_evaluate_grounded_expression_empty (ReturnNothing → Empty),
;;;;         interpret_atom_evaluate_grounded_expression_noreduce (NonReducible → NotReducible),
;;;;         interpret_atom_evaluate_grounded_expression_incorrect_argument (IncorrectArgument → NotReducible),
;;;;         interpret_atom_evaluate_grounded_expression_error (ThrowError → Error … "Test error"),
;;;;         interpret_evaluate_once (EvalCounter — asserts a Rust side-effect counter == 1),
;;;;         interpret_atom_evaluate_non_executable_grounded_atom_on_a_first_position ({1} {2} grounded ints).
;;;;     (b) Rust-API-only: build Atom::gnd(DynSpace)/Bindings or assert internals, NO pure MeTTa form (6 fns):
;;;;         test_superpose_bind (constructs Stack + Bindings via bind!{}/superpose_bind directly),
;;;;         interpret_duplicated_types, run_metta_using_context, interpret_stop_evaluation,
;;;;         interpret_context_space, interpret_variable_substitution
;;;;           (all pass Atom::gnd(space) / CONTEXT_SPACE_SYMBOL — a grounded space atom — as an arg).
;;;;     (c) (metta …) with a {space} grounded-space arg (2 fns):
;;;;         type_check_returned_value (→ (Error (foo) (BadType Bool Number))),
;;;;         test_incorrect_number_of_arguments_issue_1037 (→ (Error (foo b c) IncorrectNumberOfArguments)).
;;;;   PARTIAL: interpret_minimal_metta_smoketest is PORTED except its final collapse-bind raw-dump
;;;;     sub-assert (asserts the inner (atom bindings) pair structure via atom_bindings_into_atom) — that
;;;;     one sub-assert is residue; all its other sub-asserts are ported in the smoketest group below.
;;;;   NOTE: residue groups (a)/(b)/(c) are covered instead by Core's Julia-level interpreter tests.
;;;;
;;;; Provenance: hyperon-experimental/lib/src/metta/interpreter.rs ; per-group `; interpreter.rs:NNN`.

; ── eval: incorrect args (interpreter.rs:1480-1484) ──────────────────────────
!(assertEqual (eval) (Error (eval) "expected: (eval <atom>), found: (eval)"))
!(assertEqual (eval a b) (Error (eval a b) "expected: (eval <atom>), found: (eval a b)"))

; ── eval: evaluate atom against a definition (interpreter.rs:1488-1490) ───────
(= a b)
!(assertEqual (eval a) b)

; ── eval: no definition / empty expr → keep-form at the TOP LEVEL. The BARE interpreter yields the internal
;    NotReducible sentinel (interpreter.rs:1494-1502), but the metta driver SUPPRESSES it and surfaces the
;    original (eval …) unchanged (metta_call_return interpreter.rs:1456) — hyperon does the same; neither
;    engine shows the bare sentinel to the user. Strong assertEqualToResult pins the keep-form result set
;    (would catch a sentinel leak). (These were mis-vendored as bare-level `… NotReducible` assertions.)
!(assertEqualToResult (eval no-def-symbol) ((eval no-def-symbol)))
!(assertEqualToResult (eval ()) ((eval ())))

; ── eval: pure expression with var binding (interpreter.rs:1513-1516) ─────────
(= (foo $a B) $a)
!(assertEqual (eval (foo A $b)) A)

; ── eval: pure expression non-determinism (interpreter.rs:1520-1531) ──────────
(= color red)
(= color green)
(= color blue)
!(assertEqualToResult (eval color) (red green blue))

; ── eval: pure expr, no definition → keep-form at top level (bare NotReducible suppressed, rs:1535-1537/1456)
!(assertEqualToResult (eval (undefined-foo A)) ((eval (undefined-foo A))))

; ── eval: pure expr, variable in space (interpreter.rs:1542-1544) ─────────────
; space also contains a bare `$t` atom plus (= (foo2 $a B) $a)
$t
(= (foo2 $a B) $a)
!(assertEqual (eval (foo2 A $b)) A)

; ── eval: variable name conflict (interpreter.rs:1549-1551) ───────────────────
; asserts result[0] == True (single expected value kept)
(= (foo3 ($W)) True)
!(assertEqual (eval (foo3 $W)) True)

; ── eval: variable in OP position. Bare interp → NotReducible (rs:1585-1591, default not variable_operation);
;    at the top level that sentinel is SUPPRESSED → keep-form (metta_call_return rs:1456). hyperon matches.
; (= (foo $a B) $a) already in space above; ($a A $b) has a VARIABLE in op position
!(assertEqualToResult (eval ($a A $b)) ((eval ($a A $b))))
(= ((baz $a) $b) ($a $b))
; NOTE: Core performs variable-operation matching here ((($a A) B) unifies the ((baz $a) $b) rule) where
; hyperon's not(variable_operation) default does not — a SEPARATE pre-existing divergence (baseline), not the
; NotReducible-leak fix. Left asserting NotReducible so the baseline keeps tracking that gap honestly.
!(assertEqual (eval (($a A) B)) NotReducible)

; ── eval: variable via call, direct equality (interpreter.rs:1595-1605) ───────
; asserts result[0] == value
(= (bar) (function (return ())))
(= (foo-call $b) (function
  (chain (eval (bar)) $_
  (unify $b value
    (return ())
    (return (Error () "Unexpected error")) ))))
!(assertEqual (chain (eval (foo-call $a)) $_ $a) value)

; ── eval: variable via call, struct equality (interpreter.rs:1609-1630) ───────
; formal-arg-struct: foo's formal arg is ($b); asserts result[0] == ("value")
(= (bar-s) (function (return ())))
(= (foo-fs ($b)) (function
  (chain (eval (bar-s)) $_
  (unify $b value
    (return ())
    (return (Error () "Unexpected error")) ))))
!(assertEqual (chain (eval (foo-fs $a)) $_ $a) (value))
; actual-arg-struct: foo's formal arg is $b; called as (foo-as ($a)); result[0] == value
(= (foo-as $b) (function
  (chain (eval (bar-s)) $_
  (unify $b (value)
    (return ())
    (return (Error () "Unexpected error")) ))))
!(assertEqual (chain (eval (foo-as ($a))) $_ $a) value)

; ── chain: incorrect args (interpreter.rs:1654-1659) ─────────────────────────
!(assertAlphaEqualToResult (chain n $v t o) ((Error (chain n $v t o) "expected: (chain <nested> (: <var> Variable) <templ>), found: (chain n $v t o)")))
!(assertEqual (chain n v t) (Error (chain n v t) "expected: (chain <nested> (: <var> Variable) <templ>), found: (chain n v t)"))
!(assertAlphaEqualToResult (chain n $v) ((Error (chain n $v) "expected: (chain <nested> (: <var> Variable) <templ>), found: (chain n $v)")))

; ── chain: atom template (interpreter.rs:1664-1665) ──────────────────────────
!(assertEqual (chain (A () 6 y) $x (bar $x)) (bar (A () 6 y)))

; ── chain: evaluation (interpreter.rs:1671-1673) ─────────────────────────────
; (= (foo $a B) $a) already in space
!(assertEqual (chain (eval (foo A $b)) $x (bar $x)) (bar A))

; ── chain: nested evaluation (interpreter.rs:1678-1680) ──────────────────────
!(assertEqual (chain (chain (eval (foo A $b)) $x (bar $x)) $y (baz $y)) (baz (bar A)))

; ── chain: nested value (interpreter.rs:1685) ────────────────────────────────
!(assertEqual (chain (chain A $x (bar $x)) $y (baz $y)) (baz (bar A)))

; ── chain: expression non-determinism (interpreter.rs:1690-1701) ─────────────
(= (color2) red)
(= (color2) green)
(= (color2) blue)
!(assertEqualToResult (chain (eval (color2)) $x (bar $x)) ((bar red) (bar green) (bar blue)))

; ── chain: return Empty (interpreter.rs:1706) ────────────────────────────────
!(assertEqual (chain Empty $x (bar $x)) (bar Empty))

; ── chain: keep var from evaluated part (interpreter.rs:1712-1713) ───────────
(= (even 4) True)
!(assertEqual (chain (eval (even $x)) $res (= (is-even $x) $res)) (= (is-even 4) True))

; ── unify: incorrect args (interpreter.rs:1719-1722) ─────────────────────────
!(assertEqual (unify a p t e o) (Error (unify a p t e o) "expected: (unify <atom> <pattern> <then> <else>), found: (unify a p t e o)"))
!(assertEqual (unify a p t) (Error (unify a p t) "expected: (unify <atom> <pattern> <then> <else>), found: (unify a p t)"))

; ── unify: then-branch (interpreter.rs:1727) ─────────────────────────────────
!(assertEqual (unify (A $b) ($a B) ($a $b) Empty) (A B))

; ── unify: else-branch (interpreter.rs:1733) ─────────────────────────────────
!(assertEqual (unify (A $b C) ($a B D) ($a $b) Empty) Empty)

; ── decons-atom: incorrect args (interpreter.rs:1740-1744) ───────────────────
!(assertEqual (decons-atom a) (Error (decons-atom a) "expected: (decons-atom (: <expr> Expression)), found: (decons-atom a)"))
!(assertEqual (decons-atom (a) (b)) (Error (decons-atom (a) (b)) "expected: (decons-atom (: <expr> Expression)), found: (decons-atom (a) (b))"))
!(assertEqual (decons-atom) (Error (decons-atom) "expected: (decons-atom (: <expr> Expression)), found: (decons-atom)"))

; ── decons-atom: empty / single / list (interpreter.rs:1750-1762) ────────────
!(assertEqual (decons-atom ()) (Error (decons-atom ()) "expected: (decons-atom (: <expr> Expression)), found: (decons-atom ())"))
!(assertEqual (decons-atom (a)) (a ()))
!(assertEqual (decons-atom (a b c)) (a (b c)))

; ── cons-atom: incorrect args (interpreter.rs:1769-1773) ─────────────────────
!(assertEqual (cons-atom a (e) o) (Error (cons-atom a (e) o) "expected: (cons-atom <head> (: <tail> Expression)), found: (cons-atom a (e) o)"))
!(assertEqual (cons-atom a e) (Error (cons-atom a e) "expected: (cons-atom <head> (: <tail> Expression)), found: (cons-atom a e)"))
!(assertEqual (cons-atom a) (Error (cons-atom a) "expected: (cons-atom <head> (: <tail> Expression)), found: (cons-atom a)"))

; ── cons-atom: empty / single / list (interpreter.rs:1779-1791) ──────────────
!(assertEqual (cons-atom a ()) (a))
!(assertEqual (cons-atom a (b)) (a b))
!(assertEqual (cons-atom a (b c)) (a b c))

; ── function: error on no return (interpreter.rs:1813-1819) ──────────────────
!(assertEqual (function (SomeValue)) (Error (SomeValue) NoReturn))
(= (foo-nr) (function (SomeValue)))
!(assertEqual (eval (foo-nr)) (Error (foo-nr) NoReturn))

; ── Turing machine: busy beaver (interpreter.rs:1823-1865) ───────────────────
(= (tm $rule $state $tape)
  (function (eval (tm-body $rule $state $tape))) )
(= (tm-body $rule $state $tape)
  (unify $state HALT
    (return $tape)
    (chain (eval (read $tape)) $char
      (chain (eval ($rule $state $char)) $res
        (unify $res ($next-state $next-char $dir)
          (chain (eval (move $tape $next-char $dir)) $next-tape
            (eval (tm-body $rule $next-state $next-tape)) )
          (return (Error (tm-body $rule $state $tape) "Incorrect state")) )))))
(= (read ($head $hole $tail)) $hole)
(= (move ($head $hole $tail) $char N) ($head $char $tail))
(= (move ($head $hole $tail) $char L) (function
  (chain (cons-atom $char $head) $next-head
    (chain (decons-atom $tail) $list
      (unify $list ($next-hole $next-tail)
        (return ($next-head $next-hole $next-tail))
        (return ($next-head 0 ())) )))))
(= (move ($head $hole $tail) $char R) (function
  (chain (cons-atom $char $tail) $next-tail
    (chain (decons-atom $head) $list
      (unify $list ($next-hole $next-head)
        (return ($next-head $next-hole $next-tail))
        (return (() 0 $next-tail)) )))))
(= (busy-beaver A 0) (B 1 R))
(= (busy-beaver A 1) (C 1 L))
(= (busy-beaver B 0) (A 1 L))
(= (busy-beaver B 1) (B 1 R))
(= (busy-beaver C 0) (B 1 L))
(= (busy-beaver C 1) (HALT 1 N))
!(assertEqual (eval (tm busy-beaver A (() 0 ()))) ((1 1) 1 (1 1 1)))

; ── minimal metta smoketest (interpreter.rs:1869-1899) ───────────────────────
; (NOTE: the final collapse-bind raw-dump sub-assert of this fn is RESIDUE — see header (d).)
(= (foo-st $a B) $a)
(= (fu $x) (function (chain (eval (foo-st $x B)) $r (return $r))))
(= (color3) red)
(= (color3) green)
(= (color3) blue)
!(assertEqual (chain (chain A $x $x) $y $y) A)
!(assertEqual (chain (chain (eval (foo-st A $b)) $x (bar $x)) $y (baz $y)) (baz (bar A)))
!(assertEqual (chain (chain (eval (fu A)) $x (bar $x)) $y (baz $y)) (baz (bar A)))
!(assertEqual (unify (A $b) ($a B) ($a $b) Empty) (A B))
!(assertEqual (decons-atom (a b c)) (a (b c)))
!(assertEqual (cons-atom a (b c)) (a b c))
!(assertEqualToResult (chain (collapse-bind (eval (color3))) $collapsed (superpose-bind $collapsed)) (red green blue))
!(assertAlphaEqualToResult ((P $a B) $a) (((P $a B) $a)))

; ── variable substitution after superpose (interpreter.rs:2097-2107) ─────────
(= (foo-sp a) xa)
(= (foo-sp b) xb)
!(assertEqualToResult
  (chain (collapse-bind (eval (foo-sp $a))) $collapsed
    (chain (superpose-bind $collapsed) $x
      ($x $a)))
  ((xa a) (xb b)))
