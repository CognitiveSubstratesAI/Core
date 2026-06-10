; core.metta — Core MeTTa standard library
; Pure MeTTa rules, hot-reloadable, introspectable via (match &self (= ...) ...)
;
; Cross-verified against:
;   CeTTa/lib/stdlib.metta
;   hyperon-experimental/lib/src/metta/runner/stdlib/stdlib.metta
;   PeTTa/lib/lib_he.metta (HE-MeTTa compatibility)
;   MeTTa-Compiler/src/backend/eval/control_flow.rs
;   docs/research/metta-language-spec.md

; ── Type declarations ─────────────────────────────────────────────────────────
(: = (-> $t $t %Undefined%))
(: if (-> Bool Atom Atom $t))
(: if-equal (-> Atom Atom Atom Atom %Undefined%))
(: noeval (-> Atom Atom))
(: if-error (-> Atom Atom Atom %Undefined%))
(: ErrorType Type)
(: Error (-> Atom Atom ErrorType))
(: Empty (-> Atom))
(: NotReducible Atom)
(: id (-> $t $t))
(: not (-> Bool Bool))
(: or (-> Bool Bool Bool))
(: and (-> Bool Bool Bool))

; ── Boolean / conditional ─────────────────────────────────────────────────────
; Per CeTTa stdlib.metta lines 354-355 and MeTTa spec §Special Expressions

(= (if True $then $else) $then)
(= (if False $then $else) $else)

(= (if-equal $a $b $then $else)
   (if (== $a $b) $then $else))

; ── Identity and no-eval ──────────────────────────────────────────────────────
; Per CeTTa stdlib.metta and hyperon-experimental stdlib.metta

(= (id $x) $x)

(= (noeval $x) $x)

; ── Error handling ────────────────────────────────────────────────────────────
;
; if-error — eager rewrite of H-E's CPS helper. The previous version used
; function/chain/unify/return — H-E's lazy CPS style. Under PRIMUS's eager
; evaluator the unevaluated-branch property of those helpers doesn't hold
; (rule arguments are pre-evaluated before the rule body fires), so the
; CPS form returned garbage. The eager rewrite uses `if` — the one
; construct that IS lazy in branches in this interpreter — and grounded
; get-metatype/car-atom for structural inspection.
;
; SEMANTIC DIVERGENCE FROM H-E: the result is correct (returns $then on
; Error, $else otherwise) but the branches are NOT lazy. Both $then and
; $else are evaluated when if-error is called (they're rule arguments).
; Programs that relied on H-E's lazy short-circuit to skip costly work
; on the unselected branch will still run that work under PRIMUS. This
; is the eager-evaluator decision (see commit history / project notes);
; full short-circuit would require making if-error a special form.
;
; Removed alongside the H-E CPS layer (all unused in this tree, found
; via grep across stdlib + src + test + lib):
;   atom-subst        — internal plumbing, never API surface
;   return-on-error   — trivially `(if-error $r $r $next)` if needed
;   if-decons-expr    — internal plumbing; use `decons-atom` + `if` directly

(= (if-error $atom $then $else)
   (if (== (get-metatype $atom) Expression)
       (if (== (car-atom $atom) Error)
           $then
           $else)
       $else))

; ── Type predicates (MeTTa-level wrappers) ───────────────────────────────────
; Grounded: get-metatype, is-number, is-symbol, is-variable, is-expression

; OVER-PRODUCE bin fix: the two-clause version below fires BOTH clauses
; on an arrow type under streaming `=`, returning [True, False] — a
; contradiction. Single structural clause via `car-atom` returns exactly
; one result regardless of rewriter shape.
;
;   was:
;     (= (is-function (-> $a $b)) True)
;     (= (is-function $x) False)
(= (is-function $x)
   (if (== (car-atom $x) ->)
       True
       False))

; ── Quoting ───────────────────────────────────────────────────────────────────
; Per hyperon-experimental and CeTTa

(= (unquote (quote $atom)) $atom)

; ── HE-MeTTa compatibility (PeTTa lib_he.metta) ──────────────────────────────

(= (if-equal2 $a $b $then $else)
   (if (== $a $b) $then $else))

(= (noreduce-eq $a $b) (== $a $b))

(= (match-types $a $b $then $else)
   (if (== $a $b) $then $else))

(= (first-from-pair ($a $b)) $a)

; ── boolean / list operators promoted from per-library copies ─────────────────
; Consolidated 2026-06-10 (see docs/PRIMITIVE_SURFACE_AND_ECOSYSTEM_TOOLING_2026-06-10.md).
; `xor` IS hyperon-canonical (arithmetics.rs) — kept as a thin stdlib rule to keep the
; grounded tier minimal. `is-member`/`~=`/`===` are PeTTa/MeTTaLog-compat (not hyperon-
; canonical), needed by MeTTaLog-sourced ports (e.g. MOSES). Previously each was redefined
; locally; now there is one canonical home. (`!=` cannot be a stdlib rule — the parser
; tokenizes it as `! =`; use `~=`.)
(= (xor $a $b) (not (== $a $b)))
(= (is-member $x $xs) (member $x $xs))
(= (~=  $a $b) (not (== $a $b)))
(= (=== $a $b) (== $a $b))

(= (evalc $expression &self)
   (eval $expression))

; ── Assertion helpers (for testing) ──────────────────────────────────────────
; Per MeTTa language reference (Asserts §): assertEqual/assertEqualToResult
; return the unit value () on match and an Error-expression on mismatch.

(= (assertEqual $a $b)
   (if (== $a $b)
       ()
       (Error (assertEqual $a $b) AssertionFailed)))

(= (assertAlphaEqual $a $b)
   (if (== $a $b)
       ()
       (Error (assertAlphaEqual $a $b) AssertionFailed)))

; assertEqualToResult — evaluates $expr, treats $expected as a literal set of
; expected results (no evaluation of the second arg). Per MeTTa spec, the
; expected-results arg is a *set* even if it contains one element, so callers
; write (assertEqualToResult (+ 1 2) (3)) — the bracket around 3 is mandatory.
;
; Implementation uses collapse to gather all non-deterministic results of
; $expr and compares with == against the literal expected set.
(= (assertEqualToResult $expr $expected)
   (if (== (collapse $expr) $expected)
       ()
       (Error (assertEqualToResult $expr $expected) AssertionFailed)))
