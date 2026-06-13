;;;; unit/atom.metta — hyperon UNIT-test corpus for atom ops (the layer the 26 integration
;;;; scripts never gated). EXTRACTED + TRANSLATED VERBATIM (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/runner/stdlib/atom.rs  (test mod, lines 484-555)
;;;; Method: each `run_program("PROG")` + `assert_eq!(.., Ok(vec![vec![EXPECTED]]))` becomes
;;;;   one self-checking directive. expr! → MeTTa surface: "X"→symbol X, bare x→$x (variable),
;;;;   {Number::Integer n}→n (Int), {Number::Float f}→f (Float) — numeric TYPE preserved.
;;;;   GROUND expected → (assertEqual …). VARIABLE-containing expected → (assertAlphaEqualToResult
;;;;   … (R)) [alpha-equality up to var-renaming; assertAlphaEqual is NOT in Minimal].
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   atom.rs run_program cases = 26 total → 24 translated here.
;;;;   KNOWN-NOT-IN-MINIMAL (expected FAIL until implemented): min-atom, max-atom — only the
;;;;     primary value case of each kept (2); their 6 error/edge cases OMITTED (all fail identically
;;;;     as "op missing", no extra signal).
;;;;   RESIDUE — Rust-op-direct assert_eq!(res, …) with NO MeTTa program, NOT portable (gated by
;;;;     hand-written test/standard/test_atoms.jl instead): size_atom_op, min_atom_op, max_atom_op,
;;;;     index_atom_op, unique_op_, index_atom_to_key (6 fns). Duplicate MeTTa-level coverage above
;;;;     OR test trie-key internals.

; ── car-atom (atom.rs:491-498) ───────────────────────────────────────────────
!(assertEqual (car-atom (A $b)) A)
!(assertAlphaEqualToResult (car-atom ($a B)) ($a))
!(assertEqual (car-atom ()) (Error (car-atom ()) "car-atom expects a non-empty expression as an argument"))
!(assertEqual (car-atom A) (Error (car-atom A) "car-atom expects a non-empty expression as an argument"))

; ── cdr-atom (atom.rs:503-507) ───────────────────────────────────────────────
!(assertEqual (cdr-atom (a b c)) (b c))
!(assertAlphaEqualToResult (cdr-atom ($a b $c)) ((b $c)))
!(assertEqual (cdr-atom ()) (Error (cdr-atom ()) "cdr-atom expects a non-empty expression as an argument"))
!(assertEqual (cdr-atom a) (Error (cdr-atom a) "cdr-atom expects a non-empty expression as an argument"))
!(assertAlphaEqualToResult (cdr-atom $a) ((Error (cdr-atom $a) "cdr-atom expects a non-empty expression as an argument")))

; ── size-atom (atom.rs:512-513) ──────────────────────────────────────────────
!(assertEqual (size-atom (5 4 3 2 1)) 5)
!(assertEqual (size-atom ()) 0)

; ── min-atom / max-atom (atom.rs:518-529) — KNOWN NOT-IN-MINIMAL (expected FAIL) ─
!(assertEqual (min-atom (5 4 5.5)) 4)
!(assertEqual (max-atom (5 4 5.5)) 5.5)

; ── index-atom (atom.rs:534-535) ─────────────────────────────────────────────
!(assertEqual (index-atom (5 4 3 2 1) 2) 3)
!(assertEqual (index-atom (A B C D E) 5) (Error (index-atom (A B C D E) 5) "Index is out of bounds"))

; ── filter-atom (atom.rs:540-542) — the LIVE bug: computed pred (eval (if-error …)) ─
!(assertEqual (filter-atom () $x (eval (if-error $x False True))) ())
!(assertAlphaEqualToResult (filter-atom (a (b) $c) $x (eval (if-error $x False True))) ((a (b) $c)))
!(assertAlphaEqualToResult (filter-atom (a (Error (b) "Test error") $c) $x (eval (if-error $x False True))) ((a $c)))

; ── map-atom (atom.rs:547-548) ───────────────────────────────────────────────
!(assertEqual (map-atom () $x ($x mapped)) ())
!(assertAlphaEqualToResult (map-atom (a (b) $c) $x (mapped $x)) (((mapped a) (mapped (b)) (mapped $c))))

; ── foldl-atom (atom.rs:553-554) ─────────────────────────────────────────────
!(assertEqual (foldl-atom () 1 $a $b (eval (+ $a $b))) 1)
!(assertEqual (foldl-atom (1 2 3) 0 $a $b (eval (+ $a $b))) 6)

;;;; ─────────────────────────────────────────────────────────────────────────────
;;;; CORE-ADDED REGRESSION (not in hyperon's atom.rs) — the bare-predicate filter-atom bug.
;;;; hyperon ONLY tests filter-atom with eval-WRAPPED predicates (line 540-542 above, all green);
;;;; MOSES (faithful from metta-moses) uses BARE predicates — (isLiteral $e), (> $x 1) — which
;;;; trigger a Minimal `chain`(bare computed head) + `eval(if)` continuation bug → ERROR. This is
;;;; the root of the whole M6 reduce-to-elegance cluster failing. NO upstream suite covers it, so
;;;; these gate it directly. EXPECTED-FAIL until the interpreter bug is fixed (baseline records it).
(= (gt1 $x) (> $x 1))
!(assertEqual (filter-atom (1 2 3) $x (gt1 $x)) (2 3))     ; bare user-rule predicate (MOSES pattern)
!(assertEqual (filter-atom (1 2 3) $x (> $x 1)) (2 3))     ; bare grounded predicate
