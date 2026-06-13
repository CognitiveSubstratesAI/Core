;;;; unit/space.metta — hyperon UNIT-test corpus for space ops (add-atom, remove-atom,
;;;; get-atoms, new-space, new-state/get-state/change-state!, mod-space!). EXTRACTED +
;;;; TRANSLATED VERBATIM (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/runner/stdlib/space.rs  (test mod, lines 226-324)
;;;; Method: each runner.run("PROG") whose per-directive result is a plain MeTTa-surface
;;;;   Ok(vec![vec![EXPECTED]]) becomes one self-checking directive. expr!/metta! → MeTTa
;;;;   surface: "X"→symbol X, bare x→$x (variable). GROUND expected → (assertEqual …);
;;;;   VARIABLE-containing expected → (assertAlphaEqualToResult … (R)); multiple results →
;;;;   (assertEqualToResult … (R1 R2)). Multi-statement programs keep the WHOLE program
;;;;   string intact (data/bind! definitions before the final `!` directive).
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   space.rs #[cfg(test)] mod tests = 6 test fns total.
;;;;   run_program / runner.run extracted = 1 (state_ops → get-state directive).
;;;;     state_ops runs 4 `!` directives; only get-state has a plain MeTTa-surface expected
;;;;     value (F aa). The other three expected values are Rust-constructed OPAQUE grounded
;;;;     atoms — bind! → UNIT_ATOM, change-state! → Atom::gnd(StateAtom) [Display "(State …)"],
;;;;     2nd change-state! → (Error (<gnd ChangeStateOp> <gnd StateAtom> (F b)) (BadArgType 2 A B))
;;;;     embedding grounded-atom payloads not expressible as faithful MeTTa surface — OMITTED
;;;;     (cannot reconstruct the gnd payloads as surface text without fabricating them).
;;;;   RESIDUE — Rust-op-direct OpStruct{}.execute(...) / runner.run with grounded-atom expected,
;;;;     NO portable MeTTa-surface program (gated by hand-written Julia space tests instead):
;;;;     (1) mod_space_op       — runner.run, but asserts result[2] == [<gnd ModSpaceOp> stdlib];
;;;;                              expected head is a Rust-constructed grounded module-space op.
;;;;     (2) remove_atom_op     — RemoveAtomOp{}.execute direct; asserts UNIT + space contents via
;;;;                              collect_atoms (space-introspection, not a query result).
;;;;     (3) get_atoms_op       — GetAtomsOp{}.execute direct; assert_eq_no_order vs collect_atoms.
;;;;     (4) new_space_op       — NewSpaceOp{}.execute direct; asserts empty space (no MeTTa value).
;;;;     (5) add_atom_op        — AddAtomOp{}.execute direct; asserts UNIT + collect_atoms contents.
;;;;     (5 residue fns + 3 omitted state_ops directives.) These test Rust API / space-mutation
;;;;     side-effects via collect_atoms() introspection, not value-returning MeTTa programs.

; ── state_ops: get-state after change-state! (space.rs:301-323) ───────────────
; new-state holds (F a); change-state! mutates it to (F aa); get-state reads it back.
; Type decls (: a A) etc. carried verbatim from the program; only the get-state
; directive yields a plain MeTTa-surface value, so only that one is asserted.
(: a A)
(: aa A)
(: b B)
(: F (-> $t $t))
!(bind! &stateAB (new-state (F a)))
!(change-state! &stateAB (F aa))
!(assertEqual (get-state &stateAB) (F aa))
