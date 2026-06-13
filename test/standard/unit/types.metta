;;;; unit/types.metta — hyperon UNIT-test corpus for the type system (get-type / check-type /
;;;; type-checking). EXTRACTED + TRANSLATED VERBATIM (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/types.rs  (#[cfg(test)] mod tests, lines 641-1319)
;;;; Method: each `run_program("PROG")` + `assert_eq!(.., Ok(vec![vec![EXPECTED]]))` becomes
;;;;   one self-checking directive. expr! → MeTTa surface: "X"→symbol X, bare x→$x (variable),
;;;;   {Number::Integer n}→n (Int), {Number::Float f}→f (Float) — numeric TYPE preserved.
;;;;   GROUND expected → (assertEqual …). VARIABLE-containing expected → (assertAlphaEqualToResult
;;;;   … (R)). MULTI-result → (assertEqualToResult … (R1 R2)). assertAlphaEqual is NOT in Minimal.
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   types.rs test fns = 38 total.
;;;;   run_program / string-form-MeTTa-eval cases extracted = 0.
;;;;   RESIDUE (NOT portable) = 38 (ALL of them).
;;;;
;;;; WHY ZERO EXTRACTED — the whole module is Rust-direct residue:
;;;;   Unlike stdlib/atom.rs (which drives builtins through `run_program("!(...)")` and asserts
;;;;   `Ok(vec![vec![...]])`), types.rs NEVER calls run_program. Every test constructs Rust `Atom`
;;;;   / `DynSpace` values and invokes the Rust type-checking helpers DIRECTLY:
;;;;       check_type(&space, &atom, &typ)            -> bool      (assert!/assert!(!))
;;;;       validate_atom(&space, &atom)               -> bool      (assert!/assert!(!))
;;;;       get_atom_types(&space, &atom)              -> Vec<AtomType>  (assert_eq!/assert_eq_no_order!)
;;;;       get_atom_types_internal(&space, &atom)     -> Vec<AtomType>  (assert_eq!)
;;;;   These return Rust `bool` / `Vec<AtomType>` (an internal struct carrying Application / value /
;;;;   error TypeInfo via the typ!/typ_app!/typ_err! macros), NOT a MeTTa result vector. There is no
;;;;   MeTTa `!(...)` program text to copy verbatim, and surfacing them as `get-type`/`assertEqual`
;;;;   directives would be INVENTION, not extraction — so they are recorded as residue here.
;;;;   The .rs:598/.rs:631 `metta.run(SExprParser::new(...))` calls are in DOC-COMMENT examples
;;;;   (check_type / validate_atom rustdoc), not in the #[cfg(test)] module, and assert nothing.
;;;;
;;;;   This type-checking behaviour IS covered at the MeTTa/Julia level by hand-written Core tests
;;;;   (see test_types.jl — the gradual type system: fn-application return-type inference, BadArgType
;;;;   checking, meta-type acceptance), which is the intended home for the residue below.
;;;;
;;;; RESIDUE ACCOUNTING (per test fn — helper used, hence not portable; types.rs:NNN):
;;;;   types.rs:697  test_check_type ................................... check_type (direct)
;;;;   types.rs:719  test_check_expr_type .............................. check_type (direct)
;;;;   types.rs:737  nested_type ...................................... check_type (direct)
;;;;   types.rs:749  nested_loop_type ................................. check_type (direct)
;;;;   types.rs:761  test_validate_atom ............................... validate_atom (direct)
;;;;   types.rs:769  validate_symbol .................................. validate_atom (direct)
;;;;   types.rs:775  simple_types ..................................... check_type (direct)
;;;;   types.rs:786  arrow_type ....................................... check_type (direct)
;;;;   types.rs:795  arrow_allows_specific_type ....................... validate_atom + check_type (direct)
;;;;   types.rs:808  validate_basic_expr .............................. validate_atom (direct)
;;;;   types.rs:817  simple_dep_types ................................. check_type + validate_atom (direct)
;;;;   types.rs:861  dep_types_prop ................................... validate_atom + check_type (direct)
;;;;   types.rs:877  arrow_allows_undefined_type ...................... validate_atom (direct)
;;;;   types.rs:886  arrow_has_type_of_returned_value ................. check_type (direct)
;;;;   types.rs:896  nested_arrow_type ................................ validate_atom (direct)
;;;;   types.rs:906  nested_return_type ............................... validate_atom (direct)
;;;;   types.rs:917  validate_non_functional_expression ............... validate_atom (direct)
;;;;   types.rs:927  check_type_non_functional_expression ............. check_type (direct)
;;;;   types.rs:938  get_atom_types_symbol ............................ get_atom_types (direct)
;;;;   types.rs:948  get_atom_types_variable .......................... get_atom_types (direct)
;;;;   types.rs:954  get_atom_types_grounded_atom ..................... get_atom_types (direct)
;;;;   types.rs:975  get_atom_types_variables_are_substituted_for_grounded_atom_type .. get_atom_types (direct)
;;;;   types.rs:986  parameterized_atom_types_should_not_conflict ..... get_atom_types (direct)
;;;;   types.rs:1007 get_atom_types_tuple ............................. get_atom_types (direct)
;;;;   types.rs:1022 get_atom_types_function_call_and_tuple ........... get_atom_types (direct)
;;;;   types.rs:1032 get_atom_types_empty_expression .................. get_atom_types (direct)
;;;;   types.rs:1038 get_atom_types_function_call_simple .............. get_atom_types (direct)
;;;;   types.rs:1048 get_atom_types_function_call_meta_types .......... get_atom_types (direct)
;;;;   types.rs:1086 get_atom_types_function_call_incorrect_arguments .. get_atom_types (direct)
;;;;   types.rs:1095 get_atom_types_function_call_parameterized_types .. get_atom_types (direct)
;;;;   types.rs:1109 check_type_parameterized_type_no_variable_bindings  check_type (direct)
;;;;   types.rs:1120 check_type_dependent_type_symbol_param ........... check_type (direct)
;;;;   types.rs:1139 check_type_dependent_type_grounded_param ......... check_type (direct)
;;;;   types.rs:1158 check_type_accept_meta_type ...................... check_type (direct)
;;;;   types.rs:1196 check_type_return_meta_type ...................... check_type (direct)
;;;;   types.rs:1238 validate_atom_accept_meta_type ................... validate_atom (direct)
;;;;   types.rs:1270 validate_atom_return_meta_type ................... validate_atom (direct)
;;;;   types.rs:1311 tuple_with_undefined_member ...................... get_atom_types_internal (direct)
;;;;
;;;; NET: 38 test fns · 0 run_program cases · 38 residue (all Rust-helper-direct, none portable).
;;;; No directives are emitted: there is nothing to translate without inventing MeTTa programs.
