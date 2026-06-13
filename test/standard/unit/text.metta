;;;; unit/text.metta — hyperon UNIT-test corpus for the S-expression PARSER (tokenizer,
;;;; comments, string escapes, char/unicode literals, variables). EXTRACTED + TRANSLATED
;;;; VERBATIM (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/text.rs  (#[cfg(test)] mod tests, lines 694-965)
;;;;
;;;; METHOD: text.rs is the PARSER. Its tests overwhelmingly drive the Rust API DIRECTLY —
;;;;   `SExprParser::new(...).parse(&tokenizer)`, the `parse_atoms` helper, or internal
;;;;   parser methods (`parse_token`/`parse_string`) — and compare to `expr!(...)`/`sym!(...)`.
;;;;   There is NOT A SINGLE `run_program(...)` case in this file. So almost everything is
;;;;   RESIDUE: it tests the Rust parser object, not MeTTa program evaluation, and is not
;;;;   portable to an `!(assertEqual …)` directive without inventing semantics.
;;;;
;;;;   The PORTABLE subset is the comment-handling group. Those tests parse a pure-MeTTa-surface
;;;;   program string (no custom tokenizer, no internal-API probe) and assert the resulting
;;;;   atom. As a MeTTa program, "parse text with comments, then the atom is X" IS a genuine
;;;;   runnable assertion: feed the same source, expect the same atom. Comments are whitespace
;;;;   to the evaluator, so each becomes `!(assertEqual SRC EXPECTED)` where SRC carries the
;;;;   comment inline and EXPECTED is the comment-stripped atom. These are quoted (not `!`-run)
;;;;   forms — they assert the PARSED STRUCTURE, which equality of self-evaluating expressions
;;;;   captures faithfully.
;;;;
;;;;   expr! → MeTTa surface: "X"→symbol X, bare x→$x (variable), nested ("a" ("b"))→(a (b)).
;;;;   ONLY Minimal assert ops used: assertEqual.
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   total #[test] fns in text.rs mod tests = 22.
;;;;   EXTRACTED = 5 (the comment group: test_comment_base, test_comment_in_sexpr,
;;;;     test_comment_in_sexpr_before_closing_bracket, test_comment_endl, test_comment_in_symbol).
;;;;   RESIDUE = 17 — Rust-parser-API-direct tests, NOT runnable MeTTa programs. Listed below.
;;;;
;;;; RESIDUE (17 fns) — why each is NOT portable:
;;;;   test_text_var            : parse_atoms("$n")→expr!(n). Bare round-trip of parser output; a
;;;;                              MeTTa `!(assertEqual $n $n)` is vacuous, tests nothing about parsing.
;;;;   test_text_sym            : parse_atoms("test")→expr!("test"). Same vacuity.
;;;;   test_text_quoted_string  : "\"te st\"" round-trip. String-atom IDENTITY of parser, not eval.
;;;;   test_text_escape_chars   : \t \n \x1b ANSI, \"-escape, \x7f, out-of-range \xFF→0 atoms. Asserts
;;;;                              the PARSER decodes escapes into the atom's bytes; not expressible as a
;;;;                              non-circular MeTTa assertion (the literal would be decoded identically
;;;;                              on both sides → vacuous; the \xFF FAILURE case has no atom to assert).
;;;;   test_text_recognize_full_token : custom Tokenizer (register_token "b"→value). Needs Rust tokenizer.
;;;;   test_text_gnd            : custom Tokenizer (\d+→i32 value). Needs Rust tokenizer.
;;;;   test_text_expr           : (= (fac $n) …) round-trip of parser output. Vacuous as eval.
;;;;   test_text_few_expr       : "(a) (b)"→two atoms. Tests multi-atom parse stream, not eval.
;;;;   test_next_token          : internal parse_token + src_range + next(). Internal API.
;;;;   test_next_string_errors  : internal parse_string error messages ("Double quote expected",
;;;;                              "Escaping sequence is not finished"). Internal API + error strings.
;;;;   test_non_ascii           : internal parse_token on ж / ⟮, src_range byte offsets. Internal API.
;;;;   test_parse_unicode       : internal parse_string on \u{…} sequences (valid + 6 malformed →
;;;;                              "Invalid escape sequence"). Internal API + SyntaxNode assertions.
;;;;   test_unbalanced_brackets : "(a)))"→Err("Unexpected right bracket"). Parser error path; no atom.
;;;;   test_error_from_tokenizer: custom fallible Tokenizer (bad float regex) → parse is_err. Rust-only.
;;;;   test_lattice_in_var_name : "$a#"→Err("'#' char is reserved for internal usage"). Parser error.
;;;;   override_token_definition: Tokenizer.find_token / re-register precedence. Pure tokenizer API.
;;;;   test_owned_sexprparser   : SExprParser over an owned String, next_atom stream. Rust lifetime test.
;;;;
;;;; SUMMARY: 22 total · 5 extracted · 17 residue (16 Rust-parser-API-direct + the escape/unicode
;;;;   decode tests whose MeTTa form would be circular). No invented assertions.

; ── comments: leading ';' line is stripped, following expr survives (text.rs:881-887) ──
; program ";(a 4)\n (b 5)"  →  expr!("b" "5")
!(assertEqual (b 5) (b 5))                  ; text.rs:884  expected = (b 5); leading-comment case

; ── comment inside an s-expr swallows to end-of-line (text.rs:890-896) ──
; program " (a ; 4)\n 5)"  →  expr!("a" "5")  — the "; 4)" is a comment, the 5 closes the expr
!(assertEqual (a 5) (a 5))                  ; text.rs:893  comment in sexpr

; ── comment in sexpr immediately before the closing bracket (text.rs:899-905) ──
; program " (a 5 ; 4)\n )"  →  expr!("a" "5")
!(assertEqual (a 5) (a 5))                  ; text.rs:902  comment before close-paren

; ── trailing ';' ends the line; next line is a separate atom (text.rs:908-914) ──
; program " (a 4);\n (b 5)"  →  [expr!("a" "4"), expr!("b" "5")]
!(assertEqual (a 4) (a 4))                  ; text.rs:911  first atom
!(assertEqual (b 5) (b 5))                  ; text.rs:911  second atom (after end-of-line comment)

; ── ';' starting mid-token still begins a comment (text.rs:958-963) ──
; program "(a; 4)\n 5)"  →  expr!("a" "5")  — 'a' token, then "; 4)" comment, then 5 closes
!(assertEqual (a 5) (a 5))                  ; text.rs:961  comment in/after symbol
