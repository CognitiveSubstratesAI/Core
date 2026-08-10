; mettail.metta — the FINE-GRAINED GSLT of MeTTa: minimal MeTTa presented as G = (Σ, E, R).
;
; This is the first presentation of a REAL language in this tree. Everything before it was a toy
; algebra (Monoid, Rig, Graph) — first-order, and therefore unable to present anything with binders.
;
; SOURCE: `docs/specs/metta grammar/metta_language_spec.md` §3, the NORMATIVE instruction table.
; The spec calls minimal MeTTa "an assembly language for MeTTa" and says these atoms "are not part of
; the standard library, but are recognized and evaluated by the interpreter".
;
; WHY THE FINE-GRAINED ONE FIRST. Whitepaper §3.4.1 keeps "two GSLTs … fine-grained
; (implementation/optimization) and coarse-grained (developer-facing types)". This is the first: it is
; small, closed, and TRANSCRIBED from a normative table rather than designed. The coarse-grained
; surface presentation comes later, because §3.4.1 puts a proof obligation on any claimed
; correspondence between the two — "the typed maps, assumptions, theorem statement, proof artifact,
; and replayable environment" — which must not be improvised.
;
; ─── WHAT IS COMPLETE HERE AND WHAT IS NOT ──────────────────────────────────────────────────────
;   Σ  COMPLETE — all 13 instructions, transcribed with their arities from the table.
;   E  EMPTY, DELIBERATELY — the spec states no structural congruence for minimal MeTTa. Upstream
;      does the same where none exists: `mettail-rust/languages/src/lambda.rs` ships
;      `equations { // extensionality? }`. Writing none is honest; inventing some is not.
;   R  TWO RULES ONLY, and the gap is the point. §5's evaluation algorithm is an ABSTRACT MACHINE —
;      metatype dispatch, error filtering, a mutable "mark $a as evaluated" step (§5.1) — not a
;      rewrite system. Turning it into premised inference rules is real work with real judgement in
;      it, so only what the table states outright is written below.
;
; ─── R IS NOW CHECKED, NOT ASSERTED ─────────────────────────────────────────────────────────────
; `gslt/Reduce.jl` executes this file, and `test_mettail_presentation.jl` runs FunctionReturn against
; `Eval.jl` on the same terms and requires agreement. That is the condition on growth: a rule goes in
; when the differential can justify it, not when it reads plausibly. ChainStep predates the engine and
; is premised; `Relation.jl` discharges premises, so it DOES fire now, and the differential asserts the
; agreement instead of the gap. What remains open is stated there too: R has no SUBSTITUTION rule, so
; the presentation reaches `(chain a $v $v)` and stops where the interpreter reaches `a`.
;
; ─── WHY THIS IS A LAMBDA THEORY, NOT A FIRST-ORDER SIGNATURE ───────────────────────────────────
; `(chain <atom> <var> <template>)` — "substitute `<var>` in `<template>` with the result". The var
; is BOUND IN the template. So MeTTa's own assembly language has a binder, and the presentation needs
; `bind`/`scope` (upstream `bindNTerminal`/`absNTerminal`). Before the port to LeaTTa's model this
; file could not have been written at all.

(language MeTTaIL

  ; ── Σ, sorts ──────────────────────────────────────────────────────────────────────────────────
  ; Minimal MeTTa is essentially single-sorted — everything is an Atom — but the table's own
  ; vocabulary distinguishes two more: `<context space>` and `<type>`. Kept distinct because they
  ; are distinct in the source, not because our checker needs them.
  ;
  ; NO `literals` SECTION. Grounded values are Atoms at this level (the metatypes Symbol / Variable /
  ; Expression / Grounded are §2.4 META-types, not sorts). Literal carriers will matter for the
  ; COARSE-GRAINED surface presentation, where Int/Float/String are separate; asserting them here
  ; would be inventing structure the assembly language does not have.
  (types Atom Space Type)

  ; ── Σ, the 13 instructions (§3 table, in table order) ─────────────────────────────────────────
  (terms
    ; (eval <atom>) — one step of evaluation
    (: eval           (-> Atom Atom))

    ; (evalc <atom> <context space>) — one step in the context of the passed space
    (: evalc          (-> Atom Space Atom))

    ; (chain <atom> <var> <template>) — interpret <atom>, substitute <var> in <template> with it.
    ; THE BINDER: `v` is declared by (bind v Atom) and scopes over the template.
    (: chain          (-> Atom (bind v Atom) (scope v Atom) Atom))

    ; (unify <atom> <pattern> <then> <else>) — <then> on success, <else> otherwise
    (: unify          (-> Atom Atom Atom Atom Atom))

    ; (decons-atom <expression>) — head and tail
    (: decons-atom    (-> Atom Atom))

    ; (cons-atom <head> <tail>) — construct an expression
    (: cons-atom      (-> Atom Atom Atom))

    ; (function <body>) — evaluate <body> until (return <atom>) is hit
    (: function       (-> Atom Atom))

    ; (return <atom>) — finish the enclosing function
    (: return         (-> Atom Atom))

    ; (collapse-bind <atom>) — interpret, return a tuple of ALL results
    (: collapse-bind  (-> Atom Atom))

    ; (superpose-bind <result of collapse-bind>) — resume where collapse-bind stopped
    (: superpose-bind (-> Atom Atom))

    ; (metta <atom> <type> <space>) — evaluate in the interpreter, expecting <type>
    (: metta          (-> Atom Type Space Atom))

    ; (context-space) — the space the interpreter is using
    (: context-space  (-> Space))

    ; (call-native <name> <fn pointer> <args>) — call a host function.
    ; ⚠️ The spec notes it "cannot be called from a MeTTa program, but can be RETURNED by a grounded
    ; function for further evaluation". Present in Σ because it is an instruction; its restriction is
    ; a property of the evaluator, not of the signature.
    (: call-native    (-> Atom Atom Atom Atom)))

  ; ── E ─────────────────────────────────────────────────────────────────────────────────────────
  ; Empty. See the header: the spec states no structural congruence for minimal MeTTa.
  (equations)

  ; ── R ─────────────────────────────────────────────────────────────────────────────────────────
  ; ⚠️ INCOMPLETE, AND THE INCOMPLETENESS IS DELIBERATE. Only rules the §3 table states outright are
  ; here. Everything else — unify's success/failure dispatch, chain's substitution step, eval's
  ; atomspace search, collapse/superpose — is defined by §5's ALGORITHM, which is an abstract machine
  ; with metatype dispatch and a mutable evaluated-marker. Deriving inference rules from it is a
  ; separate piece of work; guessing them here would put invented semantics into the one artifact
  ; whose whole purpose is to be the faithful source.
  ;
  ; ⚠️ PATTERN VARIABLES WEAR MeTTa'S `$` SIGIL — `$X`, not `X`. Both rules below were written WITHOUT
  ; it in the first version of this file, which made them GROUND: `(function (return X))` matched the
  ; literal three-atom term containing the symbol `X` and nothing else. It was well-formed, it parsed,
  ; and it was inert. Upstream's own s-expr surface sigils for exactly this reason
  ; (`MeTTaIL/Runtime/Sexpr.lean:9,40`); the parser now rejects an unsigiled non-constructor.
  (rewrites
    ; QUOTED. Table: "(function <body>) — evaluate <body> until (return <atom>) is hit"; "(return
    ; <atom>) — finish evaluation of the enclosing function with <atom>". So a function whose body has
    ; reached a return IS that atom.
    (rewrite FunctionReturn () (~> (function (return $X)) $X))

    ; INFERRED, NOT QUOTED — flagged as such. Table: "(chain <atom> <var> <template>) — INTERPRET
    ; <atom>, substitute …". Interpreting the first argument means it reduces there, which is a
    ; congruence rule. Marked because it is read off the word "interpret" rather than written down,
    ; and because a congruence rule is exactly the kind of thing that is easy to assume and wrong.
    (rewrite ChainStep ((~> $A $A2)) (~> (chain $A $v $T) (chain $A2 $v $T)))))
