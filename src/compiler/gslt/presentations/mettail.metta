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
;   R  FOUR RULES, and the ceiling is the point. §5's evaluation algorithm is an ABSTRACT MACHINE —
;      metatype dispatch, error filtering, a mutable "mark $a as evaluated" step (§5.1) — not a
;      rewrite system. Four of the thirteen instructions ARE a rewrite system and are written below;
;      the other nine are not, and the closing section of this file says which and why, per
;      instruction. Every rule here agrees with `Eval.jl` on the differential corpus.
;
; ─── R IS CHECKED, NOT ASSERTED — AND THAT IS THE CONDITION ON ITS GROWTH ───────────────────────
; `gslt/{Reduce,Context,Relation}.jl` execute this file, and `test_mettail_presentation.jl` runs every
; rule below against `Eval.jl` on the same terms and requires agreement. A rule goes in when the
; differential can justify it, not when it reads plausibly — ChainSubst and FunctionStep were both
; probed against the interpreter BEFORE being written here, and `unify` was probed and REJECTED (see
; the closing section). Premised rules fire via `Relation.jl`, so ChainStep is no longer inert.
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
  ; ⚠️ INCOMPLETE, AND THE INCOMPLETENESS IS DELIBERATE. Every rule here is either QUOTED from the §3
  ; table or read off a VERB in it, and each is labelled as one or the other. Nothing is derived from
  ; §5's ALGORITHM — an abstract machine with metatype dispatch and a mutable evaluated-marker —
  ; because deriving inference rules from a machine is real work with real judgement in it, and
  ; guessing would put invented semantics into the one artifact whose purpose is to be the faithful
  ; source. Which instructions that leaves out, and why each is out, is the closing section.
  ;
  ; ⚠️ PATTERN VARIABLES WEAR MeTTa'S `$` SIGIL — `$X`, not `X`. The rules below were written WITHOUT
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
    (rewrite ChainStep ((~> $A $A2)) (~> (chain $A $v $T) (chain $A2 $v $T)))

    ; QUOTED, and the other half of the same table entry: "(chain <atom> <var> <template>) — interpret
    ; <atom>, SUBSTITUTE <var> IN <template> with the result". `Subst` is the ported AST's own node,
    ; so this is that sentence and nothing more.
    ;
    ; ⚠️ IT COMPETES WITH ChainStep, ON PURPOSE. Both apply to the same redex, so `reducts` returns
    ; two — R is a RELATION, and the leftmost-outermost strategy in `Context.jl`, not the rule set,
    ; picks one. Written after ChainStep so the strategy interprets before substituting, which is the
    ; order the table's sentence reads in. MEASURED: on the differential corpus BOTH orders reach the
    ; same normal form, so the ordering is a reading of the table here, not a correctness fix — and
    ; that observation is NOT a confluence claim, which nothing in this tree proves.
    (rewrite ChainSubst () (~> (chain $A $v $T) (Subst $T $A $v)))

    ; INFERRED from the verb, exactly as ChainStep is. Table: "(function <body>) — EVALUATE <body>
    ; until (return <atom>) is hit". A body that evaluates is a body that reduces, which is a
    ; congruence rule; FunctionReturn is what stops it.
    (rewrite FunctionStep ((~> $B $B2)) (~> (function $B) (function $B2)))))

; ─── WHAT IS STILL ABSENT FROM R, AND WHY — read this before adding to it ────────────────────────
; R is now four rules, each one either quoted from the §3 table or read off a verb in it, and each
; one AGREEING with `Eval.jl` on the differential corpus in `test_mettail_presentation.jl`. The
; remaining nine instructions are absent for reasons, not for lack of trying:
;
;   unify              Needs "these two terms unify" as a SIDE CONDITION, which R has no way to
;                      state. ⚠️ The tempting near-miss: `(unify $X $X $Then $Else) ~> $Then` DOES
;                      fire, because `match_pat` enforces consistency for a recurring variable — but
;                      it fires only on SYNTACTIC EQUALITY, so `(unify (a $b) ($a b) ($a $b) fail)`
;                      — the spec's own worked example — would not reduce. A rule that is right
;                      wherever it fires and silent everywhere else reads as coverage it does not
;                      have. Left out deliberately.
;   cons-atom          Builds an expression from a head and a tail of ARBITRARY length. R's terms are
;   decons-atom        fixed-arity, so neither direction is expressible without a list sort in Σ.
;   eval / evalc       Search the atomspace. The space is not in the term, so no term rewrite can
;   metta              express it — this is precisely where §5's abstract machine is not a rewrite
;   context-space      system, and where a presentation of MeTTa stops being able to say more.
;   collapse-bind      Need the machine's continuation ("resume where collapse-bind stopped").
;   superpose-bind
;   call-native        Calls out of the calculus entirely.
;
; So the ceiling here is not effort — it is that R describes a rewrite system and four of MeTTa's
; thirteen instructions are one. Anything further belongs to the coarse-grained presentation or to a
; machine model, not to this file.
