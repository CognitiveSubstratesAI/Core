; pattern_miner_metta_il.metta — §9.1 of Notes on the Path to Scalable MeTTa Infrastructure
; (Ben Goertzel, 2025-06-30). Extracted verbatim via docs/specs/Mork/scalable_metta_infrastructure_spec.md §9.1.
;
; ─── THE TOP OF THE TRIPLE ───────────────────────────────────────────────────────────────────────
; The SAME 7 stages as the two .mm2 siblings, in MeTTa-IL — the surface Fig-2's one compile arrow
; actually targets. Read the three together: this is the source, §9.2 is the MM2+ lowering, §9.3 is
; what pure MM2 can express without guards. The triple is the differential; no single file is.
;
; Surface used here: `def` / `match` / `when` / `emit` / `let`. Note `when` carries the thresholds
; (`(>= N Minsup)`, `(>= I HighSurp)`) that pure MM2 §9.3 must fake with exact-value matching and that
; MM2+ §9.2 expresses as `:guard`. Same predicate, three encodings — that is the thing to test.
;
; ⚠️ THIS IS THE PAPER'S MeTTa-IL, NOT NECESSARILY OURS. The author self-caveats §9.1.1: "Possibly
; some details ... may be incorrect due to my imperfect understanding of MeTTa-IL." Treat divergence
; from our EmitIL surface as a question to settle against `Core/src/compiler/EmitIL.jl`, NOT as our
; error — and NOT as licence to widen our IL toward this file. See §9.1.1's own list of MeTTa-IL
; limitations (reduced macro power, fixed host-primitive set, S-expression-only data model).
;
; ⚠️ `.metta` extension, but this is NOT loadable by the conformance runner and must not be added to
; test/standard/conformance/ — that corpus is hyperon-experimental's and is asserted against. This is
; a vendored REFERENCE for the compiler differential.
;
; allow-new-artifact: vendored upstream corpus; source spec read this session (§9.1)

(def extract-skeleton ()
  (match (eval (pred P) (list A1 A2))
    (emit (skeleton (eval (pred P) (list (var "X") A2))))
    (emit (skeleton (eval (pred P) (list A1 (var "X")))))))

(def specialize ()
  (match (skeleton Template)
         (eval (pred P) (list A1 A2))
    (when (unify Template (eval (pred P) (list A1 A2)) Sub)
      (emit (candidate (instantiate Template Sub))))))

(def increment-count ()
  (match (candidate C Pattern) (count C Pattern N)
    (emit (count C Pattern (+ N 1)))))

(def mark-kept (Minsup)
  (match (count C Pattern N)
    (when (>= N Minsup)
      (emit (kept C Pattern)))))

(def combine-patterns ()
  (match (kept C1 P1) (kept C2 P2)
    (emit (conj C1 C2 (and P1 P2)))))

(def compute-surprise (Universe)
  (match (conj C1 C2 And) (count C1 P1 N1) (count C2 P2 N2)
         (universe Universe)
    (let Obs (/ N1 Universe)
         Exp (* (/ N1 Universe) (/ N2 Universe))
         I   (/ (abs (- Obs Exp)) Obs)
      (emit (score And I)))))

(def select-output (HighSurp)
  (match (score Pattern I)
    (when (>= I HighSurp)
      (emit (output Pattern I)))))
