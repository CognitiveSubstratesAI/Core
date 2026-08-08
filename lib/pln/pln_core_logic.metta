;; ════════════════════════════════════════════════════════════════════════════
;; ECAN coupling — attention-blended priority (lib/ecan/ landed; un-stubbed 2026-06-16)
;; ════════════════════════════════════════════════════════════════════════════
;; PLN.Derive's priority ranking blends confidence with ECAN STI:
;;   priority = 0.5 * confidence + 0.5 * (STI / 100.0)
;; ECAN's real get-sti / boost-sti! (lib/ecan/core_logic.metta, imported by pln.metta)
;; now supply attention. get-sti defaults to 0.0 for atoms with no AV, so the blend
;; degrades to confidence-only ranking until attention is assigned — no stub needed.
;; The earlier `(= (get-sti _) 0.0)` / `(= (boost-sti! _ _) (empty))` stubs were REMOVED:
;; on Core they MULTI-RESULT-SHADOW ECAN's real rules (both fire) → PriorityRank returned
;; duplicates. This closes the ECAN→PLN half of the synergy loop (pln_ecan_coupling.metta
;; is the PLN-demand→STI half). Validated: test_pln_ecan.jl T6.
;; ────────────────────────────────────────────────────────────────────────────
(= (trace! $atom $level) $atom)
;; atom-to-str is used as a UUID derivation in PLN; identity is a safe stub
;; (collisions only matter for ECAN's attention bookkeeping which is also stubbed).
(= (atom-to-str $atom) $atom)
;; ════════════════════════════════════════════════════════════════════════════

;; clamp lives in Core stdlib/math.metta (always loaded) — PLN's second local copy
;; removed 2026-06-10 (it was also in stv.metta).

;;Concat tuples — reuse the common grounded union-atom (concat, no dedup) instead of the undefined
;; upstream `append` (only existed in the dead top-level stdlib/). hyperon/CeTTa-faithful: reuse, don't re-roll.
(= (TupleConcat $Ev1 $Ev2)
   (union-atom $Ev1 $Ev2))
;   (collapse (superpose ((superpose $Ev1) (superpose $Ev2)))))

;;Count size of tuple
(= (TupleCount $tuple)
   (length $tuple))
;   (if (== $tuple ()) 0 (+ 1 (TupleCount (cdr-atom $tuple)))))

;Shortcut for and with 5 args
(= (and5 $0 $1 $2 $3 $4)
   (and $0 (and $1 (and $2 (and $3 $4)))))

;Shortcut for min with 5 args
(= (min5 $0 $1 $2 $3 $4)
   (min $0 (min $1 (min $2 (min $3 $4)))))

;Exclude division by 0
(= (/safe $A $B)
   (if (> $B 0.0)
       (/ $A $B)
       (empty)))

;Negate (1 minus)
(= (negate $arg)
   (- 1.0 $arg))

;Invert (1 over)
(= (invert $arg)
   (/safe 1.0 $arg))

;; Truth_or — probabilistic OR / Łukasiewicz t-conorm under independence:
;;   P(A ∨ B) = 1 - (1 - P(A))(1 - P(B))
;;
;; Added 2026-04-08 to fix audit Bug 1 (docs/research/algorithm_audits/pln_2026-04-08.md).
;; Previously, PLN's Truth_SymmetricModusPonens (line 178) and Truth_transitiveSimilarity
;; (line 225) referenced Truth_or but it was only defined in lib/legacy/nars_legacy.metta
;; (the rejected NARS legacy file, NOT in the active load chain). This caused both
;; functions to leak unevaluated MeTTaTerms instead of computing their confidence values.
;;
;; Note: this is the *probabilistic* t-conorm, not Q_PLN's max (Gödel t-conorm).
;; See audit "Mismatch A" for the architectural decision that needs to be made about
;; which t-conorm becomes canonical. For now, preserve the historical PLN semantics.
;;
;; Examples:
;;   (Truth_or 0.6 0.4) → 0.76
;;   (Truth_or 0.0 0.5) → 0.5
;;   (Truth_or 1.0 0.5) → 1.0
(= (Truth_or $a $b)
   (- 1.0 (* (- 1.0 $a) (- 1.0 $b))))

;;Test case
(= (Test2 $Is $Should)
   ((Is: $Is) (Should: $Should) (Passed: (== $Is $Should))))

;; InsertionSort helper: insert element x into sorted list L
(= (InsertSorted $x $L)
   (if (== $L ())
       ($x)
       (let* (($head (car-atom $L))
              ($tail (cdr-atom $L)))
             (if (< $x $head)
                 (TupleConcat ($x $head) $tail)
                 (TupleConcat ($head) (InsertSorted $x $tail))))))

;; InsertionSort main — canonicalises an evidence stamp to a total order so that
;; StampDisjoint's overlap test is order-independent.
;;
;; ⚠️ WAS `(msort $L)` — and `msort` IS NOT DEFINED ANYWHERE (one grep hit repo-wide: this
;; call site). It silently returned the UNREDUCED term `(msort (s1 s2))` instead of a sorted
;; tuple, so EVERY derived sentence's stamp (built here at :502 / :553) was malformed. Verified
;; by execution — the gate then broke in BOTH directions:
;;   · derived-vs-derived: (StampDisjoint (msort (s1 s2)) (msort (s3 s4))) => False on fully
;;     DISJOINT evidence — both stamps contain the symbol `msort`, so every pair "overlaps".
;;     Legitimate revisions are blocked  ⇒ INFERENCE STARVATION.
;;   · seed-vs-derived: (StampDisjoint (s1) (msort (s1 s2))) => True although s1 is in BOTH —
;;     `s1` is nested inside the unreduced term, so superpose never sees it. The gate fails OPEN
;;     and licenses re-counting the same evidence ⇒ EVIDENCE FABRICATION (ωPLN Prop 7.1: D_dc>0).
;; `sort-atom` is grounded (src/standard/Eval.jl:2229) and verified on stamp-shaped data:
;; (s3 s1 s2)->(s1 s2 s3), ()->(), (s1)->(s1), (s2 s1 s2)->(s1 s2 s2). Any total order suffices;
;; sorting is for canonicalisation, not dedup. Found by auditing our PLN against Goertzel's ωPLN
;; law catalogue (docs/specs/omegaclaw/omegapln_implementation_v3_spec.md §26.2/App C).
;; The original recursive impl (via the still-live InsertSorted, :81-89) is kept below for
;; reference; it compares with `<` and so is numeric-only, whereas stamps are symbols.
(= (InsertionSort $L $Ret)
   (sort-atom $L))
;   (if (== $L ())
;       $Ret
;       (let* (($x (car-atom $L))
;              ($rest (cdr-atom $L))
;              ($newRet (InsertSorted $x $Ret)))
;             (InsertionSort $rest $newRet))))

;;Exclude item from tuple
(= (Without $Tuple $a)
   (subtraction-atom $Tuple ($a)))   ; reuse grounded subtraction-atom (was undefined `exclude-item`)
;   (collapse (let $x (superpose $Tuple)
;                  (if (== $x $a)
;                      (empty)
;                      $x))))

;;Whether a is an element of the tuple
(= (ElementOf $a $Tuple)
   (is-member $a $Tuple))
;   (not (== (collapse (let $x (superpose $Tuple)
;                           (if (== $x $a)
;                               True
;                               (empty)))) ())))

;;Fast but TODO use efficient native handling once available: https://github.com/trueagi-io/metta-morph/pull/27
(= (Unique $L $Ret)
   (unique-atom $L))   ; reuse grounded unique-atom (dedup, keeps first) — was undefined `list_to_set`
;   (if (== $L ())
;       $Ret
;       (let* (($x (car-atom $L))
;              ($rest (cdr-atom $L)))
;             (if (ElementOf $x $Ret)
;                 (Unique $rest $Ret)
;                 (Unique $rest (TupleConcat ($x) $Ret))))))

;; Consistency Conditions: PLN book "5.2.2.2 PLN Deduction and Second-Order Probability", page 74:

; borrowed from https://github.com/trueagi-io/hyperon-pln/blob/main/metta/pln/dependent-types/DeductionDTL.metta
(: smallest-intersection-probability (-> Number Number Number))
(= (smallest-intersection-probability $As $Bs)
   (clamp (/ (- (+ $As $Bs) 1) $As) 0 1))

(: largest-intersection-probability (-> Number Number Number))
(= (largest-intersection-probability $As $Bs)
   (clamp (/ $Bs $As) 0 1))

(: conditional-probability-consistency (-> Number Number Number Bool))
;; Bug 4 fix (2026-04-08): use let* to extract helper return values BEFORE
;; passing them to <=. The interpreter's <= comparison does not auto-unwrap
;; Channel-valued arguments — when smallest-intersection-probability and
;; largest-intersection-probability return Channels (because they're rule-
;; based with multiple firings), inline (<= (fn ...) value) compares the
;; Channel object itself against value and returns false. let* forces value
;; extraction via the binding mechanism. Verified:
;;   (<= (smallest-intersection-probability 0.8 0.7) 0.7) → false (BROKEN)
;;   (let* (($s (smallest-intersection-probability 0.8 0.7))) (<= $s 0.7)) → true ✓
;; This is the same pattern that the let* fix in SpecialForms.jl now supports
;; reliably. See docs/research/algorithm_audits/pln_2026-04-08.md for full
;; root cause analysis. Fixing this one helper unblocks Truth_Deduction,
;; Truth_evaluationImplication (via simpleDeductionStrength), and
;; Truth_transitiveSimilarity.
;;
;; Examples:
;;   (conditional-probability-consistency 0.8 0.7 0.7) → true
;;   (conditional-probability-consistency 0.8 0.7 0.95) → false
(= (conditional-probability-consistency $As $Bs $ABs)
   (let* (($smallest (smallest-intersection-probability $As $Bs))
          ($largest  (largest-intersection-probability $As $Bs)))
         (and (< 0 $As)
              (and (<= $smallest $ABs)
                   (<= $ABs $largest)))))

;; valid-strength — L-C4 domain guard. A PLN strength is the mean of a first-order
;; probability and MUST lie in [0,1]; s>1 (or s<0) is out-of-domain, never legitimate
;; (canonical itself treats >1 as something to bound — see Truth_Revision's (min 1.0 $f)).
;; Pure-MeTTa predicate composing primitives — no grounded op, no Error atom — same
;; Bool + (if … fallback) shape as conditional-probability-consistency above. Used at the
;; ORIGIN of Induction/Abduction/equivalenceToImplication/TransitiveSimilarityStrength to
;; REJECT an out-of-domain inference (from probabilistically-inconsistent input TVs) rather
;; than let it flow downstream where Truth_Revision's (min 1.0 $f) would silently launder it
;; into a confident belief. The four bodies are byte-identical to canonical trueagi-io/PLN +
;; PeTTa — only their domain PRECONDITION was missing (deduction has it, these four lacked it).
(: valid-strength (-> Number Bool))
(= (valid-strength $s)
   (and (<= 0.0 $s) (<= $s 1.0)))

(= (Consistency_ImplicationImplicantConjunction $As $Bs $Cs $ACs $BCs)
   ; Conditional probability consistency checks:
   ; P(C|A) <= P(C)/P(A)  =>  $sAC <= $sC / $sA
   ; P(C|B) <= P(C)/P(B)  =>  $sBC <= $sC / $sB
   ; Also ensure denominators are not zero for the checks.
   (and5 (> $As 0) (> $Bs 0) (> $Cs 0) ; Avoid division by zero and ensure meaningful probabilities
         (<= $ACs (/ $Cs $As))
         (<= $BCs (/ $Cs $Bs))))

;; Truth functions

;Forward declaration
(= (STV $stv) (empty))

(: Truth_c2w (-> Number Number))
(= (Truth_c2w $c)
   (/safe $c (- 1 $c)))

(: Truth_w2c (-> Number Number))
;; ⚠️ `(* 1.0 $w)` is LOAD-BEARING, not noise. MeTTa `/` on two Integers is INTEGER division
;; (hyperon arithmetics.rs:154-155 `Number::Integer(a / b)`; LeaTTa proves `Ground.int (a / b)`;
;; measured on upstream's own binary: `!(/ 7 2)` -> [3]). Core promoted Int/Int to Float until
;; 2026-08-06, and this formula silently relied on that: with a bare `(/safe $w (+ $w 1))` and an
;; integer count, Truth_w2c can only ever return 0 or 1. A confidence is a REAL in [0,1), so the
;; float is part of the formula, not a workaround. Do not "simplify" it away.
(= (Truth_w2c $w)
   (/safe (* 1.0 $w) (+ $w 1)))

; Deduction formula: PLN book "1.4 Truth-value Formulas", page 15:
; borrowed from https://github.com/trueagi-io/hyperon-pln/blob/main/metta/pln/dependent-types/DeductionDTL.metta
;; Truth_Deduction — PLN book "1.4 Truth-value Formulas", page 15
;; Strength: PQs*QRs + (1-PQs)*(Rs - Qs*QRs)/(1-Qs)
;; Confidence: PQs*QRs*PQc*QRc
;; Returns (stv 1 0) fallback when consistency preconditions fail.
;;
;; Examples:
;;   (Truth_Deduction (stv 0.8 0.9) (stv 0.7 0.85) (stv 0.6 0.8) (stv 0.7 0.9) (stv 0.6 0.85)) → (stv 0.6 0.3213)
(= (Truth_Deduction (stv $Ps $Pc)
                    (stv $Qs $Qc)
                    (stv $Rs $Rc)
                    (stv $PQs $PQc)
                    (stv $QRs $QRc))
   ;; Canonical form (matches PeTTa lib_pln.metta — no let* wrapper).
   ;; The original let* was added 2026-04-08 to work around a Channel-leak
   ;; in `and`. Today's interpreter handles this correctly without let*,
   ;; AND the let* version was load-order-fragile (broke when goal_tracking
   ;; loaded BEFORE PLN). Keeping PRIMUS confidence formula
   ;; (* (* PQs QRs) (* PQc QRc)) — PeTTa uses (min Pc (min Qc (min Rc...))).
   (if (and (conditional-probability-consistency $Ps $Qs $PQs)
            (conditional-probability-consistency $Qs $Rs $QRs))
       ;; Preconditions are met
       (stv (if (< 0.9999 $Qs)                  ; avoid division by 0
                ;; Qs tends to 1
                $Rs
                ;; Otherwise
                (+ (* $PQs $QRs) (/safe (* (- 1 $PQs) (- $Rs (* $Qs $QRs))) (- 1 $Qs))))
            (* (* $PQs $QRs) (* $PQc $QRc)))
       ;; Preconditions are not met
       (stv 1 0)))

; Induction formula: PLN book "Appendix A: Comparison of PLN Rules with NARS Rules", page 307
(= (Truth_Induction (stv $sA $cA)
                    (stv $sB $cB)
                    (stv $sC $cC)
                    (stv $sBA $cBA)
                    (stv $sBC $cBC))
   (let* (($s (+ (/safe (* (* $sBA $sBC) $sB) $sA)
                 (* (- 1 (/safe (* $sBA $sB) $sA))
                    (/safe (- $sC (* $sB $sBC)) (- 1 $sB))))))
         (if (valid-strength $s)
             (stv $s (Truth_w2c (* (* $sBC $cBC) $cBA)))
             ;; L-C4: out-of-domain strength (inconsistent input TVs) — reject at origin
             (stv 1 0))))

; Abduction formula: PLN book "Appendix A: Comparison of PLN Rules with NARS Rules", page 307
(= (Truth_Abduction (stv $sA $cA)
                    (stv $sB $cB)
                    (stv $sC $cC)
                    (stv $sAB $cAB)
                    (stv $sCB $cCB))
   (let* (($s (+ (/safe (* (* $sAB $sCB) $sC)
                        $sB)
                 (/safe (* $sC (* (- 1 $sAB) (- 1 $sCB)))
                        (- 1 $sB)))))
         (if (valid-strength $s)
             (stv $s (Truth_w2c (* (* $sAB $cAB) $cCB)))
             ;; L-C4: out-of-domain strength (term1 diverges as sB→0) — reject at origin
             (stv 1 0))))

;Modus Ponens: PLN book "5.7.1 Modus Ponens", page 111:
;; Strength: Ps*PQs + 0.02*(1-Ps)
;; Confidence: Truth_w2c(Pc*PQc)
;;
;; Examples:
;;   (Truth_ModusPonens (stv 0.8 0.9) (stv 0.7 0.85)) → (stv 0.564 0.4334)
;;
;; Bug 2 (still open as of 2026-04-08): the confidence path leaks Channel{Any}.
;; The strength is correct (0.564) but Truth_w2c(Pc*PQc) returns a Channel.
;; This doctest will FAIL until Bug 2 is fixed; that's intentional — it's the
;; canary that surfaces the bug to any future maintainer.
(= (Truth_ModusPonens (stv $Ps $Pc) (stv $PQs $PQc))
   (stv (+ (* $Ps $PQs) (* 0.02 (- 1 $Ps)))
        (Truth_w2c (* $Pc $PQc))))

; SymmetricModusPonens rule   see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/symmetric-modus-ponens.scm
;; Strength: sA*sAB + (snotAB*(1-sA))*(1+sAB)  where snotAB=0.2
;; Confidence: cA*cAB*Truth_or(sA, sAB)
;;
;; Examples:
;;   (Truth_SymmetricModusPonens (stv 0.8 0.9) (stv 0.7 0.85)) → (stv 0.628 0.7191)
(= (Truth_SymmetricModusPonens (stv $sA $cA) (stv $sAB $cAB))
   (let* (($snotAB 0.2)
          ($cnotAB 1.0))
         (stv (+ (* $sA $sAB) (* (* $snotAB (negate $sA)) (+ 1.0 $sAB)))
              (* (* $cA $cAB) (Truth_or $sA $sAB)))))

;Revision: PLN Book "5.10.2 A Heuristic Revision Rule for Simple Truth-values", page 116:
;; w1=Truth_c2w(c1), w2=Truth_c2w(c2), w=w1+w2
;; f = (w1*f1 + w2*f2) / w
;; c = max(Truth_w2c(w), c1, c2)
;;
;; Examples:
;;   (Truth_Revision (stv 0.6 0.5) (stv 0.8 0.7)) → (stv 0.74 0.7692)
(= (Truth_Revision (stv $f1 $c1) (stv $f2 $c2))
   (let* (($w1 (Truth_c2w $c1))
          ($w2 (Truth_c2w $c2))
          ($w (+ $w1 $w2))
          ($f (/safe (+ (* $w1 $f1) (* $w2 $f2)) $w))
          ($c (Truth_w2c $w)))
         (stv (min 1.0 $f)
              (min 1.0 (max (max $c $c1) $c2)))))

; negation, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/negation-introduction.scm#L41
; negation elimination, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/not-elimination.scm#L34
(= (Truth_Negation (stv $s $c))
   (stv (- 1.0 $s) $c))

;; Truth_inversion — confidence-attenuated swap
;; Strength: ABs (unchanged)
;; Confidence: Bc * ABc * 0.6
;;
;; Examples:
;;   (Truth_inversion (stv 0.7 0.8) (stv 0.6 0.9)) → (stv 0.6 0.432)
(= (Truth_inversion (stv $Bs $Bc) (stv $ABs $ABc))
   ; confidence depends on Truth of (target) B node, which is not according to OpenCOG classic.
   ; confidence penality not according to OpenCOG classic PLN. Is weaker in this implementation.
   (stv $ABs (* $Bc (* $ABc 0.6))))

; see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/equivalence-to-implication.scm
(= (Truth_equivalenceToImplication (stv $As $Ac) (stv $Bs $Bc) (stv $ABs $ABc))
    (let* (($ConclS (if (< 0.99 (* $ABs $ABc)) ; Hack to work around the lack of distributional
                                               ; TV. If ABs is high enough, we just set $ConclS as $ABs
                        $ABs
                        ;; Formula based on PLN book formula for sim2inh
                        (/safe (* (+ 1.0 (/safe $Bs $As)) $ABs) (+ 1.0 $ABs)))))
          (if (valid-strength $ConclS)
              (stv $ConclS $ABc)
              ;; L-C4: sim2inh factor (1+Bs/As) explodes for small As — reject at origin
              (stv 1 0))))

; see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/formulas.scm#L160-L173
(= (TransitiveSimilarityStrength $sA $sB $sC $sAB $sBC)
   (let* (($T1 (/safe (* (+ 1.0 (/safe $sB $sA)) $sAB) (+ 1.0 $sAB)))
          ($T2 (/safe (* (+ 1.0 (/safe $sC $sB)) $sBC) (+ 1.0 $sBC)))
          ($T3 (/safe (* (+ 1.0 (/safe $sB $sC)) $sBC) (+ 1.0 $sBC)))
          ($T4 (/safe (* (+ 1.0 (/safe $sA $sB)) $sAB) (+ 1.0 $sAB)))
          ($s (invert (- (+ (invert (+ (* $T1 $T2) (* (negate $T1) (/safe (- $sC (* $sB $T2)) (negate $sB)))))
                            (invert (+ (* $T3 $T4) (* (negate $T3) (/safe (- $sC (* $sB $T4)) (negate $sB)))))) 1.0))))
         ;; L-C4: sim2inh terms T1..T4 are unbounded when node strengths differ; the bare `/` here
         ;; also risked Inf/NaN on a zero node-strength — harden to /safe and REJECT the out-of-domain
         ;; result at origin. (empty) prunes, mirroring simpleDeductionStrength's guard on the same path.
         (if (valid-strength $s) $s (empty))))

; see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/transitive-similarity.scm
;; Truth_transitiveSimilarity — see opencog/pln/rules/wip/transitive-similarity.scm
;; Strength: TransitiveSimilarityStrength(As, Bs, Cs, ABs, BCs)
;; Confidence: ABc*BCc*Truth_or(ABs, BCs)
;;
;; Examples:
;;   (Truth_transitiveSimilarity (stv 0.6 0.7) (stv 0.5 0.8) (stv 0.7 0.9) (stv 0.8 0.85) (stv 0.6 0.8)) → (stv 0.6694 0.6256)
(= (Truth_transitiveSimilarity (stv $As $Ac)
                               (stv $Bs $Bc)
                               (stv $Cs $Cc)
                               (stv $ABs $ABc)
                               (stv $BCs $BCc))
   ;; Inlined — let* removed for load-order robustness (same fix as Truth_Deduction).
   (stv (TransitiveSimilarityStrength $As $Bs $Cs $ABs $BCs)
        (* (* $ABc $BCc) (Truth_or $ABs $BCs))))

; see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/formulas.scm
(= (simpleDeductionStrength $sA $sB $sC $sAB $sBC)
   ;; Bug 4 cascade fix (2026-04-08): same let* extraction pattern as
   ;; Truth_Deduction. See conditional-probability-consistency comment.
   (let* (($cons1 (conditional-probability-consistency $sA $sB $sAB))
          ($cons2 (conditional-probability-consistency $sB $sC $sBC)))
     (if (and $cons1 $cons2)
         ;; Preconditions are met
         (if (< 0.99 $sB)
             ;; sB tends to 1
             $sC
             ;; otherwise
             (+ (* $sAB $sBC) (/safe (* (- 1.0 $sAB) (- $sC (* $sB $sBC))) (- 1.0 $sB))))
         ;; Preconditions are not met
         (empty))))

; see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/evaluation-implication.scm
;; Truth_evaluationImplication — see opencog/pln/rules/wip/evaluation-implication.scm
;; Strength: simpleDeductionStrength(Bs, As, Cs, ABs, ACs)
;; Confidence: ABs*ACs*ABc*ACc
;;
;; Examples:
;;   (Truth_evaluationImplication (stv 0.6 0.7) (stv 0.5 0.8) (stv 0.7 0.9) (stv 0.8 0.85) (stv 0.6 0.8)) → (stv 0.65 0.3264)
(= (Truth_evaluationImplication (stv $As $Ac)
                                (stv $Bs $Bc)
                                (stv $Cs $Cc)
                                (stv $ABs $ABc)
                                (stv $ACs $ACc))
   ;; Inlined — let* removed for load-order robustness (same fix as Truth_Deduction).
   (stv (simpleDeductionStrength $Bs $As $Cs $ABs $ACs)
        (* (* $ABs $ACs) (* $ABc $ACc))))

;; INFERENCE RULES


; guard to only allow inference for certain link types
(= (SymmetricModusPonensRuleGuard Similarity) True)
(= (SymmetricModusPonensRuleGuard IntentionalSimilarity) True)
(= (SymmetricModusPonensRuleGuard ExtensionalSimilarity) True)

; guard to only allow inference for certain link types
(= (SyllogisticRuleGuard Inheritance) True)
(= (SyllogisticRuleGuard Implication) True)

;Revision
(= (|- ($T $T1) 
       ($T $T2))
   ($T (Truth_Revision $T1 $T2)))

;Modus Ponens
(= (|- ($A $T1) 
       ((Implication $A $B) $T2))
   ($B (Truth_ModusPonens $T1 $T2)))

; SymmetricModusPonens rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/symmetric-modus-ponens.scm
(= (|- ($A $TruthA)
       (($LinkType $A $B) $TruthAB))
   (if (SymmetricModusPonensRuleGuard $LinkType)
       ($B (Truth_SymmetricModusPonens $TruthA $TruthAB)) (empty)))

; Deduction rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/term/deduction.scm
(= (|- (($LinkType $A $B) $T1)
       (($LinkType $B $C) $T2))
   (if (SyllogisticRuleGuard $LinkType)
       (($LinkType $A $C)
        (Truth_Deduction (STV $A)
                         (STV $B)
                         (STV $C) $T1 $T2)) (empty)))

; Induction rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/induction.scm
(= (|- (($LinkType $C $A) $T1)
       (($LinkType $C $B) $T2))
   (if (SyllogisticRuleGuard $LinkType)
       (($LinkType $A $B) (Truth_Induction (STV $A)
                                           (STV $B)
                                           (STV $C) $T1 $T2)) (empty)))

; Abduction rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/abduction.scm
(= (|- (($LinkType $A $C) $T1)
       (($LinkType $B $C) $T2))
   (if (SyllogisticRuleGuard $LinkType)
       (($LinkType $A $B) (Truth_Abduction (STV $A)
                                           (STV $B)
                                           (STV $C) $T1 $T2)) (empty)))

;Usage of inheritance for predicates
;unary arg
(= (|- ((Evaluation (Predicate $x)
                    (List (Concept $C))) $T1)
       ((Inheritance (Concept $S) (Concept $C)) $T2))
   ((Evaluation (Predicate $x)
                (List (Concept $S))) (Truth_ModusPonens $T1 $T2)))

;binary arg1
(= (|- ((Evaluation (Predicate $x)
                    (List (Concept $C1) (Concept $C2))) $T1)
       ((Inheritance (Concept $S) (Concept $C1)) $T2))
   ((Evaluation (Predicate $x)
                (List (Concept $S) (Concept $C2))) (Truth_ModusPonens $T1 $T2)))

;binary arg2
(= (|- ((Evaluation (Predicate $x)
                    (List (Concept $C1) (Concept $C2))) $T1)
       ((Inheritance (Concept $S) (Concept $C2)) $T2))
   ((Evaluation (Predicate $x)
                (List (Concept $C1) (Concept $S))) (Truth_ModusPonens $T1 $T2)))

; negation elimination rule (introduction now handled by Translator), see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/not-elimination.scm#L1-L8
(= (|- ((Not $A) $T)) ($A (Truth_Negation $T)))

; Inheritance Inversion Rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/inversion.scm
(= (|- ((Inheritance $A $B) $Truth))
   ((Inheritance $B $A) (Truth_inversion (STV $B) $Truth)))

; Implication Inversion Rule (same)
(= (|- ((Implication $A $B) $Truth))
   ((Implication $B $A) (Truth_inversion (STV $B) $Truth)))

; Equivalence to Implication Rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/equivalence-to-implication.scm
(= (|- ((Equivalence $A $B) $Truth))
   ((Implication $A $B) (Truth_equivalenceToImplication (STV $A)
                                                        (STV $B) $Truth)))

(= (|- ((Equivalence $A $B) $Truth))
   ((Implication $B $A) (Truth_equivalenceToImplication (STV $A)
                                                        (STV $B) $Truth)))

; transitive similarity Rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/transitive-similarity.scm
(= (|- ((Similarity $A $B) $T1)
       ((Similarity $B $C) $T2))
   ((Similarity $A $C) (Truth_transitiveSimilarity (STV $A)
                                                   (STV $B)
                                                   (STV $C) $T1 $T2)))

; Evaluation Implication Rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/wip/evaluation-implication.scm
(= (|- ((Evaluation $A $B) $TruthAB)
       ((Implication $A $C) $TruthAC))
   ((Evaluation $C $B) (Truth_evaluationImplication (STV $A)
                                                    (STV $B)
                                                    (STV $C) $TruthAB $TruthAC)))

; extensional - Member deduction rule, see https://github.com/opencog/pln/blob/master/opencog/pln/rules/extensional/member-deduction.scm
; we are using the truth of deduction here
(= (|- ((Member $A $B) $T1)
       ((Inheritance $B $C) $T2))
   ((Member $A $C) (Truth_Deduction (STV $A)
                                    (STV $B)
                                    (STV $C) $T1 $T2)))

;;How many derivation steps (task selections)
(= (PLN.Config.MaxSteps) 100)

;;Size of active tasks PQ
(= (PLN.Config.TaskQueueSize) 10)

;;Max beliefs buffer size
(= (PLN.Config.BeliefQueueSize) 100)

;;Whether evidence was just counted once
(= (StampDisjoint $Ev1 $Ev2)
   (== () (collapse (let* (($x (superpose $Ev1))
                           ($y (superpose $Ev2)))
                          (case (== $x $y) ((True True)))))))

;;Concat stamp with sorting
(= (StampConcat $stamp $addition)
   (if (== $addition ())
       $stamp
       (InsertionSort (TupleConcat $stamp $addition) ())))

;;retrieve the best candidate (PQ functionality)
(= (BestCandidate $evaluateCandidateFunction $bestCandidate $tuple)
   (if (== $tuple ())
       $bestCandidate
       (let* (($head (car-atom $tuple))
              ($tail (cdr-atom $tuple)))
             (if (> ($evaluateCandidateFunction $head)
                    ($evaluateCandidateFunction $bestCandidate))
                 (BestCandidate $evaluateCandidateFunction $head $tail)
                 (BestCandidate $evaluateCandidateFunction $bestCandidate $tail)))))

;;candidate evaluation based on priority (ECAN-blended)
;; MJ ECAN: PLN candidate ranking now blends confidence with ECAN STI score.
;; Priority = 0.5 * confidence + 0.5 * (STI / 100.0)
;; Atoms with high ECAN attention AND high PLN confidence are processed first.
(= (PriorityRank (Sentence ($x (stv $f $c)) $Ev1))
   (let $sti (get-sti (get-uuid $x))
        (+ (* 0.5 $c) (* 0.5 (/ $sti 100.0)))))
(= (PriorityRank ()) -99999.0)

;;candidate elimination based on negated priority (ECAN-blended)
(= (PriorityRankNeg (Sentence ($x (stv $f $c)) $Ev1))
   (let $sti (get-sti (get-uuid $x))
        (- 0.0 (+ (* 0.5 $c) (* 0.5 (/ $sti 100.0))))))
(= (PriorityRankNeg ()) -99999.0)

(= (get-uuid $x) (atom-to-str $x))

;; pln-freshness-check: default to True if no specific freshness logic is triggered
(= (pln-freshness-check $uuid) True)

;;Return limited-sized version of $L (bounded PQ functionality)
(= (LimitSize $L $size)
   (if (< (TupleCount $L) $size)
       $L
       (let $lowestPriorityItem (BestCandidate PriorityRankNeg () $L)
            (LimitSize (Without $L $lowestPriorityItem) $size))))

;;Priority-queue based task ranking deriver with belief buffer
;; MJ-3 Freshness Gate: beliefs are checked via pln-freshness-check before inference.
;; Stale beliefs (evidence older than max_age) are silently filtered out.
(= (PLN.Derive $Tasks $Beliefs $steps $maxsteps $taskqueuesize $beliefqueuesize)
   (if (or (> $steps $maxsteps) (== $Tasks ()))
       ($Tasks $Beliefs)
       (let (Sentence $x $Ev1) (BestCandidate PriorityRank () $Tasks)
            (let $derivations
                 (collapse (superpose ((let* (((Sentence $y $Ev2) (superpose $Beliefs))
                                              ;; MJ-3: Freshness gate — skip stale beliefs
                                              ($fresh (pln-freshness-check (get-uuid $y)))
                                              ($stamp (InsertionSort (TupleConcat $Ev1 $Ev2) ())))
                                             (if (and $fresh (StampDisjoint $Ev1 $Ev2))
                                                 (case (superpose ((|- $x $y)
                                                                   (|- $y $x)))
                                                       ((($T $TV) (Sentence ($T $TV) $stamp))))
                                                 (empty)))
                                       (case (|- $x) ((($T3 $TV3) (Sentence ($T3 $TV3) $Ev1)))))))
                 (let* (($temp (trace! (SELECTED $steps (Sentence $x $Ev1)) 42))
                        ($stim (if (== $derivations ()) (empty) (boost-sti! (get-uuid $x) 50.0))))
                            (PLN.Derive (LimitSize (Without (Unique (TupleConcat $Tasks $derivations) ()) (Sentence $x $Ev1)) $taskqueuesize)
                                        (LimitSize (Unique (TupleConcat $Beliefs $derivations) ()) $beliefqueuesize)
                                        (+ $steps 1)
                                        $maxsteps
                                        $taskqueuesize
                                        $beliefqueuesize))))))


(= (PLN.Derive $Tasks $Beliefs $maxsteps $taskqueuesize $beliefqueuesize)
   (PLN.Derive $Tasks $Beliefs 1 $maxsteps $taskqueuesize $beliefqueuesize))

(= (PLN.Derive $Tasks $Beliefs $maxsteps)
   (PLN.Derive $Tasks $Beliefs $maxsteps (PLN.Config.TaskQueueSize) (PLN.Config.BeliefQueueSize)))

(= (PLN.Derive $Tasks $Beliefs)
   (PLN.Derive $Tasks $Beliefs (PLN.Config.MaxSteps)))

;;Candidate evaluation based on confidence
(= (ConfidenceRank ((stv $f $c) $Ev)) $c)
(= (ConfidenceRank ()) 0)

;;Pose a question of a certain term to the system on some knowledge base
(= (PLN.Query $Tasks $Beliefs $term $maxsteps $taskqueuesize $beliefqueuesize)
   (BestCandidate ConfidenceRank () (collapse (let ($TasksRet $BeliefsRet) (PLN.Derive $Tasks $Beliefs $maxsteps $taskqueuesize $beliefqueuesize)
                                                   (case (superpose $BeliefsRet)
                                                         (((Sentence ($Term $TV) $Ev) (case (== $Term $term)
                                                                                            ((True ($TV $Ev)))))))))))

(= (PLN.Query $kb $term $maxsteps $taskqueuesize $beliefqueuesize)
   (PLN.Query $kb $kb $term $maxsteps $taskqueuesize $beliefqueuesize))

(= (PLN.Query $kb $term $maxsteps)
   (PLN.Query $kb $term $maxsteps (PLN.Config.TaskQueueSize) (PLN.Config.BeliefQueueSize))) ;default space bound

(= (PLN.Query $kb $term)
   (PLN.Query $kb $term (PLN.Config.MaxSteps))) ;default steps bound

(= (PLN.Query $term $maxsteps)
   (PLN.Query &self $term $maxsteps))

(= (PLN.Query $term)
   (PLN.Query &self $term (PLN.Config.MaxSteps)))

