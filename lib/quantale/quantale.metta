; quantale.metta — Foundational quantale construction (Core / Minimal-native)
;
; Source papers (specs, read-once):
;   docs/specs/Quantale/quantale_spec.md  — "Weakness is All You Need" Ch 2/4/5/6
;   docs/specs/Mork/MORK_MOSES_spec.md §9  — "Quantales in the MOSES Framework"
;
; Substrate-native port of the PRIMUS_Core draft (lib/quantale/quantale.metta),
; corrected per quantale_spec:
;   * scalar [0,1] probability quantale RENAMED q-prob-* (the draft mislabelled it
;     q-pln-*; §3 is explicit the scalar is Q_prob, NOT Q_PLN);
;   * the REAL Q_PLN is the PAIRED (n+, n-) evidence quantale of §4.4.1 — added here
;     as q-pln-* over an (ev n+ n-) constructor;
;   * program-cost FIXED to a faithful recursive total-node-count (the draft's
;     count-atoms double-counted via size-atom and broke its own additivity axiom).
;
; Dialect: faithful Minimal (no `begin`; structural-match heads like (ev $a $b);
; let*; foldl-atom with a bound list arg). Runs on the same evaluator as PLN/ECAN.
;
; Quantales implemented:
;   q-prob  ([0,1], ⊗=×, ⊕=max, e=1)               scalar probability / fuzzy strength
;   q-pln   (R≥0 × R≥0, ⊗=⊙×, ⊕=⊙+, e=(1,1))       PAIRED paraconsistent evidence (§4.4.1) ⭐
;   q-cdl   (H × H^op, ⊗=(∧,∨), ⊕=(∨,∧))            Constructible-Duality pair (§4.3)
;   q-cost  (R≥0, ⊗=+, ⊕=min, e=0)                 Occam complexity (tropical)
;   q-var   = q-prob                                MOSES variation strength
;   q-prog  (P(Prog), ⊗=Compose, ⊕=Choose, e=Id)   program-space (symbolic)
;
; Weakness morphism w : q-prog → q-cost is program-cost (node count); CoDD weakness
; w(h) = N · 2^(-σ(h)) is codd-weakness (§5.5, Axiom W9).

; ════════════════════════════════════════════════════════════════════════════
; Q_prob — scalar probability quantale ([0,1], ×, max, 1)   (§3 Q_prob)
; ════════════════════════════════════════════════════════════════════════════
; ⊗ = × independent conjunction ; ⊕ = max fuzzy disjunction.

(= (q-prob-times $a $b) (* $a $b))
(= (q-prob-join  $a $b) (max $a $b))
; Units/zeros are nullary expression-functions (= (q-prob-unit) ...) — a bare
; symbol `(= sym v)` does NOT reduce on Minimal; only an expression head does.
(= (q-prob-unit) 1.0)
(= (q-prob-zero) 0.0)

; Residuum a ⊸ b = min(1, b/a) ; a=0 ⇒ 1 (vacuous). Quantale implication.
(= (q-prob-resid $a $b)
   (if (== $a 0) 1.0 (min 1.0 (/ $b $a))))

; ════════════════════════════════════════════════════════════════════════════
; Q_PLN — PAIRED paraconsistent evidence quantale (§4.4.1)   ⭐ the real Q_PLN
; ════════════════════════════════════════════════════════════════════════════
; V_PLN = R≥0 × R≥0, an (ev n+ n-) pair of (positive, negative) evidence counts.
;   ⊕ unions independent micro-situations by ADDING counts;
;   ⊗ does independent conjunction by MULTIPLYING counts.
; This is NOT the scalar [0,1] quantale — it tracks paraconsistent evidence so a
; proposition carries both support (n+) and refutation (n-).

(= (q-pln-times (ev $np $nn) (ev $mp $mn)) (ev (* $np $mp) (* $nn $mn)))
(= (q-pln-join  (ev $np $nn) (ev $mp $mn)) (ev (+ $np $mp) (+ $nn $mn)))
(= (q-pln-unit) (ev 1.0 1.0))
(= (q-pln-zero) (ev 0.0 0.0))

; ════════════════════════════════════════════════════════════════════════════
; Q_CDL — Constructible-Duality pair + isomorphism to Q_PLN (§4.3, §4.4.2)
; ════════════════════════════════════════════════════════════════════════════
; Raw evidence pairs (x, x') over H = ([0,∞], ≤, ∧=min, ∨=max):
;   (x,x') ⊕ (y,y') = (x∨y, x'∧y') = (max, min)
;   (x,x') ⊗ (y,y') = (x∧y, x'∨y') = (min, max)
; CDL models paraconsistent reasoning (positive support × negative refutation).
; We reuse the (ev x x') constructor as the carrier.

(= (q-cdl-join  (ev $x $xp) (ev $y $yp)) (ev (max $x $y) (min $xp $yp)))
(= (q-cdl-times (ev $x $xp) (ev $y $yp)) (ev (min $x $y) (max $xp $yp)))

; §4.4.2 isomorphism Φ : V_CD → V_PLN, Φ(x, x') = (N·x, N·x'), N = ensemble size.
; Commutative-quantale homomorphism mapping CDL truth-pairs to evidence counts.
(= (phi-cdl->pln $N (ev $x $xp)) (ev (* $N $x) (* $N $xp)))

; ════════════════════════════════════════════════════════════════════════════
; Q_cost — complexity quantale (R≥0, +, min, 0)   (§3 Q_cost, tropical)
; ════════════════════════════════════════════════════════════════════════════
; ⊗ = + composition adds cost ; ⊕ = min choice takes the simpler. The Occam bias.

(= (q-cost-times $a $b) (+ $a $b))
(= (q-cost-join  $a $b) (min $a $b))
(= (q-cost-unit) 0.0)

; Residuum a ⊸ b = max(0, b - a) : the extra-cost budget beyond a (no negatives).
(= (q-cost-resid $a $b) (max 0.0 (- $b $a)))

; ════════════════════════════════════════════════════════════════════════════
; Q_var — variation quantale (defaults to scalar Q_prob)   (§9.2)
; ════════════════════════════════════════════════════════════════════════════
; MOSES crossover/mutation (MORK-MOSES §7) build on these. Default domain = Q_prob.

(= (q-var-times $a $b) (q-prob-times $a $b))
(= (q-var-join  $a $b) (q-prob-join  $a $b))
(= (q-var-unit) (q-prob-unit))
(= (q-var-resid $a $b) (q-prob-resid $a $b))

; ════════════════════════════════════════════════════════════════════════════
; Q_prog — program-space quantale (P(Prog), Compose, Choose, Id)   (§9.3)
; ════════════════════════════════════════════════════════════════════════════
; Programs are MeTTa expressions. Compose = sequential composition (⊗_prog),
; Choose = nondeterministic union (⊕_prog), IdentityProgram = unit. Symbolic here;
; gCoDD (deferred) would back these with hash-consed content-addressed dedup.

(= (q-prog-id) IdentityProgram)
(= (q-prog-times $p1 $p2) (Compose $p1 $p2))
(= (q-prog-join  $p1 $p2) (Choose  $p1 $p2))
(= (q-prog-equal? $p1 $p2) (== $p1 $p2))

; ════════════════════════════════════════════════════════════════════════════
; Weakness morphism  w : q-prog → q-cost   (§6.1.2, §9.4)
; ════════════════════════════════════════════════════════════════════════════
; program-cost = TOTAL NODE COUNT (each leaf atom contributes unit cost; §3 gCoDD
; "total node count = weakness measure"). Faithful recursive count, FIXED from the
; draft which used size-atom (direct-child count, not recursive total).
;
;   program-cost(leaf)          = 1
;   program-cost(expr c1..cn)   = Σ program-cost(ci)        (folds over ALL elements,
;                                                            head symbol included)
; This realises the CoDD cost recurrence σ(⊗_i(y,z)) = σ(y)+σ(z)+c_i with the
; constructor head as the unit-cost combinator c_i = 1 :
;   program-cost(Compose p q) = program-cost(p) + program-cost(q) + 1.
(= (program-cost $x)
   (if (== (get-metatype $x) Expression)
       (foldl-atom $x 0 $acc $c (+ $acc (program-cost $c)))
       1))

; CoDD weakness — Axiom W9 (§5.5):  w(h) = N · 2^(-σ(h)) = N / 2^σ(h),  N = world count.
; Division form (not pow 2 negative) — integer pow throws DomainError on negatives.
; Exact length↔weakness bijection (every combinator halves weakness when all c_i=1).
(= (codd-weakness $prog $world-count)
   (/ $world-count (pow 2 (program-cost $prog))))

; ── General quantale weakness — Axiom W1 (§2.8) ──────────────────────────────
; w(H) = ⊕_{(u,v)∈H} [ μ(u) ⊗ μ(v) ].  Here specialised to the Bennett/counting
; quantale (⊗ = ×, ⊕ = +) so Bennett recovery (W3) holds: μ≡1 ⇒ w(H) = |H|.
; H is a list of pairs (P u v) ; $mu is a unary measure function symbol.
(= (pair-measure (P $u $v) $mu) (* ($mu $u) ($mu $v)))
(= (weakness $pairs $mu)
   (foldl-atom $pairs 0 $acc $pr (+ $acc (pair-measure $pr $mu))))

; ════════════════════════════════════════════════════════════════════════════
; Functorial morphisms between quantales   (§9.7)
; ════════════════════════════════════════════════════════════════════════════
; f : q-cost → q-var — simpler programs get milder mutations (rate 0.1 / unit cost).
(= (cost-to-var $cost) (* 0.1 $cost))
; g : q-prob → q-var — inference confidence to variation strength (identity default).
(= (pln-to-var $confidence) $confidence)
; h : q-prog → q-prob — program complexity seeds a prior: 1 / (1 + cost).
(= (prog-to-pln $prog)
   (let $cost (program-cost $prog) (/ 1.0 (+ 1.0 $cost))))
