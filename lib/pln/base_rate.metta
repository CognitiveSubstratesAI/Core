;; lib/pln/base_rate.metta — node BASE RATES as MeTTa formulas.
;;
;; A PLN node's strength is its BASE RATE: P(C), the chance a random element of the universe is in C —
;; not "how true C is". These are the formulas the world model uses to give a node an STV; the HOST
;; supplies only the two counts (an extension size and a universe size, both substrate queries over the
;; trie) and never the arithmetic.
;;
;; Confidence rides the CANONICAL count->confidence map already defined in pln_core_logic.metta:
;;     (= (Truth_w2c $w) (/safe $w (+ $w 1)))        ; k = 1
;; Do NOT re-derive n/(n+1) anywhere else — a second copy of a truth-value formula is exactly how the
;; Julia/MeTTa divergence that killed 2-hop deduction happened (node_stv fabricating (0,0) against
;; `(= (STV $stv) (empty))`). One definition, referenced.
;;
;; ABSENCE IS NOT A TRUTH VALUE. A concept with no instances, or an empty universe, yields `no-evidence`
;; — NOT (0,0). `(0,0)` claims "strength 0 with no confidence", which fails PLN's `as > 0` consistency
;; precondition and silently forces the (stv 1 0) ignorance fallback. Callers must treat `no-evidence`
;; as "skip this candidate", mirroring `(= (STV $stv) (empty))` and CeTTa's lib_pln.metta:127.

;; NO type declarations here, deliberately: a declared return type of `Atom` makes the metta driver return
;; the body LAZILY (the `typ == ATOM_T` short-circuit) — `(BaseRateTv 3 7)` came back as its own unevaluated
;; `if`. Domain libs stay BARE; only stdlib/FFI is typed.
;; ── the extensional base rate ────────────────────────────────────────────────────────────────────
;; s = |ext(C)| / |universe|   — the textbook extensional prior
;; c = Truth_w2c(|ext(C)|)     — evidence mass from the instance count, on the shared k=1 scale
;; `stv` is a CONSTRUCTOR, so its arguments are not reduced inside it — writing
;; `(stv (/safe $ext $universe) (Truth_w2c $ext))` returns those terms UNEVALUATED. Bind first with let*,
;; then construct. (Verified: the constructor form came back as `(stv (/safe 3 7) (Truth_w2c 3))`.)
(= (BaseRateTv $ext $universe)
   (if (or (<= $universe 0) (<= $ext 0))
       no-evidence
       (let* (($s (/safe $ext $universe))
              ($c (Truth_w2c $ext)))
          (stv $s $c))))

;; `EvidenceConfidence` MOVED to `decay.metta` — it is a re-validation (R10 belief-dynamics) concept,
;; not a base rate, and it now sits beside the decay law that creates the staleness it answers.

;; ── consistency of a base rate with a conditional (PLN book §5.2.2.2) ────────────────────────────
;; Exposed so a caller can ASK whether a link strength is possible given two base rates, rather than
;; discovering it only via the (stv 1 0) fallback: P(B|A) must lie in
;;     [ max(0, (sA + sB - 1)/sA) , min(1, sB/sA) ]
;;
;; This is a NAME, not a formula. The interval test already exists in this same library and loads into
;; this same Space as `conditional-probability-consistency` (pln_core_logic.metta:175-180, on
;; smallest-/largest-intersection-probability :148-154). It was originally written out again here, and
;; the two copies had ALREADY diverged: this one used max/min where canonical uses `clamp`, and — the
;; reason this is a bug and not a style note — its `(> $sA 0)` guard was INOPERATIVE. `and` is a
;; grounded EAGER op (Interpreter.jl:1938, no short-circuit) and `/safe` returns `(empty)` on a
;; non-positive denominator (pln_core_logic.metta:43-46), so the empty annihilated the conjunction:
;; `(BaseRateAdmits 0.0 0.5 0.5)` evaluated to NOTHING AT ALL rather than to False — a decision
;; procedure that vanishes instead of answering, which is the fail-OPEN shape this project bans.
;; Canonical gets sA=0 right because it divides with plain `/` inside a `clamp`, so the conjunction
;; survives to be decided by `(< 0 $As)` = False.
;; Delegating rather than re-deriving is the rule this file's own header states 35 lines above.
(= (BaseRateAdmits $sA $sB $sAB)
   (conditional-probability-consistency $sA $sB $sAB))
