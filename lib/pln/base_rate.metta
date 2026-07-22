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

;; ── re-validation confidence (R10) ───────────────────────────────────────────────────────────────
;; A stale belief's confidence, refreshed from the evidence that still anchors the symbol. Strength is
;; deliberately NOT recomputed here: re-validation refreshes how confident we are given current
;; evidence, it does not invent what we believe.
(= (EvidenceConfidence $n) (Truth_w2c $n))

;; ── consistency of a base rate with a conditional (PLN book §5.2.2.2) ────────────────────────────
;; Exposed so a caller can ASK whether a link strength is possible given two base rates, rather than
;; discovering it only via the (stv 1 0) fallback: P(B|A) must lie in
;;     [ max(0, (sA + sB - 1)/sA) , min(1, sB/sA) ]
(= (BaseRateAdmits $sA $sB $sAB)
   (and (> $sA 0)
        (and (>= $sAB (max 0.0 (/safe (- (+ $sA $sB) 1.0) $sA)))
             (<= $sAB (min 1.0 (/safe $sB $sA))))))
