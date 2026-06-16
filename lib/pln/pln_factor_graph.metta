;; ═══════════════════════════════════════════════════════════════════════════
;; PLN factor-graph forward chain — substrate-native (Core), conclusion-first schema.
;;
;; This is the §3.4 SIMPLIFIED forward layer that the demand-driven Layer-1 chainer
;; rides on (PLN_backward_chaining_factor_graphs_spec). It is DISTINCT from the book
;; Truth_* maps in pln_core_logic.metta: the book layer is the contract (weight-of-
;; evidence confidence); this §3.4 layer is the approximation the demand sensitivities
;; are computed against. Differentially validated against the Julia oracle
;; (MorkSupercompiler/src/mgfw/PLNDemand.jl `forward_supply`) on the §6.1 Mammal/Lassie
;; worked example → marginal (0.8935, 0.456).
;;
;; SCHEMA (conclusion-first, per Gate-2 / _derive_prefix):
;;   (message <node> (stv s c))                                   ; a leaf node's truth value
;;   (factor <f> <rule> (premises <p1> <p2>) (conclusion <n>))    ; a factor definition
;;   (produces <conclusion> <factor>)                             ; INVERTED index — conclusion
;;                                                                ; FIRST so `(produces X $f)`
;;                                                                ; is a prefix-cheap lookup.
;; ═══════════════════════════════════════════════════════════════════════════

;; §3.4 HMP forward map (product strength, product confidence, pi_b=0):
;;   B = (sA * sAB, cA * cAB)
(= (fwd-hmp (stv $sA $cA) (stv $sAB $cAB)) (stv (* $sA $sAB) (* $cA $cAB)))

;; forward supply: a leaf returns its message; otherwise forward-evaluate the factor
;; that produces it. The leaf case is guarded by `collapse` (empty ⇒ no message), and
;; the producing-factor lookups are let*-sequenced so each `match` reduces before the
;; next (a nested match in template position is returned UNREDUCED in Core).
(= (supply $n)
   (if (== (collapse (match &self (message $n $s) $s)) ())
       (supply-via-factor $n)
       (match &self (message $n $s) $s)))

(= (supply-via-factor $n)
   (let* (($f  (match &self (produces $n $ff) $ff))
          ($p1 (match &self (factor $f hmp (premises $a $b) (conclusion $n)) $a))
          ($p2 (match &self (factor $f hmp (premises $a $b) (conclusion $n)) $b)))
     (fwd-hmp (supply $p1) (supply $p2))))
