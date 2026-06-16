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

;; ── demand-driven backward chain (§3.3 Eq 1) on the §3.4 sensitivity ──────────
;; Built on the SAME §3.4 product map as the forward chain (decision: factor-graph layer
;; = §3.4; book Truth_* = the contract). sens_hmp = ∞-norm Jacobian of fwd-hmp (pi_b=0):
;;   sens_A  = max(sAB, cAB)   (∂out/∂A — derives from the OTHER premise: transpose-prone)
;;   sens_AB = max(sA,  cA)    (∂out/∂AB)
;; Eq 1 adjoint, per premise i:  Ψ_i = clamp_[0,1]( d_v · sens_i/S · (1 − c_i) ),  S = max_j sens_j.
(= (clampu $x) (if (< $x 0.0) 0.0 (if (> $x 1.0) 1.0 $x)))

(= (hmp-demand $dv (stv $sA $cA) (stv $sAB $cAB))
   (let* (($senA  (max $sAB $cAB))
          ($senAB (max $sA  $cA))
          ($S     (max $senA $senAB))
          ($psiA  (clampu (* (* $dv (/ $senA  $S)) (- 1.0 $cA))))
          ($psiAB (clampu (* (* $dv (/ $senAB $S)) (- 1.0 $cAB)))))
     (dpair $psiA $psiAB)))

;; demand on a conclusion (with demand $dv) → the (Ψ_premise1, Ψ_premise2) pair of the factor
;; that produces it. Resolves the factor via the conclusion-first `(produces $conc $f)` index —
;; the Gate-2 prefix-cheap lookup, here under its intended BACKWARD-demand load.
(= (factor-demand-pair $conc $dv)
   (let* (($f  (match &self (produces $conc $ff) $ff))
          ($p1 (match &self (factor $f hmp (premises $a $b) (conclusion $conc)) $a))
          ($p2 (match &self (factor $f hmp (premises $a $b) (conclusion $conc)) $b)))
     (hmp-demand $dv (supply $p1) (supply $p2))))
