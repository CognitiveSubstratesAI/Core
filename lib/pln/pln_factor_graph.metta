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
;; §3.4 forward maps (2-premise rules). HMP = product (pi_b=0). Each consumes two `(stv s c)`.
(= (fwd-hmp (stv $sA $cA) (stv $sAB $cAB)) (stv (* $sA $sAB) (* $cA $cAB)))
(= (fwd-conjunction (stv $s1 $c1) (stv $s2 $c2))                                    ; eq 21
   (stv (* $s1 $s2) (- 1.0 (* (- 1.0 $c1) (- 1.0 $c2)))))
(= (fwd-disjunction (stv $s1 $c1) (stv $s2 $c2))                                    ; eq 24
   (stv (- (+ $s1 $s2) (* $s1 $s2)) (- (+ $c1 $c2) (* $c1 $c2))))
(= (fwd-negation (stv $s $c)) (stv (- 1.0 $s) $c))                                  ; §3.4 (1-premise)

;; rule-keyed forward dispatch (2-premise): supply routes on the factor's rule symbol.
(= (apply-fwd hmp         $a $b) (fwd-hmp $a $b))
(= (apply-fwd conjunction $a $b) (fwd-conjunction $a $b))
(= (apply-fwd disjunction $a $b) (fwd-disjunction $a $b))

;; forward supply: a leaf returns its message; otherwise forward-evaluate the factor
;; that produces it. The leaf case is guarded by `collapse` (empty ⇒ no message), and
;; the producing-factor lookups are let*-sequenced so each `match` reduces before the
;; next (a nested match in template position is returned UNREDUCED in Core).
(= (supply $n)
   (if (== (collapse (match &self (message $n $s) $s)) ())
       (supply-via-factor $n)
       (match &self (message $n $s) $s)))

(= (supply-via-factor $n)
   (let* (($f    (match &self (produces $n $ff) $ff))     ; conclusion-first: prefix-cheap, binds $f
          ($rule (match &self (factor $f $r (premises $a $b) (conclusion $n)) $r))  ; $f bound ⇒ cheap
          ($p1   (match &self (factor $f $r (premises $a $b) (conclusion $n)) $a))
          ($p2   (match &self (factor $f $r (premises $a $b) (conclusion $n)) $b)))
     (apply-fwd $rule (supply $p1) (supply $p2))))

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

;; 2-premise sensitivities → (spair sensP1 sensP2): the ∞-norm Jacobian blocks per rule.
(= (sens2-hmp         (stv $sA $cA) (stv $sB $cB)) (spair (max $sB $cB) (max $sA $cA)))
(= (sens2-conjunction (stv $s1 $c1) (stv $s2 $c2))                                      ; eqs 22,23
   (spair (max $s2 (- 1.0 $c2)) (max $s1 (- 1.0 $c1))))
(= (sens2-disjunction (stv $s1 $c1) (stv $s2 $c2))                                      ; eqs 25,26
   (spair (max (- 1.0 $s2) (- 1.0 $c2)) (max (- 1.0 $s1) (- 1.0 $c1))))
(= (apply-sens2 hmp         $a $b) (sens2-hmp $a $b))
(= (apply-sens2 conjunction $a $b) (sens2-conjunction $a $b))
(= (apply-sens2 disjunction $a $b) (sens2-disjunction $a $b))

;; rule-agnostic 2-premise Eq-1 adjoint: normalize by S=max, Ψ_i = clamp(dv·sens_i/S·(1−c_i)).
(= (adjoint2 $dv (spair $senA $senB) (stv $sA $cA) (stv $sB $cB))
   (let* (($S  (max $senA $senB))
          ($pA (clampu (* (* $dv (/ $senA $S)) (- 1.0 $cA))))
          ($pB (clampu (* (* $dv (/ $senB $S)) (- 1.0 $cB)))))
     (dpair $pA $pB)))

;; demand on a conclusion (demand $dv) → the (Ψ_p1, Ψ_p2) pair of the 2-premise factor that
;; produces it, DISPATCHED on the factor's rule. Factor resolved via the conclusion-first
;; `(produces $conc $f)` index — Gate-2's prefix-cheap lookup, under backward-demand load.
(= (factor-demand-pair $conc $dv)
   (let* (($f    (match &self (produces $conc $ff) $ff))     ; conclusion-first: prefix-cheap, binds $f
          ($rule (match &self (factor $f $r (premises $a $b) (conclusion $conc)) $r))  ; $f bound ⇒ cheap
          ($p1   (match &self (factor $f $r (premises $a $b) (conclusion $conc)) $a))
          ($p2   (match &self (factor $f $r (premises $a $b) (conclusion $conc)) $b))
          ($m1 (supply $p1)) ($m2 (supply $p2)))
     (adjoint2 $dv (apply-sens2 $rule $m1 $m2) $m1 $m2)))

;; ── deduction (4-premise) demand: rows-only sens (§3.4 eqs 8-11) + Eq-1 adjoint ──────
;; Premises are stored in SEMANTIC ROLE ORDER (B C AB BC = premise_1..4); deduction is
;; ASYMMETRIC, so each premise's demand is position-specific (non-circular). cap-sens caps
;; the singular boundary (sB→1) at SENS_CAP per the oracle (this example is non-singular).
(= (absf $x)     (if (< $x 0.0) (- 0.0 $x) $x))
(= (cap-sens $x) (let $a (absf $x) (if (> $a 1000000.0) 1000000.0 $a)))
(= (conf (stv $s $c)) $c)

(= (sens-deduction (stv $sB $cB) (stv $sC $cC) (stv $sAB $cAB) (stv $sBC $cBC))
   (let* (($d   (- 1.0 $sB))
          ($oma (- 1.0 $sAB))
          ($psB (+ (/ (* (- 0.0 $oma) $sBC) $d)
                   (/ (* $oma (- $sC (* $sB $sBC))) (* $d $d))))      ; eq 8
          ($psC (/ $oma $d))                                          ; eq 9
          ($psAB (- $sBC (/ (- $sC (* $sB $sBC)) $d)))                ; eq 10
          ($psBC (- $sAB (/ (* $oma $sB) $d)))                        ; eq 11
          ($pcB (* (* $cC $cAB) $cBC)) ($pcC (* (* $cB $cAB) $cBC))
          ($pcAB (* (* $cB $cC) $cBC)) ($pcBC (* (* $cB $cC) $cAB)))
     (quad (max (cap-sens $psB)  (cap-sens $pcB))
           (max (cap-sens $psC)  (cap-sens $pcC))
           (max (cap-sens $psAB) (cap-sens $pcAB))
           (max (cap-sens $psBC) (cap-sens $pcBC)))))

(= (demand-quad $dv (quad $sB $sC $sAB $sBC) (quad $cB $cC $cAB $cBC))
   (let* (($S (max (max $sB $sC) (max $sAB $sBC)))
          ($pB  (clampu (* (* $dv (/ $sB  $S)) (- 1.0 $cB))))
          ($pC  (clampu (* (* $dv (/ $sC  $S)) (- 1.0 $cC))))
          ($pAB (clampu (* (* $dv (/ $sAB $S)) (- 1.0 $cAB))))
          ($pBC (clampu (* (* $dv (/ $sBC $S)) (- 1.0 $cBC)))))
     (dquad $pB $pC $pAB $pBC)))

(= (factor-demand-quad $conc $dv)
   (let* (($f  (match &self (produces $conc $ff) $ff))
          ($pB  (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $conc)) $b))
          ($pC  (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $conc)) $c))
          ($pAB (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $conc)) $ab))
          ($pBC (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $conc)) $bc)))
     (demand-quad $dv
        (sens-deduction (supply $pB) (supply $pC) (supply $pAB) (supply $pBC))
        (quad (conf (supply $pB)) (conf (supply $pC)) (conf (supply $pAB)) (conf (supply $pBC))))))

;; ── rows-only rules: forward maps + inversion (3-premise) demand + negation (1-premise) demand ──
;; Forward maps (§3.4, singular at sA→0 / sB→1; the demand sensitivities cap these — see cap-sens).
(= (fwd-inversion (stv $sA $cA) (stv $sB $cB) (stv $sBA $cBA))                    ; eq 6/12
   (stv (/ (* $sBA $sB) $sA) (* (* $cA $cB) $cBA)))
(= (fwd-deduction (stv $sB $cB) (stv $sC $cC) (stv $sAB $cAB) (stv $sBC $cBC))    ; eq 6/7
   (stv (+ (* $sAB $sBC) (/ (* (- 1.0 $sAB) (- $sC (* $sB $sBC))) (- 1.0 $sB)))
        (* (* (* $cB $cC) $cAB) $cBC)))

;; inversion sensitivity (premises [A B BA]) → (triple senA senB senBA), eqs 12-13, capped at sA→0.
(= (sens-inversion (stv $sA $cA) (stv $sB $cB) (stv $sBA $cBA))
   (triple (max (cap-sens (/ (* $sBA $sB) (* $sA $sA))) (cap-sens (* $cB $cBA)))
           (max (cap-sens (/ $sBA $sA)) (cap-sens (* $cA $cBA)))
           (max (cap-sens (/ $sB $sA)) (cap-sens (* $cA $cB)))))

;; 3-premise Eq-1 adjoint
(= (adjoint3 $dv (triple $senA $senB $senBA) (stv $a $cA) (stv $b $cB) (stv $c $cBA))
   (let* (($S (max (max $senA $senB) $senBA))
          ($pA  (clampu (* (* $dv (/ $senA  $S)) (- 1.0 $cA))))
          ($pB  (clampu (* (* $dv (/ $senB  $S)) (- 1.0 $cB))))
          ($pBA (clampu (* (* $dv (/ $senBA $S)) (- 1.0 $cBA)))))
     (dtriple $pA $pB $pBA)))

;; inversion demand — conclusion-first index, premises in role order [A B BA].
(= (factor-demand-triple $conc $dv)
   (let* (($f (match &self (produces $conc $ff) $ff))
          ($pA  (match &self (factor $f inversion (premises $a $b $ba) (conclusion $conc)) $a))
          ($pB  (match &self (factor $f inversion (premises $a $b $ba) (conclusion $conc)) $b))
          ($pBA (match &self (factor $f inversion (premises $a $b $ba) (conclusion $conc)) $ba)))
     (adjoint3 $dv (sens-inversion (supply $pA) (supply $pB) (supply $pBA))
               (supply $pA) (supply $pB) (supply $pBA))))

;; negation demand (1-premise, sens = 1): Ψ = clamp(dv · (1 − c)).
(= (factor-demand-single $conc $dv)
   (let* (($f (match &self (produces $conc $ff) $ff))
          ($p (match &self (factor $f negation (premises $a) (conclusion $conc)) $a)))
     (dsingle (clampu (* $dv (- 1.0 (conf (supply $p))))))))

;; ── multi-factor demand SWEEP (§4.4 compute_demand_field) ─────────────────────
;; Top-down BFS from the query via the conclusion-first `produces` index (prefix-cheap),
;; threading each conclusion's demand down as the d_v of its producing factor. The demand
;; FIELD is materialised AS ATOMS in the space: `(dem <node> <value>)`. Forward marginals
;; are threaded automatically (factor sens uses `supply`, which forward-computes intermediates).
;; NOTE: tree-shaped graphs only — a node reached by >1 path needs MAX-JOIN
;; (dem[p] = max(old, Ψ)); add when a DAG workload requires it (§4.4 max-join).
(= (dp-1 (dpair $a $b)) $a)
(= (dp-2 (dpair $a $b)) $b)

(= (compute-demand-field! $query)
   (let $seed (add-atom &self (dem $query 1.0)) (propagate! $query)))

(= (propagate! $node)
   (let* (($dv   (match &self (dem $node $d) $d))
          ($f    (match &self (produces $node $ff) $ff))     ; conclusion-first: prefix-cheap, binds $f
          ($rule (match &self (factor $f $r (premises $a $b) (conclusion $node)) $r))
          ($p1   (match &self (factor $f $r (premises $a $b) (conclusion $node)) $a))
          ($p2   (match &self (factor $f $r (premises $a $b) (conclusion $node)) $b))
          ($pair (adjoint2 $dv (apply-sens2 $rule (supply $p1) (supply $p2)) (supply $p1) (supply $p2)))
          ($d1 (dp-1 $pair))                              ; bind REDUCED before add-atom
          ($d2 (dp-2 $pair))
          ($e1 (add-atom &self (dem $p1 $d1)))
          ($e2 (add-atom &self (dem $p2 $d2))))
     (let $r1 (recurse-if-produced! $p1) (recurse-if-produced! $p2))))

(= (recurse-if-produced! $node)
   (if (== (collapse (match &self (produces $node $f) $f)) ()) () (propagate! $node)))
