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

;; ── induction + abduction (5-premise, rows-only): chain-rule sens through the inversion
;; intermediate (ind: sAB=sBA·sB/sA; abd: sBC=sCB·sC/sB), reusing the deduction strength
;; partials. Multiple singularities (ind sA→0 & sB→1; abd sB→0 & sB→1), all capped. Abduction
;; sens_A = 0 (premise A absent from the formula) ⇒ dem_A is exactly 0 even at the singularity.
(= (fwd-induction (stv $sA $cA) (stv $sB $cB) (stv $sC $cC) (stv $sBA $cBA) (stv $sBC $cBC))  ; eq 14
   (stv (+ (/ (* (* $sBA $sBC) $sB) $sA)
           (/ (* (- 1.0 (/ (* $sBA $sB) $sA)) (- $sC (* $sB $sBC))) (- 1.0 $sB)))
        (* (* (* $cBA $cBC) $cB) $cC)))
(= (fwd-abduction (stv $sA $cA) (stv $sB $cB) (stv $sC $cC) (stv $sAB $cAB) (stv $sCB $cCB))  ; eq 15
   (stv (+ (/ (* (* $sAB $sCB) $sC) $sB)
           (/ (* (* $sC (- 1.0 $sAB)) (- 1.0 $sCB)) (- 1.0 $sB)))
        (* (* (* $cAB $cCB) $cB) $cC)))

;; deduction strength partials → (dparts dB dC dAB dBC), shared by induction & abduction.
(= (ded-partials $sB $sC $sAB $sBC)
   (let* (($d (- 1.0 $sB)) ($oma (- 1.0 $sAB)))
     (dparts (+ (/ (* (- 0.0 $oma) $sBC) $d) (/ (* $oma (- $sC (* $sB $sBC))) (* $d $d)))
             (/ $oma $d) (- $sBC (/ (- $sC (* $sB $sBC)) $d)) (- $sAB (/ (* $oma $sB) $d)))))
(= (dp-dB (dparts $dB $dC $dAB $dBC)) $dB)
(= (dp-dC (dparts $dB $dC $dAB $dBC)) $dC)
(= (dp-dAB (dparts $dB $dC $dAB $dBC)) $dAB)
(= (dp-dBC (dparts $dB $dC $dAB $dBC)) $dBC)

;; induction sensitivity (premises [A B C BA BC]). A,BA enter ONLY via sAB; B via sAB AND directly.
(= (sens-induction (stv $sA $cA) (stv $sB $cB) (stv $sC $cC) (stv $sBA $cBA) (stv $sBC $cBC))
   (let* (($sAB (/ (* $sBA $sB) $sA)) ($parts (ded-partials $sB $sC $sAB $sBC))
          ($dB (dp-dB $parts)) ($dC (dp-dC $parts)) ($dAB (dp-dAB $parts)) ($dBC (dp-dBC $parts))
          ($iA (/ (* (- 0.0 $sBA) $sB) (* $sA $sA))) ($iB (/ $sBA $sA)) ($iBA (/ $sB $sA))
          ($psA (* $dAB $iA)) ($psBA (* $dAB $iBA)) ($psB (+ (* $dAB $iB) $dB))
          ($pcB (* (* $cBA $cBC) $cC)) ($pcC (* (* $cBA $cBC) $cB))
          ($pcBA (* (* $cBC $cB) $cC)) ($pcBC (* (* $cBA $cB) $cC)))
     (quint (cap-sens $psA) (max (cap-sens $psB) (cap-sens $pcB)) (max (cap-sens $dC) (cap-sens $pcC))
            (max (cap-sens $psBA) (cap-sens $pcBA)) (max (cap-sens $dBC) (cap-sens $pcBC)))))

;; abduction sensitivity (premises [A B C AB CB]). sens_A=0 (A absent). B,C enter directly AND via sBC.
(= (sens-abduction (stv $sA $cA) (stv $sB $cB) (stv $sC $cC) (stv $sAB $cAB) (stv $sCB $cCB))
   (let* (($sBC (/ (* $sCB $sC) $sB)) ($parts (ded-partials $sB $sC $sAB $sBC))
          ($dB (dp-dB $parts)) ($dC (dp-dC $parts)) ($dAB (dp-dAB $parts)) ($dBC (dp-dBC $parts))
          ($jB (/ (* (- 0.0 $sCB) $sC) (* $sB $sB))) ($jC (/ $sCB $sB)) ($jCB (/ $sC $sB))
          ($psB (+ $dB (* $dBC $jB))) ($psC (+ $dC (* $dBC $jC))) ($psCB (* $dBC $jCB))
          ($pcB (* (* $cAB $cCB) $cC)) ($pcC (* (* $cAB $cCB) $cB))
          ($pcAB (* (* $cCB $cB) $cC)) ($pcCB (* (* $cAB $cB) $cC)))
     (quint 0.0 (max (cap-sens $psB) (cap-sens $pcB)) (max (cap-sens $psC) (cap-sens $pcC))
            (max (cap-sens $dAB) (cap-sens $pcAB)) (max (cap-sens $psCB) (cap-sens $pcCB)))))

;; 5-premise Eq-1 adjoint
(= (adjoint5 $dv (quint $s1 $s2 $s3 $s4 $s5) (stv $a $c1) (stv $b $c2) (stv $c $c3) (stv $d $c4) (stv $e $c5))
   (let* (($S (max (max (max $s1 $s2) (max $s3 $s4)) $s5))
          ($p1 (clampu (* (* $dv (/ $s1 $S)) (- 1.0 $c1)))) ($p2 (clampu (* (* $dv (/ $s2 $S)) (- 1.0 $c2))))
          ($p3 (clampu (* (* $dv (/ $s3 $S)) (- 1.0 $c3)))) ($p4 (clampu (* (* $dv (/ $s4 $S)) (- 1.0 $c4))))
          ($p5 (clampu (* (* $dv (/ $s5 $S)) (- 1.0 $c5)))))
     (dquint $p1 $p2 $p3 $p4 $p5)))

(= (factor-demand-induction $conc $dv)
   (let* (($f (match &self (produces $conc $ff) $ff))
          ($pA (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $conc)) $a))
          ($pB (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $conc)) $b))
          ($pC (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $conc)) $c))
          ($pBA (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $conc)) $ba))
          ($pBC (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $conc)) $bc)))
     (adjoint5 $dv (sens-induction (supply $pA) (supply $pB) (supply $pC) (supply $pBA) (supply $pBC))
               (supply $pA) (supply $pB) (supply $pC) (supply $pBA) (supply $pBC))))

(= (factor-demand-abduction $conc $dv)
   (let* (($f (match &self (produces $conc $ff) $ff))
          ($pA (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $conc)) $a))
          ($pB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $conc)) $b))
          ($pC (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $conc)) $c))
          ($pAB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $conc)) $ab))
          ($pCB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $conc)) $cb)))
     (adjoint5 $dv (sens-abduction (supply $pA) (supply $pB) (supply $pC) (supply $pAB) (supply $pCB))
               (supply $pA) (supply $pB) (supply $pC) (supply $pAB) (supply $pCB))))

;; ═══════════════════════════════════════════════════════════════════════════
;; §5 DISTRIBUTIONAL TRUTH VALUES — Layer 2 (Beta DTVs in (μ,n) coordinates)
;; A DTV (dtv μ n) summarises Beta(α,β) with mean μ=α/(α+β), concentration n=α+β.
;; The §3 demand construction lifts UNCHANGED (§5.5): only `need` and the sensitivity
;; change. Validated against the §6.2 worked example. SCOPE: heuristic-MP/product rule
;; (the §6.2 chain) + the STV-recovery limit; other rules apply STV formulas at the
;; sample level (§5.6) — follow-up. The demand SWEEP is STV-only so far (slice 2).
;; ═══════════════════════════════════════════════════════════════════════════
(= (dtv-mu (dtv $mu $n)) $mu)
(= (dtv-n  (dtv $mu $n)) $n)

;; §5.3 eq31 information need: need_β = 12·μ(1−μ)/(n+1)  (the α,β≥1 regime)
(= (need-dtv (dtv $mu $n)) (/ (* 12.0 (* $mu (- 1.0 $mu))) (+ $n 1.0)))

;; §5.6 forward heuristic-MP / product map (π_b=0): μ_out=μ1·μ2, concentration moment-
;; matched from the product variance (eq37-41). beta-ex2 = E[X²] for Beta(μn,(1−μ)n).
(= (beta-ex2 $mu $n) (/ (* $mu (+ (* $mu $n) 1.0)) (+ $n 1.0)))
(= (fwd-hmp-dtv (dtv $mu1 $n1) (dtv $mu2 $n2))
   (let* (($muo (* $mu1 $mu2))
          ($var (- (* (beta-ex2 $mu1 $n1) (beta-ex2 $mu2 $n2)) (* $muo $muo)))
          ($no  (- (/ (* $muo (- 1.0 $muo)) $var) 1.0)))
     (dtv $muo $no)))

;; §5.4 eq35 practical sensitivity (mean-Jacobian ∞-norm): ∂μ_out/∂μ1=μ2, ∂μ_out/∂μ2=μ1
(= (sens2-hmp-dtv (dtv $mu1 $n1) (dtv $mu2 $n2)) (spair $mu2 $mu1))

;; §5.5 eq36 DTV demand adjoint — identical SHAPE to the STV adjoint, DTV need + sens
(= (adjoint2-dtv $dv (spair $sA $sB) $pA $pB)
   (let* (($S (max $sA $sB))
          ($dA (clampu (* (* $dv (/ $sA $S)) (need-dtv $pA))))
          ($dB (clampu (* (* $dv (/ $sB $S)) (need-dtv $pB)))))
     (dpair $dA $dB)))

;; §5.7 STV→Beta embedding (STV recovery as a limit): α=s·nc+1, β=(1−s)·nc+1, nc=k·c/(1−c).
;; As nc grows, μ→s and need_β→ the STV confidence-shortfall — DTV reduces to STV.
(= (stv->dtv $s $c $k)
   (let* (($nc (/ (* $k $c) (- 1.0 $c)))
          ($al (+ (* $s $nc) 1.0)) ($be (+ (* (- 1.0 $s) $nc) 1.0)) ($n (+ $al $be)))
     (dtv (/ $al $n) $n)))

;; ── DTV demand sweep (hmp scope) ──────────────────────────────────────────────
;; The DTV analogue of compute-demand-field!: forward DTV marginals via `supply-dtv`,
;; backward demand via `adjoint2-dtv`. Demand values are scalars, so it REUSES dem-join!/
;; dem-cur/dp-1/dp-2 — max-join (DAG support) carries over for free. Messages are
;; (message N (dtv μ n)). NOTE: like the STV sweep it threads FORWARD marginals, so the
;; materialised field differs from §6.2's prior-marginal hand-computation at intermediates;
;; validated by internal consistency + the §5.7 STV-recovery cross-check. SCOPE: hmp rule.
(= (supply-dtv $n)
   (if (== (collapse (match &self (message $n $s) $s)) ())
       (supply-dtv-via-factor $n)
       (match &self (message $n $s) $s)))
(= (supply-dtv-via-factor $n)
   (let* (($f  (match &self (produces $n $ff) $ff))
          ($p1 (match &self (factor $f hmp (premises $a $b) (conclusion $n)) $a))
          ($p2 (match &self (factor $f hmp (premises $a $b) (conclusion $n)) $b)))
     (fwd-hmp-dtv (supply-dtv $p1) (supply-dtv $p2))))

(= (compute-demand-field-dtv! $query) (let $seed (dem-join! $query 1.0) (propagate-dtv! $query)))
(= (propagate-dtv! $node)
   (let* (($dv (car-atom (dem-cur $node)))
          ($f  (match &self (produces $node $ff) $ff))
          ($p1 (match &self (factor $f hmp (premises $a $b) (conclusion $node)) $a))
          ($p2 (match &self (factor $f hmp (premises $a $b) (conclusion $node)) $b))
          ($pair (adjoint2-dtv $dv (sens2-hmp-dtv (supply-dtv $p1) (supply-dtv $p2)) (supply-dtv $p1) (supply-dtv $p2)))
          ($c1 (dem-join! $p1 (dp-1 $pair))) ($c2 (dem-join! $p2 (dp-2 $pair))))
     (let $r1 (recurse-dtv! $p1 $c1) (recurse-dtv! $p2 $c2))))
(= (recurse-dtv! $node $changed)
   (if $changed (if (== (collapse (match &self (produces $node $f) $f)) ()) () (propagate-dtv! $node)) ()))

;; ── multi-factor demand SWEEP (§4.4 compute_demand_field) ─────────────────────
;; Top-down BFS from the query via the conclusion-first `produces` index (prefix-cheap),
;; threading each conclusion's demand down as the d_v of its producing factor. The demand
;; FIELD is materialised AS ATOMS in the space: `(dem <node> <value>)`. Forward marginals
;; are threaded automatically (factor sens uses `supply`, which forward-computes intermediates).
;; §4.4 MAX-JOIN: a node reached by >1 path keeps dem = max over paths. `dem-join!` upserts
;; (remove old, add max) and returns True iff demand INCREASED; recursion continues past a
;; premise only on an increase — a monotone relaxation that converges on DAGs. (Cyclic graphs
;; still need the §4.3 ε_d tolerance + λ_d damping; not handled here.)
(= (dp-1 (dpair $a $b)) $a)
(= (dp-2 (dpair $a $b)) $b)
;; demand-tuple accessors (role order matches each factor-demand-* premise order):
;; triple=inversion[A B BA], quad=deduction[B C AB BC], quint=ind[A B C BA BC]/abd[A B C AB CB], single=negation.
(= (dt-1 (dtriple $a $b $c)) $a) (= (dt-2 (dtriple $a $b $c)) $b) (= (dt-3 (dtriple $a $b $c)) $c)
(= (dq-1 (dquad $a $b $c $d)) $a) (= (dq-2 (dquad $a $b $c $d)) $b) (= (dq-3 (dquad $a $b $c $d)) $c) (= (dq-4 (dquad $a $b $c $d)) $d)
(= (dn-1 (dquint $a $b $c $d $e)) $a) (= (dn-2 (dquint $a $b $c $d $e)) $b) (= (dn-3 (dquint $a $b $c $d $e)) $c) (= (dn-4 (dquint $a $b $c $d $e)) $d) (= (dn-5 (dquint $a $b $c $d $e)) $e)
(= (ds-1 (dsingle $a)) $a)

;; current demand for a node (single value, post-upsert), or () if unset.
(= (dem-cur $node) (collapse (match &self (dem $node $d) $d)))

;; upsert (dem node) := max(old, new). Returns True iff it increased (or was newly set).
;; both-evaluator upsert idiom (match-bind old OUTSIDE template → remove-atom → add-atom).
(= (dem-join! $node $new)
   (let $cur (dem-cur $node)
     (if (== $cur ())
         (let $e (add-atom &self (dem $node $new)) True)
         (let $old (car-atom $cur)
           (if (> $new $old)
               (let* (($r (remove-atom &self (dem $node $old)))
                      ($a (add-atom &self (dem $node $new)))) True)
               False)))))

(= (compute-demand-field! $query)
   (let $seed (dem-join! $query 1.0) (propagate! $query)))

;; ARITY-COMPLETE dispatch: read the producing factor's rule (arity-agnostic match — $prem
;; binds the whole (premises …) sub-expr), then thread demand through ALL 8 rule families,
;; not just the 2-premise ones. Each arity reuses its tested `factor-demand-*` function.
(= (propagate! $node)
   (let* (($dv   (car-atom (dem-cur $node)))            ; node's current (possibly max-joined) demand
          ($f    (match &self (produces $node $ff) $ff))     ; conclusion-first: prefix-cheap, binds $f
          ($rule (match &self (factor $f $rr $prem (conclusion $node)) $rr)))  ; rule symbol, any arity
     (propagate-rule! $node $f $rule $dv)))

(= (propagate-rule! $node $f hmp $dv)         (propagate-2! $node $f $dv))
(= (propagate-rule! $node $f conjunction $dv) (propagate-2! $node $f $dv))
(= (propagate-rule! $node $f disjunction $dv) (propagate-2! $node $f $dv))
(= (propagate-rule! $node $f negation $dv)    (propagate-neg! $node $f $dv))
(= (propagate-rule! $node $f inversion $dv)   (propagate-inv! $node $f $dv))
(= (propagate-rule! $node $f deduction $dv)   (propagate-ded! $node $f $dv))
(= (propagate-rule! $node $f induction $dv)   (propagate-ind! $node $f $dv))
(= (propagate-rule! $node $f abduction $dv)   (propagate-abd! $node $f $dv))

;; 2-premise (hmp / conjunction / disjunction)
(= (propagate-2! $node $f $dv)
   (let* (($rule (match &self (factor $f $r (premises $a $b) (conclusion $node)) $r))
          ($p1   (match &self (factor $f $r (premises $a $b) (conclusion $node)) $a))
          ($p2   (match &self (factor $f $r (premises $a $b) (conclusion $node)) $b))
          ($pair (adjoint2 $dv (apply-sens2 $rule (supply $p1) (supply $p2)) (supply $p1) (supply $p2)))
          ($c1 (dem-join! $p1 (dp-1 $pair))) ($c2 (dem-join! $p2 (dp-2 $pair))))
     (let $r1 (recurse-if-increased! $p1 $c1) (recurse-if-increased! $p2 $c2))))

;; 1-premise (negation)
(= (propagate-neg! $node $f $dv)
   (let* (($p (match &self (factor $f negation (premises $a) (conclusion $node)) $a))
          ($c (dem-join! $p (ds-1 (factor-demand-single $node $dv)))))
     (recurse-if-increased! $p $c)))

;; 3-premise (inversion: A B BA)
(= (propagate-inv! $node $f $dv)
   (let* (($t  (factor-demand-triple $node $dv))
          ($pA  (match &self (factor $f inversion (premises $a $b $ba) (conclusion $node)) $a))
          ($pB  (match &self (factor $f inversion (premises $a $b $ba) (conclusion $node)) $b))
          ($pBA (match &self (factor $f inversion (premises $a $b $ba) (conclusion $node)) $ba))
          ($cA (dem-join! $pA (dt-1 $t))) ($cB (dem-join! $pB (dt-2 $t))) ($cBA (dem-join! $pBA (dt-3 $t))))
     (let* (($r1 (recurse-if-increased! $pA $cA)) ($r2 (recurse-if-increased! $pB $cB)))
       (recurse-if-increased! $pBA $cBA))))

;; 4-premise (deduction: B C AB BC)
(= (propagate-ded! $node $f $dv)
   (let* (($q (factor-demand-quad $node $dv))
          ($pB  (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $b))
          ($pC  (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $c))
          ($pAB (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $ab))
          ($pBC (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $bc))
          ($cB (dem-join! $pB (dq-1 $q))) ($cC (dem-join! $pC (dq-2 $q)))
          ($cAB (dem-join! $pAB (dq-3 $q))) ($cBC (dem-join! $pBC (dq-4 $q))))
     (let* (($r1 (recurse-if-increased! $pB $cB)) ($r2 (recurse-if-increased! $pC $cC))
            ($r3 (recurse-if-increased! $pAB $cAB)))
       (recurse-if-increased! $pBC $cBC))))

;; 5-premise (induction: A B C BA BC)
(= (propagate-ind! $node $f $dv)
   (let* (($q (factor-demand-induction $node $dv))
          ($pA  (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $a))
          ($pB  (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $b))
          ($pC  (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $c))
          ($pBA (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $ba))
          ($pBC (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $bc))
          ($cA (dem-join! $pA (dn-1 $q))) ($cB (dem-join! $pB (dn-2 $q))) ($cC (dem-join! $pC (dn-3 $q)))
          ($cBA (dem-join! $pBA (dn-4 $q))) ($cBC (dem-join! $pBC (dn-5 $q))))
     (let* (($r1 (recurse-if-increased! $pA $cA)) ($r2 (recurse-if-increased! $pB $cB))
            ($r3 (recurse-if-increased! $pC $cC)) ($r4 (recurse-if-increased! $pBA $cBA)))
       (recurse-if-increased! $pBC $cBC))))

;; 5-premise (abduction: A B C AB CB); sens_A = 0 ⇒ dem A is exactly 0
(= (propagate-abd! $node $f $dv)
   (let* (($q (factor-demand-abduction $node $dv))
          ($pA  (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $a))
          ($pB  (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $b))
          ($pC  (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $c))
          ($pAB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $ab))
          ($pCB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $cb))
          ($cA (dem-join! $pA (dn-1 $q))) ($cB (dem-join! $pB (dn-2 $q))) ($cC (dem-join! $pC (dn-3 $q)))
          ($cAB (dem-join! $pAB (dn-4 $q))) ($cCB (dem-join! $pCB (dn-5 $q))))
     (let* (($r1 (recurse-if-increased! $pA $cA)) ($r2 (recurse-if-increased! $pB $cB))
            ($r3 (recurse-if-increased! $pC $cC)) ($r4 (recurse-if-increased! $pAB $cAB)))
       (recurse-if-increased! $pCB $cCB))))

;; recurse past a premise iff its demand increased on this visit AND it has producers.
(= (recurse-if-increased! $node $changed)
   (if $changed
       (if (== (collapse (match &self (produces $node $f) $f)) ()) () (propagate! $node))
       ()))

;; ── §4.7 GATED demand expansion ──────────────────────────────────────────────
;; The sweep + a gate: HALT recursion past a premise whose demand < $tau, but RETAIN it in the
;; `active` set (Design Commitment #2) unless $retain is False — a high-confidence boundary has
;; tiny demand yet still SEEDS forward supply, so dropping it starves the marginal. Writes
;; (dem node val) + (active node) atoms. $tau=0 ⇒ nothing halts ⇒ active = full support set.
;; $retain=False ⇒ DC#2 off (drop halted boundaries — the load-bearing toggle).
;; §4.4 MAX-JOIN (DAG-safe): premise demand is upserted via `dem-join!` (max over paths, one
;; (dem _ _) atom), and a premise is re-expanded only when its demand INCREASES on this visit
;; AND meets $tau — so a boundary that crosses $tau on a later path gets expanded, while the
;; monotone-increase guard keeps recursion finite on DAGs. Activation is dedup-guarded.
(= (is-active $n) (if (== (collapse (match &self (active $n) $n)) ()) False True))

(= (gated-demand-field! $query $tau $retain)
   (let $s (dem-join! $query 1.0)
     (let $a (add-atom &self (active $query)) (gated-propagate! $query $tau $retain))))

;; ARITY-COMPLETE gated dispatch (mirrors the plain sweep): read the rule (any arity), thread
;; demand through ALL 8 rule families via the tested factor-demand-*, gating each premise.
(= (gated-propagate! $node $tau $retain)
   (let* (($f (match &self (produces $node $ff) $ff))
          ($rule (match &self (factor $f $rr $prem (conclusion $node)) $rr)))
     (gated-rule! $node $f $rule $tau $retain)))

(= (gated-rule! $node $f hmp $tau $retain)         (gated-2! $node $f $tau $retain))
(= (gated-rule! $node $f conjunction $tau $retain) (gated-2! $node $f $tau $retain))
(= (gated-rule! $node $f disjunction $tau $retain) (gated-2! $node $f $tau $retain))
(= (gated-rule! $node $f negation $tau $retain)    (gated-neg! $node $f $tau $retain))
(= (gated-rule! $node $f inversion $tau $retain)   (gated-inv! $node $f $tau $retain))
(= (gated-rule! $node $f deduction $tau $retain)   (gated-ded! $node $f $tau $retain))
(= (gated-rule! $node $f induction $tau $retain)   (gated-ind! $node $f $tau $retain))
(= (gated-rule! $node $f abduction $tau $retain)   (gated-abd! $node $f $tau $retain))

;; 2-premise (hmp / conjunction / disjunction)
(= (gated-2! $node $f $tau $retain)
   (let* (($rule (match &self (factor $f $r (premises $a $b) (conclusion $node)) $r))
          ($p1 (match &self (factor $f $r (premises $a $b) (conclusion $node)) $a))
          ($p2 (match &self (factor $f $r (premises $a $b) (conclusion $node)) $b))
          ($pair (adjoint2 (car-atom (dem-cur $node))
                           (apply-sens2 $rule (supply $p1) (supply $p2)) (supply $p1) (supply $p2)))
          ($d1 (dp-1 $pair)) ($d2 (dp-2 $pair))
          ($c1 (dem-join! $p1 $d1)) ($c2 (dem-join! $p2 $d2))    ; upsert max, capture increase
          ($af (if (is-active $f) () (add-atom &self (active $f)))))
     (let $g1 (gate! $p1 $d1 $c1 $tau $retain) (gate! $p2 $d2 $c2 $tau $retain))))

;; 1-premise (negation): sens = 1 ⇒ demand = clamp(dv · (1 − c)).
(= (gated-neg! $node $f $tau $retain)
   (let* (($p (match &self (factor $f negation (premises $a) (conclusion $node)) $a))
          ($du (clampu (* (car-atom (dem-cur $node)) (- 1.0 (conf (supply $p))))))
          ($c (dem-join! $p $du)) ($af (if (is-active $f) () (add-atom &self (active $f)))))
     (gate! $p $du $c $tau $retain)))

;; 3-premise (inversion: A B BA)
(= (gated-inv! $node $f $tau $retain)
   (let* (($t (factor-demand-triple $node (car-atom (dem-cur $node))))
          ($pA  (match &self (factor $f inversion (premises $a $b $ba) (conclusion $node)) $a))
          ($pB  (match &self (factor $f inversion (premises $a $b $ba) (conclusion $node)) $b))
          ($pBA (match &self (factor $f inversion (premises $a $b $ba) (conclusion $node)) $ba))
          ($dA (dt-1 $t)) ($dB (dt-2 $t)) ($dBA (dt-3 $t))
          ($cA (dem-join! $pA $dA)) ($cB (dem-join! $pB $dB)) ($cBA (dem-join! $pBA $dBA))
          ($af (if (is-active $f) () (add-atom &self (active $f)))))
     (let* (($g1 (gate! $pA $dA $cA $tau $retain)) ($g2 (gate! $pB $dB $cB $tau $retain)))
       (gate! $pBA $dBA $cBA $tau $retain))))

;; 4-premise (deduction: B C AB BC)
(= (gated-ded! $node $f $tau $retain)
   (let* (($q (factor-demand-quad $node (car-atom (dem-cur $node))))
          ($pB  (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $b))
          ($pC  (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $c))
          ($pAB (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $ab))
          ($pBC (match &self (factor $f deduction (premises $b $c $ab $bc) (conclusion $node)) $bc))
          ($dB (dq-1 $q)) ($dC (dq-2 $q)) ($dAB (dq-3 $q)) ($dBC (dq-4 $q))
          ($cB (dem-join! $pB $dB)) ($cC (dem-join! $pC $dC)) ($cAB (dem-join! $pAB $dAB)) ($cBC (dem-join! $pBC $dBC))
          ($af (if (is-active $f) () (add-atom &self (active $f)))))
     (let* (($g1 (gate! $pB $dB $cB $tau $retain)) ($g2 (gate! $pC $dC $cC $tau $retain))
            ($g3 (gate! $pAB $dAB $cAB $tau $retain)))
       (gate! $pBC $dBC $cBC $tau $retain))))

;; 5-premise (induction: A B C BA BC)
(= (gated-ind! $node $f $tau $retain)
   (let* (($q (factor-demand-induction $node (car-atom (dem-cur $node))))
          ($pA  (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $a))
          ($pB  (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $b))
          ($pC  (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $c))
          ($pBA (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $ba))
          ($pBC (match &self (factor $f induction (premises $a $b $c $ba $bc) (conclusion $node)) $bc))
          ($dA (dn-1 $q)) ($dB (dn-2 $q)) ($dC (dn-3 $q)) ($dBA (dn-4 $q)) ($dBC (dn-5 $q))
          ($cA (dem-join! $pA $dA)) ($cB (dem-join! $pB $dB)) ($cC (dem-join! $pC $dC)) ($cBA (dem-join! $pBA $dBA)) ($cBC (dem-join! $pBC $dBC))
          ($af (if (is-active $f) () (add-atom &self (active $f)))))
     (let* (($g1 (gate! $pA $dA $cA $tau $retain)) ($g2 (gate! $pB $dB $cB $tau $retain))
            ($g3 (gate! $pC $dC $cC $tau $retain)) ($g4 (gate! $pBA $dBA $cBA $tau $retain)))
       (gate! $pBC $dBC $cBC $tau $retain))))

;; 5-premise (abduction: A B C AB CB); sens_A = 0 ⇒ dem A is exactly 0
(= (gated-abd! $node $f $tau $retain)
   (let* (($q (factor-demand-abduction $node (car-atom (dem-cur $node))))
          ($pA  (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $a))
          ($pB  (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $b))
          ($pC  (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $c))
          ($pAB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $ab))
          ($pCB (match &self (factor $f abduction (premises $a $b $c $ab $cb) (conclusion $node)) $cb))
          ($dA (dn-1 $q)) ($dB (dn-2 $q)) ($dC (dn-3 $q)) ($dAB (dn-4 $q)) ($dCB (dn-5 $q))
          ($cA (dem-join! $pA $dA)) ($cB (dem-join! $pB $dB)) ($cC (dem-join! $pC $dC)) ($cAB (dem-join! $pAB $dAB)) ($cCB (dem-join! $pCB $dCB))
          ($af (if (is-active $f) () (add-atom &self (active $f)))))
     (let* (($g1 (gate! $pA $dA $cA $tau $retain)) ($g2 (gate! $pB $dB $cB $tau $retain))
            ($g3 (gate! $pC $dC $cC $tau $retain)) ($g4 (gate! $pAB $dAB $cAB $tau $retain)))
       (gate! $pCB $dCB $cCB $tau $retain))))

;; gate: activate the premise (DC#2 when $retain, else only if it meets $tau), dedup-guarded;
;; then recurse PAST it iff its demand INCREASED on this visit AND its demand ≥ $tau.
(= (gate! $u $du $changed $tau $retain)
   (let $m (if (is-active $u) ()
               (if (if $retain True (>= $du $tau)) (add-atom &self (active $u)) ()))
     (if (if $changed (>= $du $tau) False) (recurse-gated! $u $tau $retain) ())))

(= (recurse-gated! $node $tau $retain)
   (if (== (collapse (match &self (produces $node $f) $f)) ()) () (gated-propagate! $node $tau $retain)))
