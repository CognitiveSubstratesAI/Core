; pds.metta — SubRep Pareto-Dominant Subtask (PDS) admission gates  (MVP-1)
;
; Source papers (specs, read-once) + reference impl:
;   docs/specs/Subrep/SubRep_spec.md §2.3   — PDS cover form (componentwise + budgets)
;   docs/research/papers/Subrep/SubRep-Minecraft-AIRIS_v2_2.pdf §3.2 Def 2  — PDS-ε
;   ~/PRIMUS/dev-zone/subrep/certification/pds_test.py  — the iCog PDSGate (PDS-ε,
;       AdmissionGate.admit/get_admission_margin/get_gate_type; weight_set vertices)
;
; PDS is the WEAKER, more permissive admission rule. Where CDS demands uniform
; improvement over the whole cone, PDS admits complementary SPECIALIZED options —
; ones that win for some motive weights and lose (within budget) for others — which
; CDS would reject. Two forms, both from the paper:
;
;   (A) PDS-ε  (cone budget, §3.2 Def 2 / iCog pds_test.py):
;         admit iff  Δr + inf_{w∈W} wᵀΔn ≥ −ε      [= the CDS gate relaxed by ε]
;       It shares CDS's worst-case-motive infimum; only the threshold differs (−ε vs 0).
;
;   (B) PDS cover  (componentwise Pareto, §2.3):
;         over a finite cover {w^(k)}, gap Δ_k = B_o(w^(k)) − B_base(w^(k));
;         admit iff  Δ_k ≥ −ρ  ∀k   AND   |{k : Δ_k ≥ ε}| ≥ q·K
;       ρ = per-weight downside budget, ε = significance margin, q = coverage fraction.
;
; Depends on lib/subrep/cds.metta (vdot, backed-up, cds-margin-simplex, subrep-cert).
; Dialect: faithful Minimal — if-guarded recursion; cons-atom tails forced via let*.

; ════════════════════════════════════════════════════════════════════════════
; (A) PDS-ε — cone-budget relaxation of CDS   (§3.2 Def 2)
; ════════════════════════════════════════════════════════════════════════════
; margin = Δr + min_i Δn_i + ε  (≥ 0 ⟺ admit, matching iCog get_admission_margin).
(= (pds-eps-margin $dr $dn $eps) (+ (cds-margin-simplex $dr $dn) $eps))
(= (pds-eps-admit  $dr $dn $eps) (>= (cds-margin-simplex $dr $dn) (- 0 $eps)))
(= (pds-eps-cert   $dr $dn $eps)
   (subrep-cert PDS $dr $dn (pds-eps-margin $dr $dn $eps) $eps (pds-eps-admit $dr $dn $eps)))

; ════════════════════════════════════════════════════════════════════════════
; List reductions over the gap vector
; ════════════════════════════════════════════════════════════════════════════
; (+ reduces its recursive arg, so these need no let* forcing; cons-builders do.)
(= (vlen $xs)
   (if (== $xs ()) 0 (let* ( (($h $t) (decons-atom $xs)) ) (+ 1 (vlen $t)))))

(= (all-geq $xs $th)
   (if (== $xs ())
       True
       (let* ( (($h $t) (decons-atom $xs)) )
         (if (>= $h $th) (all-geq $t $th) False))))

(= (count-geq $xs $th)
   (if (== $xs ())
       0
       (let* ( (($h $t) (decons-atom $xs)) )
         (+ (if (>= $h $th) 1 0) (count-geq $t $th)))))

; ════════════════════════════════════════════════════════════════════════════
; (B) PDS cover — componentwise Pareto over a finite weight cover   (§2.3)
; ════════════════════════════════════════════════════════════════════════════
; gap vector Δ_k = B_o(w^(k)) − B_base(w^(k)) over a cover (list of weight vectors).
(= (pds-gaps $ro $no $rb $nb $cover)
   (if (== $cover ())
       ()
       (let* ( (($wk $rest-cov) (decons-atom $cover))
               ($gap (- (backed-up $ro $no $wk) (backed-up $rb $nb $wk)))
               ($rest (pds-gaps $ro $no $rb $nb $rest-cov)) )
         (cons-atom $gap $rest))))

; budgeted + coverage admission: all Δ_k ≥ −ρ  AND  |{k : Δ_k ≥ ε}| ≥ q·K.
(= (pds-cover-admit $ro $no $rb $nb $cover $eps $rho $q)
   (let* ( ($gaps (pds-gaps $ro $no $rb $nb $cover))
           ($k (vlen $cover)) )
     (if (all-geq $gaps (- 0 $rho))
         (>= (count-geq $gaps $eps) (* $q $k))
         False)))
