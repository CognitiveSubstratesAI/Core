; cds.metta — SubRep Cone-Dominant Subtask (CDS) admission gate  (MVP-0)
;
; Source papers (specs, read-once):
;   docs/specs/Subrep/SubRep_spec.md
;       §1   the (r̂,n̂) expectation-model interface; backed-up value B_o = r̂ + wᵀn̂
;       §2.2 CDS: m_o(x) = inf_{w∈W} (B_o − B_base) ;  admit iff m_o ≥ ε
;       §2.4 / §11.11  box/cone support-function form (no LP): inf_{w∈[ℓ,u]} wᵀΔn
;       §2.2.5 / Lemma 7.3  robust margin with model error: m − ε_r − ‖W‖_{max,1}·ε_n
;       §11.17 MVP-0 = minimal CDS, box cone, no LP   ← this file
;   docs/research/papers/Subrep/SubRep-Minecraft-AIRIS_v2_2.pdf §3.2
;       simplex W = {w≥0, ‖w‖₁=1}, h_W(u)=max_i u_i ⟹  CDS:  Δr ≥ max_i(−Δn_i)
;       i.e.  m_o = Δr + min_i(Δn_i)
; Reference impl (Python, paper-faithful): ~/dev-zone/subrep/certification/cds_test.py
;
; The CDS gate certifies a candidate option `o` against the admitted baseline `B`:
; admit `o` only if it beats the baseline for EVERY motive weight in the slice W
; (uniform improvement). This is the option-admission stage of the §4 goal loop —
; the canonical version of WorldModel's hand-built affordance admission.
;
; Dialect: faithful Minimal — single if-guarded rules (NO overlapping structural
; heads, which would fork nondeterministically), let* + decons-atom for list walks,
; `()`-expressions as numeric vectors. Runs on the same evaluator as quantale/PLN.
;
; Vectors are ()-expressions of numbers, e.g. (0.30 0.0 -0.05). All vector ops
; assume equal lengths (a motive vector has one component per sub-aspect); vmin
; assumes a non-empty vector.

; ════════════════════════════════════════════════════════════════════════════
; Vector primitives
; ════════════════════════════════════════════════════════════════════════════

; vdot — inner product wᵀn of two equal-length numeric vectors.
(= (vdot $w $n)
   (if (== $w ())
       0
       (let* ( (($wh $wt) (decons-atom $w))
               (($nh $nt) (decons-atom $n)) )
         (+ (* $wh $nh) (vdot $wt $nt)))))

; vmin — minimum component of a non-empty numeric vector (= inf over the simplex).
(= (vmin $xs)
   (let* ( (($h $t) (decons-atom $xs)) )
     (if (== $t () ) $h (min $h (vmin $t)))))

; vsub — elementwise a − b (used for Δn = n̂_o − n̂_base). NB: cons-atom does NOT
; reduce its tail argument, so the recursive call is forced through a let* binding
; ($rest) before consing — otherwise the list is left un-recursed.
(= (vsub $a $b)
   (if (== $a ())
       ()
       (let* ( (($ah $at) (decons-atom $a))
               (($bh $bt) (decons-atom $b))
               ($rest (vsub $at $bt)) )
         (cons-atom (- $ah $bh) $rest))))

; box-inf — inf_{w∈[ℓ,u]} wᵀΔn over an axis-aligned box (the §11.11 no-LP support
; function). For each coordinate the infimum puts weight at ℓ_i when Δn_i≥0 and at
; u_i when Δn_i<0.
(= (box-inf $dn $lo $hi)
   (if (== $dn ())
       0
       (let* ( (($d $dt) (decons-atom $dn))
               (($l $lt) (decons-atom $lo))
               (($u $ut) (decons-atom $hi)) )
         (+ (if (>= $d 0) (* $l $d) (* $u $d))
            (box-inf $dt $lt $ut)))))

; ════════════════════════════════════════════════════════════════════════════
; Backed-up value and improvements   (§1)
; ════════════════════════════════════════════════════════════════════════════

; B_o(x;w) = r̂ + wᵀn̂ — the per-option AVI look-ahead target under motive weight w.
(= (backed-up $r $n $w) (+ $r (vdot $w $n)))

; Δr̂ = r̂_o − r̂_base ;  Δn̂ = n̂_o − n̂_base — improvement of option over baseline.
(= (delta-r $ro $rb) (- $ro $rb))
(= (delta-n $no $nb) (vsub $no $nb))

; ════════════════════════════════════════════════════════════════════════════
; CDS margins   (§2.2 / §3.2)
; ════════════════════════════════════════════════════════════════════════════

; Simplex cone W={w≥0,‖w‖₁=1}:  m_o = Δr + min_i(Δn_i)  (paper §3.2).
(= (cds-margin-simplex $dr $dn) (+ $dr (vmin $dn)))

; Box cone [ℓ,u]:  m_o = Δr + inf_{w∈[ℓ,u]} wᵀΔn  (§11.11 no-LP support function).
(= (cds-margin-box $dr $dn $lo $hi) (+ $dr (box-inf $dn $lo $hi)))

; Robust margin (§2.2.5): subtract model-error cushions. ‖W‖_{max,1}=k (k=1 on the
; simplex). m_rob = m − ε_r − k·ε_n  lower-bounds the true margin.
(= (cds-margin-robust $m $er $en $k) (- (- $m $er) (* $k $en)))

; ════════════════════════════════════════════════════════════════════════════
; Admission   (§2.2)
; ════════════════════════════════════════════════════════════════════════════

; admit iff margin ≥ ε (the §2.2 statewise/expectation gate).
(= (cds-admit $margin $eps) (>= $margin $eps))

; Convenience: admit option (r̂_o,n̂_o) over baseline (r̂_b,n̂_b) on the simplex.
(= (cds-admit-simplex $ro $no $rb $nb $eps)
   (cds-admit (cds-margin-simplex (delta-r $ro $rb) (delta-n $no $nb)) $eps))

; ════════════════════════════════════════════════════════════════════════════
; General cone via an explicit vertex set   (upstream weight_set.get_vertices_array)
; ════════════════════════════════════════════════════════════════════════════
; The worst-case motive over ANY polyhedral cone = min over its vertices of wᵀΔn
; (the §2.4 normalized-base support function, evaluated at the extreme rays). The
; simplex (vmin, unit-basis vertices) and box (box-inf) are special cases.
(= (wc-motive-vertices $verts $dn)
   (let* ( (($v $rest) (decons-atom $verts)) )
     (if (== $rest ())
         (vdot $v $dn)
         (min (vdot $v $dn) (wc-motive-vertices $rest $dn)))))

(= (cds-margin-vertices $dr $dn $verts) (+ $dr (wc-motive-vertices $verts $dn)))

; ════════════════════════════════════════════════════════════════════════════
; Auditable admission certificate   (§5.4 / upstream certificate_schema.py)
; ════════════════════════════════════════════════════════════════════════════
; (subrep-cert GATE Δr Δn margin ε admit) — the auditable record of an admission
; decision (GATE ∈ {CDS, PDS}; margin ≥ 0 ⟺ admit; ε = budget, 0 for CDS). A bare
; data constructor; callers add bookkeeping (skill-id, seed, timestamp) around it.
(= (cds-cert $dr $dn $eps)
   (let $m (cds-margin-simplex $dr $dn)
     (subrep-cert CDS $dr $dn $m $eps (cds-admit $m $eps))))
