; category.metta — SubRep categorical backbone: planning quantale + CDS⊣PDS adjunction (§8)
;
; Source: SubRep_spec.md §8 (planning category 𝒦_M; residuated quantale (𝒦,⊗,⋁,≤);
;   CDS⊣PDS adjunction Thm 8.8; weakest-sufficient via residuation). Options are
;   decision transformers T_o; the planner JOINS them (⋁ = per-state max) and COMPOSES
;   them (⊗ = sequencing); residuals give the weakest prefix/suffix.
;   Residuation reuses the planning-cost quantale `q-cost-resid` in lib/quantale.
; Depends on lib/subrep/cds.metta (vdot, cds-margin-box, cds-margin-vertices) + pds.metta (vlen).

; ── Planner join  B_G = ⋁_o T_o  : per-state max over options' backed-up values ──
(= (transformer-join $vals)
   (let* ( (($h $t) (decons-atom $vals)) )
     (if (== $t () ) $h (max $h (transformer-join $t)))))

; ── list helpers for extreme-ray construction ────────────────────────────────
(= (zeros $n) (if (== $n 0) () (let* ( ($r (zeros (- $n 1))) ) (cons-atom 0 $r))))
(= (nth $xs $i) (if (== $i 0) (car-atom $xs) (nth (cdr-atom $xs) (- $i 1))))
(= (set-at $xs $i $v)
   (if (== $i 0)
       (let* ( (($h $t) (decons-atom $xs)) ) (cons-atom $v $t))
       (let* ( (($h $t) (decons-atom $xs))
               ($r (set-at $t (- $i 1) $v)) )
         (cons-atom $h $r))))

; ── CDS ⊣ PDS adjunction (Thm 8.8): F : Cone → Cover (extreme rays) ──────────
; For a box cone [0, u] the extreme rays are the per-axis vertices u_i·e_i. The
; Galois connection F⊣G (extreme-rays ⊣ cone-hull) means CDS over the box equals
; CDS over its extreme rays: inf_{w∈box} wᵀΔn = min over the axis vertices. So an
; option CDS-admitted on the cone is admitted on the finite vertex cover, and back.
(= (cone-extreme-rays $u) (rays-acc $u 0 (vlen $u)))
(= (rays-acc $u $i $n)
   (if (== $i $n)
       ()
       (let* ( ($ray (set-at (zeros $n) $i (nth $u $i)))
               ($rest (rays-acc $u (+ $i 1) $n)) )
         (cons-atom $ray $rest))))

; CDS margin over a box cone, evaluated via its extreme rays (the adjunction's RHS).
; Equals (cds-margin-box Δr Δn ℓ=0 u) — the §8 statement that F preserves the CDS test.
(= (cds-margin-via-rays $dr $dn $u)
   (cds-margin-vertices $dr $dn (cone-extreme-rays $u)))
