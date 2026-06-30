; anytime.metta — SubRep anytime three-tier gate + conformal certificates (§2.4, §2.3.7)
;
; Source: SubRep_spec.md §2.4 (three-tier anytime gate — cached rays → exact LP →
;   projected subgradient; most candidates stay in the cheap cached tier) + §2.3.7
;   (non-circular CONFORMAL certificates — distribution-free margin lower bound).
; Depends on cds.metta (cds-margin-vertices/box), pds.metta (vlen), category.metta (nth).

; ── §2.4 anytime gate: cheap cached-ray test; exact solve only when inconclusive ──
; A cached subset of rays gives an OVER-estimate of the true inf (fewer rays ⟹ larger
; min). So a cached margin already below −band guarantees the exact margin is negative
; → cheap decisive REJECT; otherwise the cheap test is inconclusive and we fall through
; to the exact box-cone solve. (Tier 3, projected subgradient, is a richer refinement.)
(= (anytime-margin $dr $dn $cached-rays $lo $hi $band)
   (let $mc (cds-margin-vertices $dr $dn $cached-rays)
     (if (< $mc (- 0 $band))
         $mc
         (cds-margin-box $dr $dn $lo $hi))))

; ── §2.3.7 conformal certificate: distribution-free margin lower bound ──────────
; ceil(x) via floor (stdlib has floor, not ceil).
(= (ceilNum $x) (let $f (floor $x) (if (> $x $f) (+ $f 1) $f)))

; q-quantile (nearest-rank) of a SORTED-ascending list: element at 1-based rank ceil(q·n).
(= (quantile $sorted $q)
   (let* ( ($n (vlen $sorted))
           ($r (ceilNum (* $q $n))) )
     (index-atom $sorted (- $r 1))))

; conformal margin: point margin − the (1−δ)-quantile of held-out CALIBRATION residuals
; (non-circular — residuals come from a separate calibration set, not the training data).
; m_conf ≥ 0  ⟹  Pr[ true margin ≥ 0 ] ≥ 1−δ  (distribution-free).
(= (conformal-margin $margin $calib-sorted $oneminusdelta)
   (- $margin (quantile $calib-sorted $oneminusdelta)))
