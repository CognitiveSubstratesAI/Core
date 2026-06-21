; easa.metta — Evo-Adhesive Smooth Atlas: fuzzy-guarded chart gluing, certified (§9)
;
; Source: SubRep_spec.md §9 (EASA — glue smooth neural/PC CHARTS (local contractive
;   patches) with LOGICAL GUARDS (case-split gluing) and EVOLUTIONARY mixtures, each
;   CDS/PDS-certified; approximate-EASA §9.4 = FUZZY softmax guards G_i^soft=softmax(s_i/τ),
;   blended output Σ G_i C_i). A complex goal is executed by an ATLAS of overlapping
;   charts; each chart is a local option with an (r̂,n̂) summary + a guard score. The atlas
;   blends them by fuzzy guards and the blend is screened by the SAME gate — so a
;   composition of CDS-certified charts stays certified (join-safety, §7.1, at the blend).
; Depends on cds.metta (cds-admit-simplex) + attention.metta (lscale).

; fuzzy guards for two charts = softmax of the guard scores (the §9.4 soft case-split).
(= (guard2 $s1 $s2 $tau)
   (let* ( ($e1 (exp (/ $s1 $tau)))
           ($e2 (exp (/ $s2 $tau)))
           ($z (+ $e1 $e2)) )
     ((/ $e1 $z) (/ $e2 $z))))

; elementwise vector add (for blending successor summaries n̂).
(= (vadd $a $b)
   (if (== $a ())
       ()
       (let* ( (($ah $at) (decons-atom $a))
               (($bh $bt) (decons-atom $b))
               ($r (vadd $at $bt)) )
         (cons-atom (+ $ah $bh) $r))))

; blend two charts' (r̂,n̂) by the fuzzy guards → the composite chart's (r̂,n̂):
;   r̂_blend = g1·r̂1 + g2·r̂2 ;  n̂_blend = g1·n̂1 + g2·n̂2  (Σ G_i C_i).
(= (easa-blend2 $g1 $g2 $r1 $n1 $r2 $n2)
   (let* ( ($rb (+ (* $g1 $r1) (* $g2 $r2)))
           ($nb (vadd (lscale $n1 $g1) (lscale $n2 $g2))) )
     ($rb $nb)))

; admit the GLUED atlas: blend the two charts, then screen the composite by CDS.
(= (easa-admit2 $g1 $g2 $r1 $n1 $r2 $n2 $rbase $nbase $eps)
   (let* ( (($rblend $nblend) (easa-blend2 $g1 $g2 $r1 $n1 $r2 $n2)) )
     (cds-admit-simplex $rblend $nblend $rbase $nbase $eps)))
