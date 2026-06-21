; motive_cone.metta — consume the MDN's learned cone atom (the neurosymbolic boundary, §2.4)
;
; Source: SubRep_spec.md §2.4 (a Neural Space exposes its output AS ATOMS) + §5.9. The
;   FabricPC MDN (FabricPC examples/subrep_mdn.jl) emits exactly these atoms —
;   (motive-cone ID (lo …) (hi …)) — for each context; this is the Core/symbolic side
;   that CONSUMES them and screens options under the LEARNED cone. That closes the
;   end-to-end loop MDN → atom → gate across the atom interface, WITHOUT coupling Core
;   to FabricPC (the kernel stays clean; the atom is the only contract).
; Depends on cds.metta (cds-margin-box, cds-margin-simplex, cds-admit).

; store / look up the MDN's learned cone (the §2.4 Neural-Space→atom handoff).
(= (store-cone! $id $lo $hi) (add-atom &self (motive-cone $id $lo $hi)))
(= (lookup-cone $id)
   (let $r (collapse (match &self (motive-cone $id $lo $hi) ($lo $hi)))
     (car-atom $r)))

; Screen an option under a LEARNED cone: admit iff the box-cone margin ≥ −ε (a small ε
; absorbs the softplus support floor). This is the gate consuming the MDN's output.
(= (admit-under-cone $id $dr $dn $eps)
   (let* ( (($lo $hi) (lookup-cone $id)) )
     (cds-admit (cds-margin-box $dr $dn $lo $hi) (- 0 $eps))))
