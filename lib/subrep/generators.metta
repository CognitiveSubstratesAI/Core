; generators.metta — cross-paradigm generators export (r̂,n̂), screened uniformly (§4)
;
; Source: SubRep_spec.md §4 (cross-paradigm integration). CDS/PDS only need (r̂,n̂) +
;   a motive set, so LOGIC generators (PLN backward-chaining macros) and EVOLUTIONARY
;   generators (MOSES programs) plug in as FIRST-CLASS generators, not bolt-ons — the
;   gate screens every paradigm by the same algebra. (Neural generators come via the
;   FabricPC MDN; AIRIS causal rules are the affordance generators, [[reference_airis…]].)
; Depends on cds.metta (cds-admit-simplex).
;
; A generator exports an expectation-model summary (r̂, n̂) — for a LOGIC macro from
; proof traces / abstract-interpretation bounds (§4.2.1); for an EVO program from
; instrumented rollouts / static analysis (§4.2.2). Here it is stored as the atom
; (generator ID KIND r̂ n̂); KIND is metadata only — the screening algebra is uniform.

(= (store-generator! $id $kind $rhat $nhat)
   (add-atom &self (generator $id $kind $rhat $nhat)))

; read back a generator's exported (r̂, n̂) summary.
(= (gen-summary $id)
   (let $r (collapse (match &self (generator $id $kind $rhat $nhat) ($rhat $nhat)))
     (car-atom $r)))

; Screen ANY generator by the same CDS gate (modality-neutral, §4): admit iff its
; (r̂,n̂) beats the baseline over the cone. Same rule for LOGIC, EVO, and neural.
(= (screen-generator $id $rb $nb $eps)
   (let* ( (($rhat $nhat) (gen-summary $id)) )
     (cds-admit-simplex $rhat $nhat $rb $nb $eps)))
