; store.metta — SubRep atom-native certificate storage + zero-shot reuse  (Phase 4)
;
; Source: deep-dive whitepaper §5.9 ("every admitted option gets a certificate …
;   neurosymbolically native"), §2.4 (expose neural output AS ATOMS), §2.6 (state
;   as Atomspace patches); SubRep_spec.md §5.4 (certificate); iCog Quarter Plan
;   Obj 3 / Phase 4 (store certificates as native Atoms; retrieval queries select
;   certified skills by CURRENT motive weights; zero-shot reuse through motive
;   shifts WITHOUT retraining); ref ~/dev-zone/subrep/certification/metta_storage.py.
;
; The certificate-driven, auditable library is the SubRep backbone: certified
; skills live IN the space as atoms (not in an external store), so a motive shift
; is answered by RE-QUERYING the stored summaries under the new weights — zero-shot,
; no recertification. PRIMUS substrate-native (MORK/AtomSpace) — vs the iCog Python
; prototype's PyMeTTa bridge. Depends on lib/subrep/cds.metta (vdot).
;
; Dialect: faithful Minimal — add-atom/match/collapse over &self; if-guarded recursion.

; ════════════════════════════════════════════════════════════════════════════
; Store an admitted skill's expectation-improvement summary as an Atom
; ════════════════════════════════════════════════════════════════════════════
; (admitted-skill ID Δr Δn) — the auditable atom for a certified skill: its id and
; the (Δr, Δn) improvement over baseline that earned admission. Stored in &self so
; it is queryable by the same MeTTa the gates run in.
(= (store-admitted! $id $dr $dn)
   (add-atom &self (admitted-skill $id $dr $dn)))

; All certified skill ids currently in the library.
(= (admitted-ids)
   (collapse (match &self (admitted-skill $id $dr $dn) $id)))

; ════════════════════════════════════════════════════════════════════════════
; Zero-shot reuse: re-evaluate stored skills under the CURRENT motive weights
; ════════════════════════════════════════════════════════════════════════════
; A stored skill's backed-up improvement under motive weight w (zero-shot: just
; re-reads the stored (Δr, Δn) — no re-execution, no recertification).
(= (skill-value $dr $dn $w) (+ $dr (vdot $w $dn)))

; Look the skill up in the space by id and value it under the current weights w.
(= (skill-value-by-id $id $w)
   (let $vs (collapse (match &self (admitted-skill $id $dr $dn) (skill-value $dr $dn $w)))
     (car-atom $vs)))

; Retrieval by motive: ids of stored skills whose value under w clears a threshold
; (the §5.9 "select certified skills based on current motive weights"). A motive
; shift (new w) re-selects from the SAME atoms — zero-shot reuse.
(= (reuse-under-weight $w $thresh)
   (collapse (match &self (admitted-skill $id $dr $dn)
               (keep-if (>= (skill-value $dr $dn $w) $thresh) $id))))

; keep-if True ID → ID ; keep-if False ID → (no result, drops from the collapse).
(= (keep-if True  $x) $x)
(= (keep-if False $x) (superpose ()))
