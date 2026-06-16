;; lib/pln/pln.metta — PLN library entry point.
;;
;; PLN: Probabilistic Logic Networks (Goertzel, Iklé, Wang).
;; Truth_* formulas (PLN book), |- inference rules, PLN.Derive engine.
;;
;; Adopted from packages/PRIMUS_Core/lib/pln/ (mature reference impl).
;; MOSES_PatternMiner.metta is intentionally NOT loaded here — it depends on
;; MOSES and will be wired in when packages/Core/lib/moses/ lands.

!(import! &self "stv.metta")
;; ECAN core — supplies get-sti/boost-sti! for PLN.Derive's attention-blended
;; PriorityRank (get-sti defaults to 0.0 with no AV → confidence-only until
;; attention is assigned). Closes the ECAN→PLN half of the cognitive-synergy loop.
!(import! &self "../ecan/t1_core_logic.metta")
!(import! &self "pln_core_logic.metta")
