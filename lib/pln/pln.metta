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
!(import! &self "../ecan/core_logic.metta")
!(import! &self "pln_core_logic.metta")
;; Node BASE RATES (BaseRateTv / EvidenceConfidence / BaseRateAdmits). Loaded LAST because it builds on
;; pln_core_logic's Truth_w2c and conditional-probability-consistency. Until now its only loader in the
;; tree was Julia (WorldModel/src/PLNCore.jl:41), so an agent doing `!(import! &self "pln.metta")` got
;; the PLN library WITHOUT the base-rate formulas — the library's own entry point disagreeing with what
;; the world model actually runs.
!(import! &self "base_rate.metta")
;; Belief confidence DYNAMICS (R10): the decay law + rate, and the re-validation confidence map.
!(import! &self "decay.metta")
