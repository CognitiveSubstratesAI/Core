;; lib/ecan/ecan.metta — ECAN (Economic Attention Network) library entry point.
;;
;; ECAN: Goertzel/Hart attention allocation — STI (Short-Term Importance) and
;; LTI (Long-Term Importance) per atom, with rent/wage economic dynamics.
;;
;; Upstream:  https://github.com/iCog-Labs-Dev/metta-attention.git
;; Via:       packages/PRIMUS_Core/lib/ecan/ (mature multi-file impl,
;;            +semantic spreading +multi-objective importance +cross-system).
;;
;; ── Phase 0 (this load) ─────────────────────────────────────────────────────
;;   ECAN_Policies   — economic parameters (funds, wages, rent rates)
;;   core_logic      — AV accessors, rent collection, wage stimulation
;;
;; This is the foundation: enables get-sti, set-sti!, boost-sti!, AV storage,
;; and the economic primitives.  Sufficient to override PLN's ECAN stubs so
;; PLN.Derive's priority blend stops being confidence-only.
;;
;; ── Pending (Phase 1) ───────────────────────────────────────────────────────
;;   state_logic, FluidECAN, AttentionPolicies, SpreadingActivation,
;;   ResonancePolicies, hyperseed/adaptive_attention.metta
;;   → adds governance-step!, heartbeat!, spreading kernel, self-evolution.
;;
;; ── Pending (Phase 2) ───────────────────────────────────────────────────────
;;   t2_ECAN_WILLIAM_Integration, t2_ImportanceOptimization
;;   → cross-system attention + adaptive STI/LTI updates.
;;
;; Julia primitives `decimate-importance!` and `normalize-attention!` are
;; Phase 1 scope (used only by governance-step!).  Not needed for Phase 0.

!(import! &self "ECAN_Policies.metta")
!(import! &self "core_logic.metta")
!(import! &self "state_logic.metta")    ;; Phase 1a — AF membership, tick counter, scan gate
!(import! &self "SpreadingActivation.metta")   ;; Phase 1b — spreading kernel, Hebbian links
!(import! &self "AttentionPolicies.metta")     ;; Phase 1b — governance-step!, heartbeat!
!(import! &self "FluidECAN.metta")             ;; Phase 1c — continuous-time fluid dynamics
!(import! &self "Forgetting.metta")            ;; Phase 1c — memory reclamation (LTI threshold + Hebbian protection)
!(import! &self "../hyperseed/adaptive_attention.metta")  ;; Phase 1c — entropy classifier + self-evolution
