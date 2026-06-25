;; ============================================================
;; AttentionPolicies.metta — Governance Loop & Policies (Phase 1b)
;; ============================================================
;; Adopted from packages/PRIMUS_Core/lib/ecan/AttentionPolicies.metta —
;; only the canonical sections; PRIMUS-specific scaffolding stripped.
;;
;; INCLUDED  (canonical ECAN, upstream iCog-Labs metta-attention parity):
;;   §1 Optimal Transport       — spread-attention!, spread-proportional!
;;   §3 Autonomous Governance   — collect-all-*-rent!, governance-step!, heartbeat!
;;
;; SKIPPED   (deps on PRIMUS infrastructure not present in packages/Core):
;;
;;   ─── FEATURE-deferred (absent, will be noticed if invoked) ───────────
;;   §2 Geodesic Action Selection  (select-geodesic-action!)
;;   §5 Cognitive Resonance        (get-wm-goals, inject-goal!)
;;
;;   ─── SAFETY-deferred (silently absent — must be reinstated before any
;;       multi-agent/operator-trust use case) ────────────────────────────
;;   §4 Stable Cognitive Cycle     (verify-goal-preservation, is-aligned?)
;;     — would halt heartbeat! on goal-drift; without it, heartbeat runs
;;       through goal corruption with no warning.
;;   §5 has-capability? guards     (privilege checks on resonance/cleanup)
;;     — without these, every caller has implicit OPERATOR/ADMIN authority.
;;   §6 Ontological Guardrails     (goal-cleanup! with ADMIN gate)
;;     — without this, Core goals can be cleaned up by any caller.
;;   §7 Trust Negotiation & Exchange (validate-delegation, promote-atom!)
;;     — cross-agent atom acceptance without trust verification.
;;
;;   The safety-deferred items are NOT bugs in current Core (no multi-agent
;;   surface yet), but reinstating them is a precondition for any future
;;   work that exposes ECAN to untrusted callers or multi-worker sync.
;;
;; Conversions vs PRIMUS_Core source: lambda → 5-arg foldl-atom syntax.
;; Stub: (attention-evolution-step!) → Balanced; overridden by
;;       hyperseed/adaptive_attention.metta when Phase 1c lands.
;; ============================================================

;; -------------------------------------------------------
;; 0. Forward stub — overridden by hyperseed/adaptive_attention (Phase 1c).
;;
;; Returns an obvious-sentinel value (NOT one of the real classifier's
;; outputs Collapsed/Balanced/Diffuse) so that a downstream caller seeing
;; `EvolutionStubUnloaded` knows Phase 1c didn't actually wire up — rather
;; than seeing `Balanced` (a plausible-looking healthy state) and assuming
;; the self-evolution loop is running fine.
;; -------------------------------------------------------
(= (attention-evolution-step!) EvolutionStubUnloaded)

;; -------------------------------------------------------
;; 1. Optimal Transport
;; -------------------------------------------------------

;; Policy: Standard Spreading (Fixed Amount)
(: spread-attention! (-> Atom Bool))
(= (spread-attention! $node)
   (ecan-spread-step! $node 10.0))

;; Policy: Proportional Spreading (based on STI)
;; NB: second arg is Number, not Float — Core types every numeric literal (Int or
;; Float) as `Number`, so a `Float` annotation rejects a literal like 0.1 with
;; (BadArgType … Float Number). Matches the heartbeat! convention below.
(: spread-proportional! (-> Atom Number Bool))
(= (spread-proportional! $node $percent)
   (let $current-sti (get-sti $node)
        (ecan-spread-step! $node (* $current-sti $percent))))

;; -------------------------------------------------------
;; 3. Autonomous Governance Loop
;; -------------------------------------------------------

;; Two-tier rent collection across the atomspace.
;; lambda → 5-arg foldl-atom.
(= (collect-all-wa-rent!)
   (let $all-atoms (get-all-av-atoms)
        (if (== (size-atom $all-atoms) 0)
            True
            (foldl-atom $all-atoms True $_ $id
              (collect-wa-rent! $id)))))

(= (collect-all-af-rent!)
   (let $af-atoms (get-af-atoms)
        (if (== (size-atom $af-atoms) 0)
            True
            (foldl-atom $af-atoms True $_ $id
              (collect-af-rent! $id)))))

;; The canonical cognitive heartbeat tick.
;;   1. Two-tier rent collection (WA across all atoms; AF additionally on AF members)
;;   2. Bulk decay + normalization
;;   3. Tick counter increment + AF priority update for the goal
;;   4. Self-evolution (Phase 1c — currently a no-op stub returning Balanced)
;;   5. Spread from goal
(: governance-step! (-> Atom Bool))
(= (governance-step! $goal)
   (let $_ (collect-all-wa-rent!)
        (let $_ (collect-all-af-rent!)
             (let $_ (apply-decay!)
                  (let $_ (apply-normalization!)
                       (let $_ (increment-ecan-tick!)
                            (let $_ (update-af! $goal (get-sti $goal))
                                 (let $evo-state (attention-evolution-step!)
                                      (ecan-spread-step! $goal 10.0)))))))))

;; Recursive Heartbeat (Limited Depth for Safety)
(: heartbeat! (-> Atom Number Bool))
(= (heartbeat! $goal $depth)
   (if (<= $depth 0)
       True
       (let $dummy (governance-step! $goal)
            (heartbeat! $goal (- $depth 1)))))

;; -------------------------------------------------------
;; 4. Stable Cycle parameters (kept as evolvable atoms — the
;;    `stable-heartbeat!` policy that uses them needs goal-tracking
;;    infrastructure and was skipped from this port.)
;; -------------------------------------------------------
(= (attention-entropy-threshold) 1.5)
(= (stability-threshold) 0.8)
