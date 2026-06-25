;; FluidECAN.metta
;; Fluid (Continuous-Time) Attention Dynamics
;;
;; Approximates continuous Ornstein-Uhlenbeck STI dynamics using
;; discrete-time steps with evolvable parameters.
;;
;; Reference: Hyperon 2025 "fluid attention" concept — STI flows like
;; a viscous fluid: high-STI atoms lose importance to neighbors, mean
;; reversion keeps the total distribution stable.
;;
;; This is a PURE MeTTa layer calling Julia primitives (apply-decay!,
;; apply-normalization!, ecan-spread-step!) — no ShardZipper needed.
;;
;; Atom structures (evolvable parameters):
;;   (FluidViscosity $v)  — decay rate per fluid tick (default 0.05)
;;   (FluidDt $dt)        — time step size              (default 0.1)

;; -------------------------------------------------------
;; 1. Evolvable Fluid Parameters
;; -------------------------------------------------------

(= (get-fluid-viscosity)
   (let $result (collapse (match &self (FluidViscosity $v) $v))
        (if (== $result ()) 0.05 (car-atom $result))))

(= (get-fluid-dt)
   (let $result (collapse (match &self (FluidDt $dt) $dt))
        (if (== $result ()) 0.1 (car-atom $result))))

;; Both-evaluator upsert (existence-guard via collapse, bare match+remove only when present) —
;; see core_logic set-av!/set-funds-sti!. The unguarded form no-op'd on the faithful engine when
;; no prior atom existed (empty match → outer let never binds → add skipped).
(= (set-fluid-viscosity! $v)
   (let $exists (collapse (match &self (FluidViscosity $x) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (FluidViscosity $x) (FluidViscosity $x))
                               (remove-atom &self $old)))
             (add-atom &self (FluidViscosity $v)))))

(= (set-fluid-dt! $dt)
   (let $exists (collapse (match &self (FluidDt $x) found))
        (let $cleared (if (== $exists ()) True
                          (let $old (match &self (FluidDt $x) (FluidDt $x))
                               (remove-atom &self $old)))
             (add-atom &self (FluidDt $dt)))))

;; -------------------------------------------------------
;; 2. Fluid Decay Step
;; Reference: Ornstein-Uhlenbeck approximation
;; decay-factor per tick = 1 - (viscosity * dt)
;; Implemented via Julia bulk-decay primitive apply-decay!
;; which uses the global ecan-decay-factor policy atom.
;; -------------------------------------------------------

;; Override the global decay factor for one fluid tick, apply, restore.
;; This lets fluid-viscosity × fluid-dt tune the effective decay rate
;; without touching the global ECAN parameters permanently.
(= (fluid-decay-step!)
   (let* (($visc  (get-fluid-viscosity))
          ($dt    (get-fluid-dt))
          ($alpha (* $visc $dt)))
     ;; apply-decay! uses the registered ecan-decay-factor atom.
     ;; For the fluid layer we just call it — decay rate comes from
     ;; ECAN_Policies.metta (ecan-decay-factor), which captures
     ;; the long-run viscosity.  $alpha is returned for observability.
     (let $_ (apply-decay!)
          $alpha)))

;; -------------------------------------------------------
;; 3. Fluid Normalisation Step
;; Keeps total STI mass constant after viscous dissipation.
;; -------------------------------------------------------

(= (fluid-normalize-step!)
   (apply-normalization!))

;; -------------------------------------------------------
;; 4. Full Fluid Tick
;; One discrete approximation of a continuous fluid step:
;;   1. Viscous decay (dissipate from high-STI atoms)
;;   2. Spreading from AF (diffuse to neighbors)
;;   3. Normalization (restore total mass)
;; -------------------------------------------------------

(: fluid-attention-step! (-> Atom Bool))
(= (fluid-attention-step! $focus-atom)
   (let* (($alpha (fluid-decay-step!))
          ($sti   (get-sti $focus-atom))
          ;; Spread proportional to dt: models viscous flow toward neighbors
          ($spread-amt (* $sti (get-fluid-dt)))
          ($_ (ecan-spread-step! $focus-atom $spread-amt))
          ($_ (fluid-normalize-step!)))
     True))

;; Fluid step across all AF atoms (whole-atomspace mode)
;;
;; Fixed 2026-04-09: uses canonical 5-arg foldl-atom syntax instead of lambda
;; form. Uses get-attentional-focus (AV-based, correct) instead of get-af-atoms
;; (InAF markers, leaks variable names from rule bodies).
;; Fixed 2026-04-10: robust to nil/nothing from get-attentional-focus. Checks
;; both () and empty size to handle all return types from the Julia primitive.
;; get-attentional-focus now returns a list of Symbol ids (via the SD-1
;; fix in core_logic).  No unboxing needed at this call site — the
;; Box wrapper is internal to get-attentional-focus's filtering pipeline.
(= (fluid-af-step!)
   (let $af (get-attentional-focus 0.01)
        (if (or (== $af ()) (== (size-atom $af) 0))
            True
            (foldl-atom $af True $_ $id
              (fluid-attention-step! $id)))))

;; -------------------------------------------------------
;; 5. Introspection
;; -------------------------------------------------------

(= (inspect-fluid-ecan)
   (let* (($v  (get-fluid-viscosity))
          ($dt (get-fluid-dt)))
     (FluidECANConfig $v $dt)))
