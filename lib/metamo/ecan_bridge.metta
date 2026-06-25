;;;; ecan_bridge.metta — ILLUSTRATIVE coupling of ECAN attention signals to a
;;;; MetaMo OpenPsi stimulus, plus `metamoGovern` as a candidate governance step.
;;;;
;;;; STANDALONE DEMO — this file deliberately does NOT modify the live
;;;; `governance-step!` heartbeat (lib/ecan/AttentionPolicies.metta). It proves
;;;; the stimulus→step→(next-state) plumbing in isolation so the coupling can be
;;;; validated before being promoted into the heartbeat's Phase-4 self-evolution
;;;; slot (currently a no-op stub).
;;;;
;;;; Load order (not auto-imported by metamo.metta — both libs are independent):
;;;;   !(import! &self (library metamo))
;;;;   !(import! &self (library ecan))
;;;;   !(import! &self "<…>/lib/metamo/ecan_bridge.metta")
;;;;
;;;; ⚠ The signal→stimulus calibration below is PLAUSIBLE-BUT-ILLUSTRATIVE, not a
;;;; validated cognitive model. The four OpenPsi stimulus channels are
;;;; (novelty conduciveness risk effort); the ECAN→channel mapping is the thing a
;;;; future increment should tune against real heartbeat dynamics.

;; af-size normalizer — focus sizes at/above this read as "fully novel/active".
(= (STIMULUS_AF_SCALE) 20.0)

;; Build an OpenPsi stimulus from the current ECAN state for a given goal:
;;   novelty       ← attentional-focus occupancy  (more atoms competing = novel)
;;   conduciveness ← goal salience                (high goal STI = conducive)
;;   risk          ← focus sparsity               (little active focus = risky)
;;   effort        ← inverse goal salience        (low STI = costly to pursue)
(= (ecanStimulus $goal)
   (let* (
     ($af (af-size))
     ($sti (get-sti $goal))
     ($occupancy (clamp (/ $af (STIMULUS_AF_SCALE)) 0.0 1.0))
     ($salience (sigmoidNum $sti))
     ($sparsity (clamp (- 1.0 $occupancy) 0.0 1.0))
     ($cost (clamp (- 1.0 $salience) 0.0 1.0))
   )
     (stimulus ($occupancy $salience $sparsity $cost))))

;; One motivational governance tick: derive the stimulus from ECAN, then run the
;; fully-stabilized MetaMo step (Ψ→𝔻→damp→apply→caution→project) on the supplied
;; motivation state + action candidates. Result = (transitionResult action safeState),
;; with safeState guaranteed inside the safe region R.
(= (ecanMotivationStep $state $goal $candidates)
   (metamoGovern $state (ecanStimulus $goal) $candidates))
