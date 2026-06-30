;;;; Stimulate.metta — Full stimulate! cycle (wages paid, funds drained)
;;;;
;;;; (stimulate! $id $factor):
;;;;   sti-wage = calculate-sti-wage   (depends on current funds vs target)
;;;;   lti-wage = calculate-lti-wage
;;;;   new-sti  = cur-sti + (sti-wage * factor)
;;;;   new-lti  = cur-lti + (lti-wage * factor)
;;;;   funds-sti -= sti-wage * factor
;;;;   funds-lti -= lti-wage * factor
;;;;
;;;; This is the canonical "atom is used in reasoning → pay it wages" hook.

!(import! &self (library ecan))

; Setup: funds AT target → the canonical wage = base = 10 (a normal payment).
; wage = base*(1 + clamp((funds-target)/buffer,-1,1)) = 10*(1+0) = 10.0 at funds=target.
!(set-funds-sti! 10000.0)
!(set-funds-lti! 10000.0)

!(add-atom &self (AV stim-probe 0.1 0.05 0.0))

; Sanity: pre-stimulate values
!(assertEqual (get-sti stim-probe) 0.1)
!(assertEqual (get-lti stim-probe) 0.05)
!(assertEqual (calculate-sti-wage) 10.0)
!(assertEqual (calculate-lti-wage) 10.0)

; Test 1: stimulate with factor=1.0
; new-sti = 0.1 + (10.0 * 1.0) = 10.1
; new-lti = 0.05 + (10.0 * 1.0) = 10.05
!(stimulate! stim-probe 1.0)
!(assertEqual (get-sti stim-probe) 10.1)
!(assertEqual (get-lti stim-probe) 10.05)

; Test 2: funds drained by the wage paid — via set-av!'s conserving accounting (no manual debit).
; funds-sti = 10000 - (10.0 * 1.0) = 9990.0   (total STI conserved: atom +10, pool -10; never negative)
; funds-lti = 10000 - (10.0 * 1.0) = 9990.0
!(assertEqual (get-funds-sti) 9990.0)
!(assertEqual (get-funds-lti) 9990.0)

; Test 3: VLTI is preserved across stimulate!
!(assertEqual (get-vlti stim-probe) 0.0)

; Test 4: smaller factor → smaller wage payout
!(add-atom &self (AV stim-probe-2 0.0 0.0 0.0))
!(set-funds-sti! 10000.0)
!(set-funds-lti! 10000.0)
!(stimulate! stim-probe-2 0.1)
; new-sti = 0.0 + (10.0 * 0.1) = 1.0
!(assertEqual (get-sti stim-probe-2) 1.0)
!(assertEqual (get-lti stim-probe-2) 1.0)

!(println! "Stimulate.metta: all tests passed ✓")
