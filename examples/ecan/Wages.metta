;;;; Wages.metta — Dynamic wage calculation
;;;;
;;;; wage = clamp((target - funds) / buffer, -1, 1) * base-wage
;;;;
;;;; funds below target → POSITIVE wage (atoms get paid, draining funds back to target)
;;;; funds above target → NEGATIVE wage (atoms taxed, refilling funds)
;;;;
;;;; Defaults from ECAN_Policies.metta:
;;;;   sti-funds-target = 10000.0
;;;;   sti-funds-buffer = 10000.0
;;;;   sti-atom-wage    = 10.0

!(import! &self (library ecan))

; Canonical wage = base * (1 + clamp((funds - target)/buffer, -1, 1)) → [0, 2*base], NON-negative.
; Higher funds → MORE wage (distribute the over-full pool); the funds homeostat runs through RENT.
; Test 1: funds == target → wage = base (ndiff=(10000-10000)/10000=0, wage = 10*(1+0) = 10)
!(set-funds-sti! 10000.0)
!(assertEqual (calculate-sti-wage) 10.0)

; Test 2: funds == 0 (bank empty) → wage = 0; the bank can't pay when broke
; ndiff=(0-10000)/10000=-1, wage = 10*(1 + -1) = 0.0  (the pool refills via RENT, never a negative wage)
!(set-funds-sti! 0.0)
!(assertEqual (calculate-sti-wage) 0.0)

; Test 3: funds well above target → wage capped at 2*base (push STI out of the over-full pool)
; funds=20000, ndiff=(20000-10000)/10000=1.0, wage = 10*(1+1) = 20.0
!(set-funds-sti! 20000.0)
!(assertEqual (calculate-sti-wage) 20.0)

; Test 4: funds at target+buffer → wage at the 2*base ceiling (same boundary as test 3)
!(set-funds-sti! 20000.0)
!(assertEqual (calculate-sti-wage) 20.0)

; Test 5: linear interpolation below target
; funds=5000, ndiff=(5000-10000)/10000=-0.5, wage = 10*(1-0.5) = 5.0
!(set-funds-sti! 5000.0)
!(assertEqual (calculate-sti-wage) 5.0)

; Test 6: LTI wage uses the same formula with LTI parameters
!(set-funds-lti! 5000.0)
!(assertEqual (calculate-lti-wage) 5.0)

!(println! "Wages.metta: all tests passed ✓")
