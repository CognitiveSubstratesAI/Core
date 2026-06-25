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

; Test 1: funds == target → wage is zero (clamp((10000-10000)/10000, -1, 1) * 10 = 0)
!(set-funds-sti! 10000.0)
!(assertEqual (calculate-sti-wage) 0.0)

; Test 2: funds well below target → wage is positive, capped at base-wage
; funds=0, ratio=(10000-0)/10000=1.0, clamp=1.0, wage = 1.0 * 10.0 = 10.0
!(set-funds-sti! 0.0)
!(assertEqual (calculate-sti-wage) 10.0)

; Test 3: funds well above target → wage is negative, capped at -base-wage
; funds=20000, ratio=(10000-20000)/10000=-1.0, clamp=-1.0, wage = -10.0
!(set-funds-sti! 20000.0)
!(assertEqual (calculate-sti-wage) -10.0)

; Test 4: funds exactly at target+buffer → wage = -base-wage
; funds=20000 (=target+buffer), ratio=-1.0, wage = -10.0 (same as test 3 boundary)
!(set-funds-sti! 20000.0)
!(assertEqual (calculate-sti-wage) -10.0)

; Test 5: linear interpolation in the middle range
; funds=5000, ratio=(10000-5000)/10000=0.5, wage = 0.5 * 10.0 = 5.0
!(set-funds-sti! 5000.0)
!(assertEqual (calculate-sti-wage) 5.0)

; Test 6: LTI wage uses the same formula with LTI parameters
!(set-funds-lti! 5000.0)
!(assertEqual (calculate-lti-wage) 5.0)

!(println! "Wages.metta: all tests passed ✓")
