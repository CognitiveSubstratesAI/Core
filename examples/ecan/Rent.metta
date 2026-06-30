;;;; Rent.metta — Two-tier, deficit-scaled rent collection.
;;;;
;;;; Rent is GATED OFF when funds >= target, and ramps to 2*base as funds fall a full buffer below
;;;; target (the homeostat's COLLECT side — opposite numerator to the wage; see Convergence.metta).
;;;; STI and LTI funds gate independently. The tests reset funds to 0 before each tier so the deficit
;;;; rate sits at its 2*base ceiling (e.g. wa-sti rent = 2 * 0.01 = 0.02).
;;;;
;;;; Base rates:  wa-sti 0.01  wa-lti 0.005   af-sti 0.05  af-lti 0.02

!(import! &self (library ecan))

; Test 1: base rent rate parameters
!(assertEqual (wa-sti-rent-rate) 0.01)
!(assertEqual (wa-lti-rent-rate) 0.005)
!(assertEqual (af-sti-rent-rate) 0.05)
!(assertEqual (af-lti-rent-rate) 0.02)

; Test 2: rent is GATED OFF when funds >= target (pool full enough — wages drain the surplus instead)
!(set-funds-sti! 20000.0)
!(set-funds-lti! 20000.0)
!(add-atom &self (AV gate-probe 0.5 0.3 0.1))
!(collect-wa-rent! gate-probe)
!(assertEqual (get-sti gate-probe) 0.5)        ; STI rent off above target
!(assertEqual (get-lti gate-probe) 0.3)        ; LTI rent off above target

; Below target the deficit rate is at its 2*base ceiling (funds = 0).
; Test 3: collect-wa-rent! deducts 2*wa rates (STI 0.02, LTI 0.01)
!(set-funds-sti! 0.0)
!(set-funds-lti! 0.0)
!(add-atom &self (AV rent-probe 0.5 0.3 0.1))
!(collect-wa-rent! rent-probe)
!(assertEqual (get-sti rent-probe) 0.48)       ; 0.5 - 0.02
!(assertEqual (get-lti rent-probe) 0.29)       ; 0.3 - 0.01

; Test 4: VLTI is preserved by rent
!(assertEqual (get-vlti rent-probe) 0.1)

; Test 5: collect-af-rent! deducts the higher AF rates (STI 0.10, LTI 0.04)
!(set-funds-sti! 0.0)
!(set-funds-lti! 0.0)
!(add-atom &self (AV af-probe 0.5 0.3 0.1))
!(collect-af-rent! af-probe)
!(assertEqual (get-sti af-probe) 0.4)          ; 0.5 - 0.10
!(assertEqual (get-lti af-probe) 0.26)         ; 0.3 - 0.04

; Test 6: rent floors at 0 — atoms can't go negative (raw STI is economic-scale, no [0,1] ceiling)
!(set-funds-sti! 0.0)
!(set-funds-lti! 0.0)
!(add-atom &self (AV tiny-probe 0.005 0.001 0.0))
!(collect-wa-rent! tiny-probe)
!(assertEqual (get-sti tiny-probe) 0.0)        ; 0.005 - 0.02 → floored 0
!(assertEqual (get-lti tiny-probe) 0.0)        ; 0.001 - 0.01 → floored 0

!(println! "Rent.metta: all tests passed ✓")
