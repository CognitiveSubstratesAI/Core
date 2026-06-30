;;;; CoreAV.metta — Attention Value storage and accessors
;;;; Tests: (AV $id $sti $lti $vlti), get-sti, get-lti, get-vlti, set-*, boost-sti!
;;;;
;;;; Test 1 is the BUG PROBE for the collapse-match-in-rule-body issue
;;;; documented in PRIMUS_Core's core_logic.metta — if Core's interpreter
;;;; has the same bug, (get-sti seeded-atom) returns 0.0 instead of the seeded
;;;; value, despite the find-first-number workaround.  If it returns 0.5,
;;;; Core's interpreter doesn't have the bug and the workaround is dead code.

!(import! &self (library ecan))

;; Seed a known AV atom — this is the bug probe fixture
!(add-atom &self (AV ecan-probe 0.5 0.3 0.1))

; Test 1: BUG PROBE — get-sti must return the seeded value, not 0.0 fallback.
; If this fails with 0.0, Core inherits the collapse-match-in-rule-body bug.
!(assertEqual (get-sti ecan-probe) 0.5)

; Test 2: get-lti on the same probe
!(assertEqual (get-lti ecan-probe) 0.3)

; Test 3: get-vlti on the same probe (PRIMUS_Core comments said this one
; "works" while get-sti/get-lti failed.  Verify in Core too.)
!(assertEqual (get-vlti ecan-probe) 0.1)

; Test 4: nonexistent atom → 0.0 default (find-first-number fallback)
!(assertEqual (get-sti nonexistent-atom-xyz) 0.0)

; Test 5: get-av returns the full tuple
!(assertEqual (get-av ecan-probe) (AV ecan-probe 0.5 0.3 0.1))

; Test 6: set-sti! mutates only STI, preserves LTI and VLTI
!(set-sti! ecan-probe 0.2)
!(assertEqual (get-sti ecan-probe) 0.2)
!(assertEqual (get-lti ecan-probe) 0.3)
!(assertEqual (get-vlti ecan-probe) 0.1)

; Test 7: set-lti! preserves STI and VLTI
!(set-lti! ecan-probe 0.8)
!(assertEqual (get-sti ecan-probe) 0.2)
!(assertEqual (get-lti ecan-probe) 0.8)

; Test 8: boost-sti! adds raw STI on the economic scale (no fixed concentration cap)
; ecan-probe STI was 0.2 (Test 7) → +1.0 → 1.2 (the old 0.3 clamp was a scale bug)
!(boost-sti! ecan-probe 1.0)
!(assertEqual (get-sti ecan-probe) 1.2)

; Test 9: clamp utility
!(assertEqual (clamp 0.5 0.0 1.0) 0.5)
!(assertEqual (clamp 1.5 0.0 1.0) 1.0)
!(assertEqual (clamp -0.3 0.0 1.0) 0.0)

!(println! "CoreAV.metta: all tests passed ✓")
