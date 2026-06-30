;;;; Convergence.metta — the ECAN homeostat regulates the funds pool toward target.
;;;;
;;;; The wage (PAY side, calculate-sti-wage) and the deficit rent (COLLECT side, deficit-rent-rate)
;;;; have OPPOSITE numerators, so they push funds toward target from BOTH sides:
;;;;   funds HIGH (> target): wage high (up to 2*base), rent gated to 0    -> net DRAIN  -> funds fall
;;;;   funds LOW  (< target): wage low  (down to 0),    rent high (2*base)  -> net REFILL -> funds rise
;;;; (Only possible once raw STI is economic-scale — atoms can actually absorb/return the surplus.)

!(import! &self (library ecan))

; --- the opposite-numerator homeostat, exact rates ---
; Above target (funds = target + buffer): wage at its 2*base ceiling, rent gated OFF.
!(set-funds-sti! 20000.0)
!(assertEqual (calculate-sti-wage) 20.0)
!(assertEqual (deficit-rent-rate (wa-sti-rent-rate) (get-funds-sti) (sti-funds-target) (sti-funds-buffer)) 0.0)

; Below target (funds = 0): wage at 0, rent at its 2*base ceiling.
!(set-funds-sti! 0.0)
!(assertEqual (calculate-sti-wage) 0.0)
!(assertEqual (deficit-rent-rate (wa-sti-rent-rate) (get-funds-sti) (sti-funds-target) (sti-funds-buffer)) 0.02)

; --- the dynamics: each side moves funds TOWARD target ---
; Above target: stimulating a used atom pays a wage, draining the surplus pool downward.
!(add-atom &self (AV conv-a 5.0 0.0 0.0))
!(set-funds-sti! 20000.0)
!(stimulate! conv-a 1.0)
!(assertEqual (< (get-funds-sti) 20000.0) True)

; Below target: a rent tick collects STI back into the depleted pool, lifting it upward.
!(add-atom &self (AV conv-b 100.0 0.0 0.0))
!(set-funds-sti! 5000.0)
!(collect-wa-rent! conv-b)
!(assertEqual (< 5000.0 (get-funds-sti)) True)

!(println! "Convergence.metta: homeostat regulates funds toward target ✓")
