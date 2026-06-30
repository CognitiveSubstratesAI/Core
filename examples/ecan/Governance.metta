;;;; Governance.metta — Full cognitive heartbeat (Phase 1b)
;;;; Surface: spread-attention!, spread-proportional!, collect-all-*-rent!,
;;;;          governance-step!, heartbeat!

!(import! &self (library ecan))

;; ── Test 1: spread-attention! delegates to ecan-spread-step! ──────────
;; Below-threshold STI → no-op (returns True, source unchanged).
!(add-atom &self (AV g1 0.05 0.0 0.0))
!(assertEqual (spread-attention! g1) True)
!(assertEqual (get-sti g1) 0.05)

;; ── Test 2: spread-proportional! spreads $percent × current STI ──────
!(add-atom &self (AV g2 0.5 0.0 0.0))
!(add-atom &self (AV n2 0.0 0.0 0.0))
!(add-atom &self (Link g2 n2))
!(spread-proportional! g2 0.1)
;; Spreading happened (g2 STI decreased); n2 gained some STI.
!(let $s (get-sti g2)
  (assertEqual (< $s 0.5) True))

;; ── Test 3: collect-all-wa-rent! charges deficit-scaled WA rent to every AV atom ─────
;; Funds at 0 (< target) so the deficit rate is active (rent gates OFF at funds >= target). The bulk
;; tick refills funds as it goes (conserving set-av!), so per-atom rates drift slightly — the EXACT
;; 2*base rate is pinned in Rent.metta (single atom, no drift); here we confirm every atom is charged.
!(set-funds-sti! 0.0)
!(add-atom &self (AV r1 0.5 0.3 0.0))
!(add-atom &self (AV r2 0.4 0.2 0.0))
!(add-atom &self (AV r3 0.3 0.1 0.0))
!(collect-all-wa-rent!)
!(assertEqual (< (get-sti r1) 0.5) True)
!(assertEqual (< (get-sti r2) 0.4) True)
!(assertEqual (< (get-sti r3) 0.3) True)

;; ── Test 4: attention-evolution-step! returns a real classifier state ──
;; Phase 1c's adaptive_attention.metta overrides the Phase 1b stub.  If the
;; override failed, this would still return EvolutionStubUnloaded — the
;; sentinel value the real classifier will never emit.
!(let $s (attention-evolution-step!)
  (assertEqual (== $s EvolutionStubUnloaded) False))

;; ── Test 5: governance-step! advances tick counter and applies decay ─
;; Snapshot ECAN tick before.
!(add-atom &self (AV gv 0.5 0.3 0.0))
!(let $tick-before (get-ecan-tick)
  (let $_ (governance-step! gv)
    (let $tick-after (get-ecan-tick)
      (assertEqual (- $tick-after $tick-before) 1))))

;; ── Test 6: heartbeat! depth=0 is a no-op (returns True) ─────────────
!(assertEqual (heartbeat! gv 0) True)

;; ── Test 7: heartbeat! depth=3 advances tick by exactly 3 ────────────
!(add-atom &self (AV hb 0.5 0.3 0.0))
!(let $tick-before (get-ecan-tick)
  (let $_ (heartbeat! hb 3)
    (let $tick-after (get-ecan-tick)
      (assertEqual (- $tick-after $tick-before) 3))))

;; ── Test 8: Phase-1b parameters are reachable ─────────────────────────
!(assertEqual (attention-entropy-threshold) 1.5)
!(assertEqual (stability-threshold) 0.8)

!(println! "Governance.metta: all tests passed ✓")
