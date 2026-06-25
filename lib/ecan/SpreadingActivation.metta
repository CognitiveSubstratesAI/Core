;; SpreadingActivation.metta
;; ECAN Importance Diffusion — canonical algorithm
;; Reference: iCog-Labs metta-attention/attention/ImportanceDiffusionAgent/
;;
;; Algorithm (per canonical):
;;   1. Select source atom (stochastic from AF, or given goal)
;;   2. Compute incident probability vector  (equal weight per structural neighbor)
;;   3. Compute Hebbian probability vector   (weight = STV strength × confidence)
;;   4. Combine: hebbian-max-allocation-percentage to Hebbian, remainder to incident
;;   5. Trade STI: deduct from source, boost targets proportionally
;;   6. Hebbian learning: strengthen links for co-active pairs

;; -------------------------------------------------------
;; 0. Local Parameters (PRIMUS_Core did not define these explicitly —
;;    added here as defaults; overridable by user atoms.)
;; -------------------------------------------------------
(= (default-link-weight) 1.0)
(= (link-learning-rate) 0.1)

;; -------------------------------------------------------
;; 1. Link Structures
;; -------------------------------------------------------
;; Structural links: (Link $source $target)
;; Hebbian links:    (AsymHebbianLink $source $target $strength $confidence)

;; Atom-template results: wrap each match in a Box so that callers can
;; (a) count correctly with size-atom regardless of whether the inner
;; result is a Symbol or a compound atom, and (b) iterate over a true
;; list (Vector of Box atoms) without foldl-atom decomposing a compound
;; result by accident.  Box/unbox are defined in core_logic.metta (the
;; canonical SD-2 workaround for Core's collapse-with-atom-template ambiguity).
(= (get-hebbian-links $source)
   (collapse (match &self (AsymHebbianLink $source $target $s $c)
                    (Box (AsymHebbianLink $source $target $s $c)))))

(= (get-incident-neighbors $source)
   (collapse (match &self (Link $source $target) (Box $target))))

(= (get-link-weight $source $target)
   (let $result (collapse (match &self (WeightedLink $source $target $w) $w))
        (if (== $result ()) (default-link-weight) (car-atom $result))))

;; Core-interpreter workaround (drop collapse — atom-template single-match
;; case doesn't get wrapped, car-atom would decompose the atom).
;; Both-evaluator upsert (existence-guard + True return) — the unguarded bare-match no-op'd on the
;; faithful engine when no prior link existed (empty match → outer let never binds → add skipped).
(= (set-link-weight! $source $target $weight)
   (let $exists (collapse (match &self (WeightedLink $source $target $w) found))
        (let $_ (if (== $exists ()) True
                    (let $old (match &self (WeightedLink $source $target $w)
                                           (WeightedLink $source $target $w))
                         (remove-atom &self $old)))
             (let $a (add-atom &self (WeightedLink $source $target $weight)) True))))

;; -------------------------------------------------------
;; 2. STI Trade — canonical tradeSti()
;; Deduct from source, add to target. Zero-sum per transfer.
;; -------------------------------------------------------

(= (trade-sti! $source $target $amount)
   (let* (($src-sti (get-sti $source))
          ($tgt-sti (get-sti $target))
          ($actual  (clamp $amount 0.0 $src-sti))
          ($new-src (- $src-sti $actual))
          ($new-tgt (clamp (+ $tgt-sti $actual) 0.0 (max-attention-concentration))))
     (let $_ (set-sti! $source $new-src)
          (set-sti! $target $new-tgt))))

;; -------------------------------------------------------
;; 3. Incident Probability Vector
;; Reference: probabilityVectorIncident — equal weight per neighbor
;; -------------------------------------------------------

;; Conversions (Phase 1b):
;;   length              → size-atom (Core stdlib name)
;;   (lambda ($x) body)  → 3-arg map-atom:    (map-atom $list $x body)
;;   (lambda ($a $x) ..) → 5-arg foldl-atom:  (foldl-atom $list $init $a $x body)
;;   (let (CTOR $a $b) $val body) → let* with compound-pattern destructure
(= (incident-prob-vector $source)
   (let $neighbors (get-incident-neighbors $source)
        (if (== $neighbors ())
            ()
            (let $n (size-atom $neighbors)
                 (let $equal-weight (/ 1.0 $n)
                      (map-atom $neighbors $boxed
                        (let $t (unbox $boxed)
                          (ProbTarget $t $equal-weight))))))))

;; -------------------------------------------------------
;; 4. Hebbian Probability Vector
;; Reference: probabilityVectorHebbianAdjacent
;; weight = strength × confidence (from AsymHebbianLink STV)
;; -------------------------------------------------------

(= (hebbian-prob-vector $source)
   (let $links (get-hebbian-links $source)
        (if (== $links ())
            ()
            (let $weighted (map-atom $links $boxed
                             (let* (($link (unbox $boxed))
                                    ((AsymHebbianLink $src $tgt $s $c) $link)
                                    ($w (* $s $c)))
                               (ProbTarget $tgt $w)))
                 (normalise-prob-vector $weighted)))))

(= (sum-prob-weights $pvec)
   (foldl-atom $pvec 0.0 $acc $pt
     (let* (((ProbTarget $t $w) $pt))
       (+ $acc $w))))

(= (normalise-prob-vector $pvec)
   (let $total (sum-prob-weights $pvec)
        (if (< $total 0.000001)
            $pvec
            (map-atom $pvec $pt
              (let* (((ProbTarget $t $w) $pt))
                (ProbTarget $t (/ $w $total)))))))

;; -------------------------------------------------------
;; 5. Combine Incident + Hebbian Vectors
;; Reference: combineIncidentAdjacentVectors
;; hebbian-max-allocation-percentage goes to Hebbian targets,
;; remainder distributed across incident targets.
;; -------------------------------------------------------

(= (combine-prob-vectors $incident $hebbian)
   (let* (($hebb-alloc (hebbian-max-allocation-percentage))
          ($inc-alloc  (- 1.0 $hebb-alloc))
          ($scaled-hebb (map-atom $hebbian $pt
                          (let* (((ProbTarget $t $w) $pt))
                            (ProbTarget $t (* $w $hebb-alloc)))))
          ($scaled-inc  (map-atom $incident $pt
                          (let* (((ProbTarget $t $w) $pt))
                            (ProbTarget $t (* $w $inc-alloc))))))
     (if (== $hebbian ())
         $incident
         (if (== $incident ())
             $hebbian
             (let $combined (collapse (superpose ($scaled-hebb $scaled-inc)))
                  (normalise-prob-vector $combined))))))

;; -------------------------------------------------------
;; 6. Diffuse Atom — full canonical diffuseAtom()
;; -------------------------------------------------------

(= (diffuse-atom! $source $total-amount)
   (let* (($inc-vec   (incident-prob-vector $source))
          ($hebb-vec  (hebbian-prob-vector $source))
          ($combined  (combine-prob-vectors $inc-vec $hebb-vec)))
     (if (== $combined ())
         True
         (foldl-atom $combined True $_ $pt
           (let* (((ProbTarget $target $weight) $pt))
             (trade-sti! $source $target (* $weight $total-amount)))))))

;; -------------------------------------------------------
;; 7. Main Spread Step — called from governance-step!
;; Two modes:
;;   AF mode  — stochastic source from InAF atoms (canonical WAImportanceDiffusionAgent)
;;   Goal mode — directed from given goal atom
;; -------------------------------------------------------

;; Amount to spread = source STI × max-spread-percentage
(= (ecan-spread-step! $goal $amount)
   (let* (($source-sti (get-sti $goal))
          ($threshold  (spreading-threshold)))
     (if (< $source-sti $threshold)
         True
         (diffuse-atom! $goal $amount))))

;; Stochastic AF diffusion (whole-atomspace mode)
;; Selects a random atom from AF as source each tick.
(= (wa-diffusion-step!)
   (let $source (get-random-atom-in-af)
        (if (== $source ())
            True
            (let $amount (* (get-sti $source) (max-spread-percentage))
                 (diffuse-atom! $source $amount)))))

;; -------------------------------------------------------
;; 8. Multi-Hop Spreading
;; -------------------------------------------------------

(= (multi-hop-spread! $source $depth)
   (if (<= $depth 0)
       True
       (let $source-sti (get-sti $source)
            (if (< $source-sti (spreading-threshold))
                True
                (let $amount (* $source-sti (spreading-decay-factor))
                     (let $_ (diffuse-atom! $source $amount)
                          (let $neighbors (get-incident-neighbors $source)
                               (foldl-atom $neighbors True $_ $boxed
                                 (multi-hop-spread! (unbox $boxed) (- $depth 1))))))))))

;; Spread from all AF atoms (attention focus mode)
(= (spread-from-focus! $depth)
   (let $af (get-af-atoms)
        (if (== $af ())
            True
            (foldl-atom $af True $_ $id
              (multi-hop-spread! $id $depth)))))

;; -------------------------------------------------------
;; 9. Hebbian Link Management
;; Reference: HebbianCreationAgent + HebbianUpdatingAgent
;; -------------------------------------------------------

;; Hebbian conjunction formula (from HebbianUpdatingAgent):
;;   conj    = (ni × nj) + (nj - ni) × |nj - ni|      ∈ [-1, 1]
;;   ret     = (conj + 1) / 2                          ∈ [0, 1]
;; The raw conj is a signed correlation (-1 = strong anti-correlation, +1 = strong
;; co-activation). We map it AFFINELY to [0,1] — the canonical upstream form — so
;; anti-correlation is preserved in order rather than collapsed. (It previously
;; used clamp(conj,0,1), which floored every conj ≤ 0 to 0, conflating "independent"
;; with "anti-correlated" and discarding the lower half of the signal.)
(= (hebbian-conjunction $norm-i $norm-j)
   (let* (($product  (* $norm-i $norm-j))
          ($diff     (- $norm-j $norm-i))
          ($abs-diff (if (< $diff 0.0) (* -1.0 $diff) $diff))
          ($conj     (+ $product (* $diff $abs-diff))))
     (/ (+ $conj 1.0) 2.0)))

;; Update Hebbian link weight between two co-active atoms. A bare `(match …)` returns EMPTY (not ())
;; on the faithful engine → bound in the let* it collapsed the whole rule, so the create-branch NEVER
;; fired (Hebbian links were never created — the bug the migration missed). collapse the existence
;; check; car-atom the singleton for the update; both paths return True.
(= (hebbian-update! $source $target)
   (let* (($ni (get-normalised-sti $source))
          ($nj (get-normalised-sti $target))
          ($conj (hebbian-conjunction $ni $nj))
          ($olds (collapse (match &self (AsymHebbianLink $source $target $s $c)
                                        (AsymHebbianLink $source $target $s $c)))))
     (if (== $olds ())
         (let $a (add-atom &self (AsymHebbianLink $source $target $conj 0.5)) True)
         (let* (($old (car-atom $olds))
                ((AsymHebbianLink $src $tgt $old-s $old-c) $old)
                ($new-s (clamp (+ $old-s (* (link-learning-rate) (- $conj $old-s)))
                               0.0 1.0))
                ($_ (remove-atom &self $old)))
           (let $a (add-atom &self (AsymHebbianLink $source $target $new-s $old-c)) True)))))

;; Create Hebbian link if atoms are both in AF and link doesn't exist
(= (maybe-create-hebbian-link! $source $target)
   (if (== $source $target)
       True
       (let $exists (collapse (match &self
                                (AsymHebbianLink $source $target $s $c) True))
            (if (== $exists ())
                (add-atom &self (AsymHebbianLink $source $target 0.1 0.5))
                True))))

;; Run one Hebbian learning cycle across all AF atom pairs.
;; Nested lambdas → nested 5-arg foldl-atoms.
(= (hebbian-learning-cycle!)
   (let $af (get-af-atoms)
        (foldl-atom $af True $_ $src
          (foldl-atom $af True $__ $tgt
            (if (== $src $tgt) True
                (let $_ (hebbian-update! $src $tgt)
                     (maybe-create-hebbian-link! $src $tgt)))))))
