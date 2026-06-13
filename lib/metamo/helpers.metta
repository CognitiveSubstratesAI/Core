;;;; helpers.metta — numeric helpers. The icoglabs upstream implements these via
;;;; (py-call helpers.X) into Python/numpy; Core has no Python runtime, so they
;;;; are reimplemented in PURE MeTTa here (Core's math.metta provides exp / sqrt
;;;; / min / max / log). M1 ships the scalar helpers used by appraisal; vector
;;;; helpers (clipVector/scaleArray/parallelMerge/…) arrive with the decision +
;;;; dynamics layers.

;; e^x
(= (expNum $x) (exp $x))

;; logistic sigmoid 1/(1+e^-x)
(= (sigmoidNum $x) (/ 1.0 (+ 1.0 (exp (* -1.0 $x)))))

;; ── M2: scalar + vector helpers (pure MeTTa; upstream had these as py-call) ──

;; max(0, v)
(= (positivePart $v) (max 0.0 $v))

;; |v|
(= (absNumber $v) (abs $v))

;; (head tail) destructure pair — upstream `decons` (Core has decons-atom; this
;; form lets `let*` bind `(($h $t) (decons $l))`).
(= (decons $l) ((car-atom $l) (cdr-atom $l)))

;; elementwise clamp to [lo,hi]
(= (clipVector $arr $lo $hi) (map-atom $arr $x (clamp $x $lo $hi)))

;; elementwise scale
(= (scaleArray $arr $factor) (map-atom $arr $x (* $x $factor)))

;; mean of the elements of $arr at the positions listed in $indices
(= (meanAtIndices $arr $indices)
   (/ (foldl-atom $indices 0.0 $acc $i (+ $acc (index-atom $arr $i)))
      (size-atom $indices)))

;; ── M3: vector helpers for the bimonad / distance (pure MeTTa) ──

;; elementwise a+b (recursive; base case empty list)
(= (vectorAdd $a $b)
   (if (== $a ())
       ()
       (let* ((($ah $at) (decons $a)) (($bh $bt) (decons $b)) ($rest (vectorAdd $at $bt)))
         (cons-atom (+ $ah $bh) $rest))))

;; elementwise a-b
(= (listDifference $a $b)
   (if (== $a ())
       ()
       (let* ((($ah $at) (decons $a)) (($bh $bt) (decons $b)) ($rest (listDifference $at $bt)))
         (cons-atom (- $ah $bh) $rest))))

;; Euclidean norm: sqrt(Σ xᵢ²)
(= (norm $arr) (sqrt (foldl-atom $arr 0.0 $acc $x (+ $acc (* $x $x)))))

;; ── M4: dynamics helpers (pure MeTTa; index-conditional via member/min/max) ──

;; clip scalar to [lo,hi] (upstream npClip)
(= (npClip $v $lo $hi) (clamp $v $lo $hi))

;; (1-α)·a + α·b elementwise
(= (blendArrays $a $b $alpha)
   (vectorAdd (scaleArray $a (- 1.0 $alpha)) (scaleArray $b $alpha)))

;; set element at position $idx to $val
(= (setAtIndex $arr $idx $val) (_setAtIdx $arr 0 $idx $val))
(= (_setAtIdx $arr $pos $idx $val)
   (if (== $arr ())
       ()
       (let* ((($h $t) (decons $arr)) ($rest (_setAtIdx $t (+ $pos 1) $idx $val)))
         (cons-atom (if (== $pos $idx) $val $h) $rest))))

;; add $boost (capped at $maxVal) to elements whose position is in $indices
(= (boostAtIndices $arr $indices $boost $maxVal) (_boostAtIdx $arr 0 $indices $boost $maxVal))
(= (_boostAtIdx $arr $pos $indices $boost $maxVal)
   (if (== $arr ())
       ()
       (let* ((($h $t) (decons $arr))
              ($nh (if (member $pos $indices) (min $maxVal (+ $h $boost)) $h))
              ($rest (_boostAtIdx $t (+ $pos 1) $indices $boost $maxVal)))
         (cons-atom $nh $rest))))

;; project goals into the safe region R = { gInd ≥ θ ∧ ‖G‖ ≤ gMax }.
;;
;; NOTE — divergence from upstream (justified): the upstream floors gInd to θ and
;; THEN scales the whole vector by gMax/‖G‖, which drags gInd back below θ whenever
;; ‖G‖ > gMax — so the projected state can still be OUTSIDE R (a multi-tick
;; metamoGovern trajectory exposed this: state left R at tick 7). The correct
;; projection holds the floored weight FIXED and shrinks only the remaining
;; coordinates to the norm budget, so BOTH invariants hold exactly:
;;   gInd' = max(gInd, θ);   ‖G'‖ = min(‖G‖, gMax).
(= (projectGoalsToSafe $goals $weightIdx $thetaSafe $gMax)
   (let* (
     ($w (max (index-atom $goals $weightIdx) $thetaSafe))   ;; floored weight (gInd)
     ($g1 (setAtIndex $goals $weightIdx $w))
     ($n (norm $g1))
   )
     (if (<= $n $gMax)
         $g1
         ;; ‖G‖ too large: hold the weight, scale the rest so ‖G'‖ = gMax exactly.
         (let* (
           ($restBudget (sqrt (max 0.0 (- (* $gMax $gMax) (* $w $w)))))
           ($restNorm   (sqrt (max 0.0 (- (* $n $n)       (* $w $w)))))
           ($factor (if (> $restNorm 0.0) (/ $restBudget $restNorm) 0.0))
         )
           (setAtIndex (scaleArray $g1 $factor) $weightIdx $w)))))
