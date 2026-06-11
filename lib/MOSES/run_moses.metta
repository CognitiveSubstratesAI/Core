;;;; run_moses.metta — the MOSES metapopulation loop (port of metta-moses
;;;; deme/expand-deme.metta's expandDeme + runMoses). This ties the whole stack together:
;;;; select an exemplar → build a representation (knob space) around it → hill-climb the knobs
;;;; → fold the best candidate back into the metapopulation → repeat until a perfect program
;;;; emerges or the generation budget runs out. THIS IS THE FULL MOSES SEARCH.
;;;;
;;;; 🔶 DELIBERATE SIMPLIFICATIONS (documented):
;;;;   1. One deme per expansion (n_demes = 1, as in upstream moses_params when feature
;;;;      selection is off). No game-strategy / feature-selection / mutual-information variants.
;;;;   2. Boolean behavioral scorer only (scoreProgram over a truth table).
;;;;   3. Optimizer = hillclimbC (simplified steepest ascent, see optimization.metta).
;;;;   4. Drops upstream runMoses bookkeeping (nEval, maxCandOutput, complexityTemperature,
;;;;      capCoef, genCount); termination = $maxGen budget OR best score ≥ $maxScore.
;;;;   ⚠️ With DETERMINISTIC selectExemplar (metapopulation.metta), the loop always re-seeds
;;;;      from the single best exemplar. When the target lies within one deme's knob space
;;;;      (e.g. OR from a leaf), one expansion suffices. A target needing structural growth
;;;;      across demes would exercise the re-selection path but could stagnate without the
;;;;      upstream roulette diversification — a known consequence of simplification #2 in
;;;;      metapopulation.metta.

;; boolDemeScore — fitness of an instance within a deme: decode the instance through the
;; representation, then score the resulting program against the truth table. Context-threaded
;; ($ctx = ($rep $labels $table)) so it can drive hillclimbC.
(= (boolDemeScore ($rep $labels $table) $inst)
   (scoreProgram (preOrder (getCandidate $rep (mkInst $inst))) $labels $table))

;; expandDeme — one MOSES expansion. Select the best exemplar, build a representation around
;; its tree, hill-climb the knob space from the default instance, and return the best
;; candidate as a new scored exemplar.
(= (expandDeme $pool $labels $table $mult $steps)
   (let* (($x     (selectExemplar $pool))
          ($tree  (getXmplrTree $x))
          ($rep   (representation $tree $labels))
          ((mkInst $init) (repInitialInstance $rep))
          ($best  (hillclimbC boolDemeScore ($rep $labels $table) $init $mult $steps))
          ($cand  (getCandidate $rep (mkInst $best)))
          ($score (scoreProgram (preOrder $cand) $labels $table)))
     (mkXmplr $cand $score)))

;; runMoses — the metapopulation loop. Up to $maxGen expansions; stop early when the best
;; exemplar reaches $maxScore (0 = perfect for the 0/-1 behavioral score). Returns the best
;; exemplar found.
(= (runMoses $maxGen $maxScore $cap $labels $table $mult $steps $pool)
   (if (== $maxGen 0)
       (selectExemplar $pool)
       (let* (($new      (expandDeme $pool $labels $table $mult $steps))
              ($pool2    (mergeXmplr $pool $new $cap))
              ($top      (selectExemplar $pool2))
              ($topScore (getXmplrScore $top)))
         (if (>= $topScore $maxScore)
             $top
             (runMoses (- $maxGen 1) $maxScore $cap $labels $table $mult $steps $pool2)))))
