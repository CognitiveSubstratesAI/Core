;;;; optimization.metta — hill-climbing search (SIMPLIFIED port of metta-moses
;;;; optimization/hillclimbing/). Steepest-ascent over the instance (genotype) space:
;;;; from a starting Instance, generate single-knob-flip neighbors, score each, move to the
;;;; best while it improves. This is the CORE of MOSES optimization.
;;;;
;;;; 🔶 DELIBERATE SIMPLIFICATION (documented): upstream hillClimbing is a ~400-line
;;;; parameterized engine (crossover, neighborhood SAMPLING for large knob sets, distance
;;;; expansion, MI/strategy/complexity scorers). Those are SCALABILITY optimizations; the
;;;; algorithm they accelerate is exactly steepest-ascent-by-fitness, which this implements
;;;; exhaustively (every single-knob neighbor). Score function is passed BY NAME (works post
;;;; the bare-symbol eval fix). Uniform knob multiplicity $mult (settings 0..$mult-1).

;; nbrsAtPos — single-flip neighbors of $inst at position $i, over settings $vals (≠ current).
(= (nbrsAtPos $inst $i $vals)
   (if (== $vals ())
       ()
       (let* (($v   (car-atom $vals))
              ($cur (List.getByIdx $inst $i))
              ($rest (nbrsAtPos $inst $i (cdr-atom $vals))))
         (if (== $v $cur) $rest (cons-atom (List.replaceAt $inst $i $v) $rest)))))

;; nbrsFrom — accumulate single-flip neighbors across positions $i..$len-1.
(= (nbrsFrom $inst $mult $i $len)
   (if (== $i $len)
       ()
       (concatT (nbrsAtPos $inst $i (genList (- $mult 1)))
                (nbrsFrom $inst $mult (+ $i 1) $len))))

;; neighborsOf — all single-knob-flip neighbors of $inst (uniform multiplicity $mult).
(= (neighborsOf $inst $mult) (nbrsFrom $inst $mult 0 (List.length $inst)))

;; bestNeighbor — the highest-scoring instance among ($bestInst + $nbrs); ties keep the
;; incumbent (strict > to move).
(= (bestNeighbor $scoreFn $bestInst $bestScore $nbrs)
   (if (== $nbrs ())
       $bestInst
       (let* (($nbr (car-atom $nbrs))
              ($s   ($scoreFn $nbr)))
         (if (> $s $bestScore)
             (bestNeighbor $scoreFn $nbr $s (cdr-atom $nbrs))
             (bestNeighbor $scoreFn $bestInst $bestScore (cdr-atom $nbrs))))))

;; hillclimb — steepest ascent from $inst (uniform multiplicity $mult), up to $steps moves;
;; stops early at a local optimum. $scoreFn is a fitness function passed by name.
(= (hillclimb $scoreFn $inst $mult $steps)
   (if (== $steps 0)
       $inst
       (let* (($curScore ($scoreFn $inst))
              ($nbrs     (neighborsOf $inst $mult))
              ($best     (bestNeighbor $scoreFn $inst $curScore $nbrs)))
         (if (== $best $inst)
             $inst
             (hillclimb $scoreFn $best $mult (- $steps 1))))))
