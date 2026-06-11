;;;; metapopulation.metta — the MOSES metapopulation: a score-ranked pool of candidate
;;;; programs (exemplars) that seeds future deme expansions. Port of metta-moses
;;;; metapopulation/{exemplar-type,exemplar-selection}.metta + deme/merge-demes.metta,
;;;; reduced to the algorithmic core.
;;;;
;;;; 🔶 DELIBERATE SIMPLIFICATIONS (documented — same stance as M4 hillclimb / sampleLogicalPerms):
;;;;   1. Exemplar = (mkXmplr $tree $score) with a SINGLE behavioral fitness, replacing
;;;;      upstream's (mkXmplr tree demeId CompositeScore BehavioralScore) — no complexity
;;;;      penalty, uniformity penalty, or mutual-information CompositeScore, no BScore vector.
;;;;   2. selectExemplar = DETERMINISTIC best (head of the score-DESC pool). Upstream does a
;;;;      Boltzmann-weighted ROULETTE (py-call random) over penalized scores. Deterministic
;;;;      selection is reproducible + py-call-free, but limits diversification (see run_moses).
;;;;   3. The pool is a score-DESC-sorted native list (upstream OrderedSet OS).
;;;;   4. mergeXmplr = dedup-by-program + sorted insert + flat top-N trim. Upstream mergeDemes
;;;;      additionally dominance-filters BehavioralScores and trims by a complexity-temperature
;;;;      score range (resizeMetapop / getBetterCandidates / cullAtRandom).

;; ── Exemplar accessors (mkXmplr is a bare constructor — stays as data) ────────
(= (getXmplrTree  (mkXmplr $tree $score)) $tree)
(= (getXmplrScore (mkXmplr $tree $score)) $score)

;; xmplrProg — the program (preOrder of the tree); the dedup key for the pool.
(= (xmplrProg $x) (preOrder (getXmplrTree $x)))

;; seedXmplr — make an exemplar from a program tree, scoring it against the truth table.
(= (seedXmplr $tree $labels $table)
   (mkXmplr $tree (scoreProgram (preOrder $tree) $labels $table)))

;; seedPool — a singleton metapopulation from one exemplar tree. Built with cons-atom so the
;; exemplar is EVALUATED into the list (a bare ((seedXmplr …)) list literal would not reduce
;; its element — Core evaluates neither a non-symbol list head nor list elements).
(= (seedPool $tree $labels $table)
   (cons-atom (seedXmplr $tree $labels $table) ()))

;; selectExemplar — pick the best exemplar (head of the score-DESC pool). SIMPLIFIED:
;; upstream rouletteSelect samples a Boltzmann distribution over penalized scores.
(= (selectExemplar $pool) (car-atom $pool))

;; poolHasProg — is a program already represented in the pool? (dedup guard)
(= (poolHasProg $pool $prog)
   (if (== $pool ())
       False
       (if (== (xmplrProg (car-atom $pool)) $prog)
           True
           (poolHasProg (cdr-atom $pool) $prog))))

;; insertXmplr — insert $x into a score-DESC-sorted pool (incumbents win ties).
(= (insertXmplr $x $pool)
   (if (== $pool ())
       (cons-atom $x ())
       (if (> (getXmplrScore $x) (getXmplrScore (car-atom $pool)))
           (cons-atom $x $pool)
           (cons-atom (car-atom $pool) (insertXmplr $x (cdr-atom $pool))))))

;; trimTo — keep the first $n (the top-$n of a sorted pool). SIMPLIFIED from upstream
;; resizeMetapop (score-range keep + capCoef cap + random cull) to a flat top-N.
(= (trimTo $n $pool)
   (if (== $n 0)
       ()
       (if (== $pool ())
           ()
           (cons-atom (car-atom $pool) (trimTo (- $n 1) (cdr-atom $pool))))))

;; mergeXmplr — add $x to the pool unless its program is already present, keeping the pool
;; sorted and trimmed to $cap. The dedup-by-program + top-N essence of upstream mergeDemes.
(= (mergeXmplr $pool $x $cap)
   (if (poolHasProg $pool (xmplrProg $x))
       $pool
       (trimTo $cap (insertXmplr $x $pool))))
