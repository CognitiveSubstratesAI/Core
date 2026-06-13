;;;; scoring.metta — boolean program evaluation (port of metta-moses scoring/fitness.metta's
;;;; evaluate/evaluateAnd/evaluateOr). Evaluate a fully-instantiated boolean program (an
;;;; S-expression of AND/OR/NOT over True/False constants) to a single True/False. This is
;;;; the kernel a behavioral score is built on (M3-b: replaceVarsWithTruth + scoreTree).
;;;;
;;;; CORE-DIALECT: clean port — get-metatype/car-atom/cdr-atom/case/not all native. PeTTa-FAITHFUL
;;;; Bool: True/False are SYMBOLS (not Grounded, as in hyperon) — confirmed vs PeTTa lib_he/lib_pln and
;;;; the rest of this port (e.g. `(== True (isNullVertex …))`, `(case $tree (… True))`). So a boolean
;;;; LEAF is discriminated by "is it NOT an Expression" — an Expression recurses; anything else (a
;;;; True/False symbol) is returned as-is. (Upstream metta-moses checks `get-metatype … Grounded`
;;;; because hyperon grounds True/False; that idiom is wrong on the PeTTa-faithful evaluator.)

;; evaluate — reduce a constant boolean expression to True / False.
(= (evaluate $expr)
   (if (== (get-metatype $expr) Expression)
       (if (== (cdr-atom $expr) ())
           (evaluate (car-atom $expr))          ;; (True)/(False) wrapper → unwrap
           (case (car-atom $expr)
             ((AND (evaluateAnd (cdr-atom $expr)))
              (OR  (evaluateOr  (cdr-atom $expr)))
              (NOT (not (evaluate (cdr-atom $expr))))
              ($_  ERROR))))
       $expr))                                  ;; leaf: a True/False symbol (PeTTa-faithful Bool)

;; evaluateOr — True iff some argument is True.
(= (evaluateOr $args)
   (if (== $args ())
       False
       (let* (($first (car-atom $args))
              ($rest  (cdr-atom $args)))
         (if (== (evaluate $first) True) True (evaluateOr $rest)))))

;; evaluateAnd — False iff some argument is False.
(= (evaluateAnd $args)
   (if (== $args ())
       True
       (let* (($first (car-atom $args))
              ($rest  (cdr-atom $args)))
         (if (== (evaluate $first) False) False (evaluateAnd $rest)))))

;; ── program instantiation + per-row scoring (bscore.metta) ───────────────────
;; replaceVarWithTruth ($b $l) $expr — replace every occurrence of variable $l with
;; truth value $b throughout $expr.
(= (replaceVarWithTruth ($b $l) $boolExpr)
   (if (== (get-metatype $boolExpr) Expression)
       (let* ((($h $t) (decons-atom $boolExpr)))
         (if (== $t ())
             (replaceVarWithTruth ($b $l) $h)
             (let* (($t' (map-atom $t $ts (replaceVarWithTruth ($b $l) $ts))))
               (if (== $h $l) (cons-atom $b $t') (cons-atom $h $t')))))
       (if (== $boolExpr $l) $b
           (if (is-member $boolExpr (AND OR)) ($boolExpr) $boolExpr))))

;; replaceVarsWithTruth ($lList $expr) $bList — substitute each label by its truth value.
;; (List.zip→Core zip; List.foldl→foldl-atom with elem-first order to match
;; replaceVarWithTruth's (pair expr) signature.)
(= (replaceVarsWithTruth ($lList $boolExpr) $bList)
   (let $blList (zip $bList $lList)
     (foldl-atom $blList $boolExpr $acc $pair (replaceVarWithTruth $pair $acc))))

;; compareAndScore — 0 if equal (correct row), -1 otherwise. The per-row behavioral score.
(= (compareAndScore $a $b) (if (== $a $b) 0 -1))

;; scoreRow — instantiate $expr with the row's $inputs over $labels, evaluate, and score
;; against $expected (0 correct / -1 wrong).
(= (scoreRow $expr $labels $inputs $expected)
   (compareAndScore (evaluate (replaceVarsWithTruth ($labels $expr) $inputs)) $expected))

;; scoreProgram — total behavioral fitness of $expr over a truth table: $rows is a list of
;; ($inputs $expected) pairs. 0 = perfect; each wrong row contributes -1.
(= (scoreProgram $expr $labels $rows)
   (if (== $rows ())
       0
       (let* (($row (car-atom $rows))
              (($inputs $expected) $row))
         (+ (scoreRow $expr $labels $inputs $expected)
            (scoreProgram $expr $labels (cdr-atom $rows))))))
