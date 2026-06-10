;;;; scoring.metta — boolean program evaluation (port of metta-moses scoring/fitness.metta's
;;;; evaluate/evaluateAnd/evaluateOr). Evaluate a fully-instantiated boolean program (an
;;;; S-expression of AND/OR/NOT over True/False constants) to a single True/False. This is
;;;; the kernel a behavioral score is built on (M3-b: replaceVarsWithTruth + scoreTree).
;;;;
;;;; CORE-DIALECT: clean port — get-metatype/car-atom/cdr-atom/case/not all native; in Core
;;;; get-metatype of True/False is Grounded, so the constant check holds.

;; evaluate — reduce a constant boolean expression to True / False.
(= (evaluate $expr)
   (if (== (get-metatype $expr) Grounded)
       $expr
       (if (== (cdr-atom $expr) ())
           (evaluate (car-atom $expr))          ;; (True)/(False) wrapper → unwrap
           (case (car-atom $expr)
             ((AND (evaluateAnd (cdr-atom $expr)))
              (OR  (evaluateOr  (cdr-atom $expr)))
              (NOT (not (evaluate (cdr-atom $expr))))
              ($_  ERROR))))))

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
