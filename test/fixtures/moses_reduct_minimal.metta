;;;; moses_reduct_minimal.metta — reduct-engine assert fixture, run on the Minimal
;;;; evaluator via the warm MettaJam server:
;;;;   cd ~/code/CognitiveSubstratesAI/MettaJam && ./client.sh run-file \
;;;;     ../Core/test/fixtures/moses_reduct_minimal.metta
;;;; assertEqual returns () on PASS, (Error …) on mismatch; check "errors":[] in the JSON.
;;;;
;;;; Covers the reduct asserts that diverged Minimal-vs-legacy (MOSES_AUDIT_2026-06-16):
;;;; the dialect fixes are filtP (filter-atom function-predicate), concatT/decons let-bind,
;;;; and === → == (PeTTa-ism absent from the hyperon-faithful Minimal). M6-3d/e/f below are
;;;; GREEN; the M6-4 reduce-to block is correctness-pending + SLOW (interpretation overhead).

!(import! &self (library MOSES))

;; ── helpers / building blocks ────────────────────────────────────────────────
!(assertEqual (concatT (A) (B)) (A B))
!(assertEqual (gatherJunctors (AND A B)) (AND A B))
!(assertEqual (gatherJunctors (AND A (AND B C))) (AND A B C))
!(assertEqual (invertLiterals (A (NOT B))) ((NOT A) B))
!(assertEqual (invertLiterals (A B)) ((NOT A) (NOT B)))

;; ── M6-3d subsumption (one / zero constraint) ────────────────────────────────
!(assertEqual (oneConstraintSubsume (OR (AND E D) C) (AND E D) (C D)) ((OR C) () True))
!(assertEqual (oneConstraintSubsume (OR (AND E D) C) (AND E D) (X Y)) ((OR (AND E D) C) (AND E D) False))
!(assertEqual (nodeHasChildOrGuard (AND A)) True)
!(assertEqual (nodeHasChildOrGuard (AND)) False)
!(assertEqual (zeroConstraintSubsume (AND P (OR (AND A) (AND))) (OR (AND A) (AND))) ((AND P (OR (AND A))) (OR (AND A)) True))
!(assertEqual (zeroConstraintSubsume' (OR A C (AND) (OR A B)) (AND)) ((AND) (AND) True))

;; ── M6-3e oneCcSub / invertLiterals (complement subtraction) ──────────────────
!(assertEqual (oneCcSub (OR (AND D) (AND B C)) (AND B C) ((NOT B) C)) (OR (AND D) (AND C)))

;; ── andCut (uses == on nodes) ────────────────────────────────────────────────
!(assertEqual (andCut (AND A) (AND A)) ((AND A) (AND A) False))

;; ── M6-3f deleteInconsistentHandle (last constraint rule) ────────────────────
!(assertEqual (isConsistentExp (A B C (NOT A))) False)
!(assertEqual (deleteInconsistentHandle (OR B (AND (NOT A) (OR B C))) (AND (NOT A) (OR B C)) (A)) ((OR B) () True))
!(assertEqual (deleteInconsistentHandle (AND A (NOT A)) (AND A (NOT A)) ()) ((AND) () True))

;; ── M6-4 reduce-to (orchestrator) — CORRECTNESS-PENDING + SLOW on Minimal ─────
;; (uncomment to test once interpretation-overhead is addressed)
;; !(assertEqual (reduce-to (AND A B (NOT A))) (AND))
;; !(assertEqual (reduce-to (AND A B)) (AND A B))
;; !(assertEqual (reduce-to (AND (OR A B) (NOT A) (NOT B))) (AND (NOT A) (NOT B)))
;; !(assertEqual (reduce-to (AND (OR A B) (NOT A))) (AND (NOT A) B))
;; !(assertEqual (reduce-to (OR A (AND B C))) (AND (OR A (AND B C))))
;; !(assertEqual (reduce-to (AND (OR A B) A)) A)
