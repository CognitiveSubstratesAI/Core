;;;; CoreExtensions.metta — Core MeTTa-rule stdlib extensions (the MeTTa-rule analog of CoreExtensions.jl).
;;;;
;;;; Generic helpers Core's libraries rely on that are NOT in hyperon's standard stdlib (so they don't
;;;; belong in the hyperon-faithful stdlib.metta) and are NOT grounded ops (so not CoreExtensions.jl).
;;;; Loaded as LIBRARY content alongside stdlib.metta (load_core_stdlib!), additive — the 234/234
;;;; conformance matrix must stay green with this loaded (the conformance scripts never call these).
;;;;
;;;; Provenance: ported from Core's legacy stdlib/list.metta, adapted to the standard idiom (`(== $list ())`
;;;; instead of legacy `is-empty`; primitives car-atom/cdr-atom/if/== are all in Minimal's stdlib).

;; member: is $x an element of $list? (recursion in return position — no cons-atom let-bind needed)
(= (member $x $list)
   (if (== $list ())
       False
       (if (== $x (car-atom $list))
           True
           (member $x (cdr-atom $list)))))

;; ── helpers the MOSES library calls (legacy stdlib/list.metta + core.metta), ported for Minimal.
;; The idiom-sweep (called−defined−provided over lib/MOSES/) found these four as MOSES's only
;; undefined helpers; transitive dep `is-empty` is inlined as `(== … ())` per this file's convention.

;; is-member: legacy alias over member (MOSES tree.metta / scoring.metta: `(is-member $r (AND OR))`)
(= (is-member $x $xs) (member $x $xs))

;; xor: boolean exclusive-or (MOSES propagate_not.metta)
(= (xor $a $b) (not (== $a $b)))

;; ~= / ===: PeTTa/MeTTaLog-compat (not hyperon-canonical), the rest of the is-member/xor compat group whose
;; "one canonical home" is this live file. `~=` (not-equal) is CALLED by MOSES cut_unnecessary_and/or and was
;; left only in the dead stdlib/core.metta — so it no-op'd on the LIVE path (ml()/mc_run); `===` completes the
;; trio. (`!=` can't be a rule — the parser tokenizes it as `! =` — so ports use `~=`.) The dead-stdlib copies
;; remain, matching the existing xor/is-member duplication; the dangling-ops lint missed `~=` (symbolic name).
(= (~=  $a $b) (not (== $a $b)))
(= (=== $a $b) (== $a $b))

;; length: element count (MOSES add_logical_knobs.metta). Recursion sits in `+`'s arg position; `+`
;; is a grounded op that evaluates its args, so the recursive call reduces — no let-bind needed.
(= (length $list)
   (if (== $list ())
       0
       (+ 1 (length (cdr-atom $list)))))

;; zip: pair up two lists elementwise (MOSES scoring.metta). cons-atom is a SPECIAL FORM that does NOT
;; reduce its tail arg, so the recursive `(zip …)` is let-bound to $rest first (the proven cons-atom-tail
;; idiom — same fix as MetaMo's vectorAdd/listDifference); a bare `(cons-atom … (zip …))` would leave the
;; tail unreduced.
(= (zip $xs $ys)
   (if (== $xs ())
       ()
       (if (== $ys ())
           ()
           (let $rest (zip (cdr-atom $xs) (cdr-atom $ys))
             (cons-atom (cons-atom (car-atom $xs) (cons-atom (car-atom $ys) ())) $rest)))))
