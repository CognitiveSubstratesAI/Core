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
