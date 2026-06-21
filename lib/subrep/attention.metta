; attention.metta — SubRep conservative attention (runtime compute allocation)  (§10)
;
; Source: SubRep_spec.md §10 (conservative attention = a single-stage CONSERVED
;   attention pool driven by CDS/PDS margins — a streamlined PRIMUS RFS); deep-dive
;   whitepaper §10. Admission decides WHICH options are eligible; conservative
;   attention decides which RUN, and how hard, under a finite compute budget.
;
; Allocate a fixed budget A_total across admitted options in proportion to their
; margins, with STRICT conservation (no credit leaks / attention spam / hallucination):
;
;   a(o) = A_total · softmax_o(m_o/τ) = A_total · exp(m_o/τ) / Σ_o' exp(m_o'/τ)
;   ⟹  Σ_o a(o) = A_total   (the §10 conservation law)
;
; Minimal slice: the conserved softmax allocation. The full §10 rule adds decay
; (γ·a_prev) + A_free redistribution + per-cost priority — richer slices.
; Dialect: faithful Minimal — if-guarded recursion; cons-atom tails forced via let*.

; exp(m/τ) for each margin in the list (the un-normalized softmax scores).
(= (exp-scores $margins $tau)
   (if (== $margins ())
       ()
       (let* ( (($m $rest) (decons-atom $margins))
               ($r (exp-scores $rest $tau)) )
         (cons-atom (exp (/ $m $tau)) $r))))

; sum of a numeric list.
(= (lsum $xs)
   (if (== $xs ()) 0 (let* ( (($h $t) (decons-atom $xs)) ) (+ $h (lsum $t)))))

; scale every element by k.
(= (lscale $xs $k)
   (if (== $xs ())
       ()
       (let* ( (($h $t) (decons-atom $xs))
               ($r (lscale $t $k)) )
         (cons-atom (* $h $k) $r))))

; conserved attention allocation over a list of option margins: a(o)=A_total·softmax.
(= (attention-alloc $margins $a-total $tau)
   (let* ( ($scores (exp-scores $margins $tau))
           ($z (lsum $scores)) )
     (lscale $scores (/ $a-total $z))))

; |x − target| < tol — float-tolerant equality (max-based; for conservation asserts).
(= (within $x $target $tol) (< (max (- $x $target) (- $target $x)) $tol))
