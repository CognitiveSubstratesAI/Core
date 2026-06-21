; waveformer.metta — Waveformer control plane: budget-weighted attention routing (§11)
;
; Source: SubRep_spec.md §11 (embed option/MDN/gate heads in a Waveformer; conservative
;   attention is the execution-time CONTROL PLANE). §11.5 budget-weighted attention:
;       α_ij = softmax_j( Q_iK_jᵀ/√d + log(a_j + ε) )
;   so the conservative-attention budget a_j (from lib/subrep/attention.metta) modulates
;   the transformer attention — negligible-budget items can't dominate (anti-spam, §11.14).
;   (The §11.16 MORK mapping — two-rate scheduler, versioned double buffers, device groups
;   — is operational and changes NONE of this math.)
; Depends on attention.metta (exp-scores, lsum, lscale).
;
; Identity used to avoid a `log` builtin:  softmax(logit_j + log(a_j+ε))
;   = exp(logit_j)·(a_j+ε) / Σ_k exp(logit_k)·(a_k+ε).

; elementwise multiply two equal-length lists.
(= (vmul $a $b)
   (if (== $a ())
       ()
       (let* ( (($ah $at) (decons-atom $a))
               (($bh $bt) (decons-atom $b))
               ($r (vmul $at $bt)) )
         (cons-atom (* $ah $bh) $r))))

; add a scalar to every element (used to floor budgets at ε).
(= (vadd-scalar $xs $c)
   (if (== $xs ())
       ()
       (let* ( (($h $t) (decons-atom $xs))
               ($r (vadd-scalar $t $c)) )
         (cons-atom (+ $h $c) $r))))

; budget-weighted attention over keys with logits `Q·Kᵀ/√d` and budgets a_j (§11.5):
;   α_j ∝ exp(logit_j)·(a_j+ε),  normalized to Σ_j α_j = 1.
(= (budget-weighted-attn $logits $budgets $eps)
   (let* ( ($e (exp-scores $logits 1.0))                 ; exp(logit_j)  (τ=1)
           ($w (vmul $e (vadd-scalar $budgets $eps)))    ; · (a_j + ε)
           ($z (lsum $w)) )
     (lscale $w (/ 1.0 $z))))
