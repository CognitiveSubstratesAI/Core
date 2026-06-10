;;;; logical_probe.metta — logicalProbe / strategyProbe (port of metta-moses
;;;; representation/logical-probe.metta). Walk a list of candidate subtree permutations,
;;;; build an LSK/SSK for each (via logicalSubtreeKnob/strategySubtreeKnob), and collect
;;;; the knobs that should be kept (always if $addIfInExemplar, else only those not
;;;; already in the exemplar). Returns (knobs updatedTree).
;;;;
;;;; CORE-DIALECT: upstream's two clauses (base `()` perms + recursive `$perms`) OVERLAP
;;;; on perms=() — folded into one guarded clause (if (== $perms ())). Result tuples and
;;;; concatT accumulation are let*-bound.

(= (logicalProbe $exemplar (mkNodeId $targetId) $perms $addIfInExemplar $knobs)
   (if (== $perms ())
       ($knobs $exemplar)
       (let* ((($headPerms $tailPerms) (decons-atom $perms))
              (($updatedTree $lsk) (logicalSubtreeKnob $exemplar (mkNodeId $targetId) $headPerms))
              ($discKnob (getDiscKnob $lsk)))
         (if (or $addIfInExemplar (not (inExemplar $discKnob)))
             (let* (($updatedKnobs (concatT $knobs ($lsk))))
               (logicalProbe $updatedTree (mkNodeId $targetId) $tailPerms $addIfInExemplar $updatedKnobs))
             (logicalProbe $exemplar (mkNodeId $targetId) $tailPerms $addIfInExemplar $knobs)))))

(= (strategyProbe $exemplar (mkNodeId $targetId) $perms $addIfInExemplar $knobs)
   (if (== $perms ())
       ($knobs $exemplar)
       (let* ((($headPerms $tailPerms) (decons-atom $perms))
              (($updatedTree $ssk) (strategySubtreeKnob $exemplar (mkNodeId $targetId) $headPerms))
              ($discKnob (getDiscKnob $ssk)))
         (if (or $addIfInExemplar (not (inExemplar $discKnob)))
             (let* (($updatedKnobs (concatT $knobs ($ssk))))
               (strategyProbe $updatedTree (mkNodeId $targetId) $tailPerms $addIfInExemplar $updatedKnobs))
             (strategyProbe $exemplar (mkNodeId $targetId) $tailPerms $addIfInExemplar $knobs)))))
