;;;; MOSES.metta — MOSES library entry point (port of the iCog metta-moses MeTTaLog
;;;; reimplementation of asmoses / Looks' "Competent Program Evolution").
;;;; Upstream 1:1 reference: ~/JuliaAGI/dev-zone/metta-moses. Research-layer reference
;;;; (scalable MORK-native design): docs/research/papers/Mork/MOSES MORK.pdf.
;;;;
;;;; CORE-DIALECT ADAPTATIONS (vs upstream metta-moses):
;;;;   1. Functions are UNTYPED — drop upstream `(: fn (-> …))` signatures.
;;;;   2. LISTS = Core-native `()`-expressions via car-atom/cdr-atom/cons-atom, NOT the
;;;;      upstream `(Cons $h $t)` ADT (Core's `Nil` is already `(: Nil Expression)`).
;;;;      Recursion = single guarded clause + `if (== $xs ())` (per test_recursive_lists).
;;;;   3. No `py-call` — reimplement upstream Python helpers as Core MeTTa / grounded prims.
;;;;
;;;; Build status (incremental port — see docs/specs / the algorithm queue):
;;;;   M0  ✅ scaffold + Core-native list utilities
;;;;   M1a ✅ Instance (genotype value) + Pair
;;;;   M1b ✅ Map ADT + program-representation Tree/NodeId substrate
;;;;   M1c-1 ✅ MultiMap ADT + knob data-structure layer (knob-representation)
;;;;   M1c-2a ✅ logical-canonize (reduct-free exemplar canonicalization)
;;;;   M6-1 ✅ rte-helpers (reduce-to-elegance set-ops, filter-atom dialect adaptation)
;;;;   M6-2 ✅ normalization leaf rules: propagateNot + gatherJunctors + addAND
;;;;   M6-3a ✅ orCut constraint rule (cut-unnecessary-or)
;;;;   M6-3b ✅ andCut constraint rule (cut-unnecessary-and) + removeEmptyAND
;;;;   M6-3c ✅ promoteCommonConstraints (factor common child literals up)
;;;;   M6-3d ✅ subsumption: oneConstraintSubsume + zeroConstraintSubsume(')
;;;;   M6-3e ✅ oneCcSub (one-constraint-complement-subtraction) + invertLiterals
;;;;   M6-3f ✅ deleteInconsistentHandle (+ family) — ALL constraint rules done
;;;;   M6-4 ✅ reduce-to-elegance orchestrator + reduce-to (boolean ENF, WORKS)
;;;;   M6-5 ✅ cleanTree wired (tree.metta) — boolean-reduct engine COMPLETE
;;;;   M1c-2b ✅ lsk: logicalSubtreeKnob/strategySubtreeKnob + accessors (USES cleanTree)
;;;;   M1c-2b ✅ logical-probe: logicalProbe/strategyProbe (collect knobs over perms)
;;;;   M1c-2b ✅ sample-logical-perms (DETERMINISTIC enumerated selection, not RNG)
;;;;          [M1c-2b cont: addLogicalKnobs → buildLogical → build-knobs]
;;;;
;;;; Import:  !(import! &self (library MOSES))

!(import! &self "utilities.metta")
!(import! &self "instance.metta")
!(import! &self "map.metta")
!(import! &self "multimap.metta")
!(import! &self "tree.metta")
!(import! &self "knob.metta")
!(import! &self "logical_canonize.metta")
!(import! &self "rte_helpers.metta")
!(import! &self "propagate_not.metta")
!(import! &self "gather_junctors.metta")
!(import! &self "cut_unnecessary_or.metta")
!(import! &self "cut_unnecessary_and.metta")
!(import! &self "promote_common_constraints.metta")
!(import! &self "subsumption.metta")
!(import! &self "complement_subtraction.metta")
!(import! &self "delete_inconsistent_handle.metta")
!(import! &self "reduce_to_elegance.metta")
!(import! &self "lsk.metta")
!(import! &self "logical_probe.metta")
!(import! &self "sample_logical_perms.metta")
