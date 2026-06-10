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
;;;;          [M6: leaf rules → constraint rules → reduce-to-elegance orchestrator → reduce-to]
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
