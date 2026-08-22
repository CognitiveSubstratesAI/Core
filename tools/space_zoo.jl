# space_zoo.jl — CREATE one of every registered Space kind, exercise it, and print the capability ledger.
#
# Run it:   Core/tools/space_zoo.sh
#
# WHAT THIS IS FOR. Three questions kept being answered from memory instead of from the substrate:
# "what kinds of Space can we make?", "which ones share storage?", and "which ones can MeTTa actually
# run against?". This script answers all three by DOING it — every space below is constructed for real,
# written to, and queried, and what prints is what happened.
#
# ⚠️ READ THE LEDGER, NOT THE COUNT. TWO kinds, on THREE axes — kind (what backs the payload) vs
# ACCESS MODE (who sees/writes it) vs INTEGRATION MODE (where execution lives). "Shared" is a mode, not
# a kind; a "fork" is a seeded Private region, not a kind. Only `:vector` can be evaluated against; only
# `:mork` persists; only `:mork` at Shared co-resides with siblings. The whitepaper (§2.2.1) promises "MeTTa code is substantially Space-independent" — the
# ledger printed at the end is the honest measurement of how far that is true here, and it is meant to
# be read as a gap list.

using MeTTaCore
const MC = MeTTaCore
const EV = MeTTaCore.Eval
const SM = MeTTaCore.StandardMeTTa

hdr(s) = (println(); println("═"^96); println("  ", s); println("═"^96))
step(s) = println("  · ", s)
# `core_atoms` returns Vector{SExprConvertible}, whose element type prints as a five-way Union that is
# wider than the atoms it contains — noise that obscures the very thing each line is demonstrating.
# Render the s-expressions instead of the container.
sx(a) = a isa AbstractVector ? "(" * join(sx.(a), " ") * ")" : string(a)
atoms(sp) = isempty(MC.core_atoms(sp)) ? "(none)" : join(sx.(MC.core_atoms(sp)), " ")

hdr(
    "1. :vector — the interpreter's store. The ONLY kind MeTTa can currently reduce against."
)
vs = MC.make_space(:vector)
step("make_space(:vector) → $(typeof(vs))")
EV.load_metta!(vs, raw"(= (twice $x) (+ $x $x))")
EV.load_metta!(vs, "(belief a 0.9 0.8)\n(belief b 0.1 0.2)")
step("evaluate  !(twice 21)                        → $(EV.load_metta!(vs, "!(twice 21)"))")
step(
    "bind      !(match &self (belief \$k \$s \$c) \$k) → $(EV.load_metta!(vs, raw"!(match &self (belief $k $s $c) $k)"))"
)
step("↑ the variable's WITNESS comes back. No MORK-backed kind below can do this yet.")

hdr("2. :vector; parent = … — a FORK is a seeded PRIVATE region, not a kind of its own.")
fk = MC.make_space(:vector; parent=vs)
EV.load_metta!(fk, "(only-in-the-fork)")
step(
    "parent sees the fork's new atom?  $(!isempty(EV.load_metta!(vs, "!(match &self (only-in-the-fork) yes)")))  ← must be false"
)
step(
    "fork sees it?                     $(!isempty(EV.load_metta!(fk, "!(match &self (only-in-the-fork) yes)")))  ← must be true"
)
step(
    "fork still has the parent's snapshot? $(!isempty(EV.load_metta!(fk, "!(match &self (belief a 0.9 0.8) yes)")))"
)

hdr("3. :mork at Private — an ISOLATED MORK atomspace. Its own trie, root prefix.")
m1 = MC.make_space(:mork)
m2 = MC.make_space(:mork)
MC.core_add!(m1, [:only_in_m1, 1])
step("make_space(:mork) → $(typeof(m1))")
step(
    "two :mork spaces share a trie?  $(m1.inner === m2.inner)  ← must be false (isolated by construction)"
)
step("m1 atoms: $(atoms(m1))   m2 atoms: $(atoms(m2))")
step("...but MeTTa cannot RUN here — this is compile-arrow 6:")
try
    MC.load_metta!(m1, "!(+ 1 2)")
    step(
        "  ⚠️ UNEXPECTED: the directive was accepted. The ledger is now STALE — update :mork's caps."
    )
catch e
    msg = sprint(showerror, e)
    step("  raises, as declared: " * first(split(msg, '\n')))
end

hdr(
    "4. :mork at Shared — SHARED SPACES. Same KIND, different ACCESS MODE. Whitepaper Fig. 4."
)
common = MC.make_space(:mork; mode=MC.Shared, name=Symbol("&common"))
games = MC.make_space(:mork; mode=MC.Shared, name=Symbol("&app/games"))
social = MC.make_space(:mork; mode=MC.Shared, name=Symbol("&app/social"))
step("one shared trie behind all three?  $(common.inner === games.inner === social.inner)")
for (nm, sp) in (("&common", common), ("&app/games", games), ("&app/social", social))
    step("  $(rpad(nm, 12)) prefix = $(String(copy(sp.prefix)))")
end
MC.core_add!(common, [:shared_fact, :visible_to_its_own_region])
MC.core_add!(games, [:score, 10])
MC.core_add!(social, [:score, 99])
step("games sees its own score only:   $(atoms(games))")
step("social sees its own score only:  $(atoms(social))")
step(
    "cross-prefix match does not bleed: games match (score \$v) → $(length(MC.core_match(games, [:score, Symbol("\$v")]))) hit(s)"
)
step(
    "addressable BY NAME (the prefix registry): lookup_prefix(:&app/games) = " *
    "$(String(copy(MC.lookup_prefix(Symbol("&app/games")))))"
)

hdr("5. Persistence — declared on the MORK kinds, and exercised here.")
dir = mktempdir()
MC.set_act_dir!(dir)
step(
    "empty region snapshot → $(MC.snapshot_space_to_act!(MC.make_space(:mork; mode = MC.Shared, prefix = Vector{UInt8}("empty_probe/")), "zoo_empty"))  ← false: nothing to save"
)
step(
    "filled region snapshot → $(MC.snapshot_space_to_act!(games, "zoo_games"))   act_exists → $(MC.act_exists("zoo_games"))"
)

hdr("6. THE CAPABILITY LEDGER — read this as the gap list")
MC.space_ledger(stdout)

hdr("7. What is NOT here, and why")
println(
    """
  Kinds are OPEN: a package that owns a backend registers it itself via `register_space_kind!`, so
  Core never has to depend on it. Nothing outside Core registers a kind yet, so these are absent:

    :neural / :vsa   FactorVSA holds the store (VectorArena{Id,V,B<:ReverseBackend} — already the exact
                     swappable-backend-as-type-parameter shape the Space store seam prescribes) and HMH
                     holds the ENCODERS (Column / RoleBook / Episode). HMH is our exact counterpart of
                     upstream rhoHDC, which the Space survey §6.3 classed as "the encoding half of a
                     Neural Space" — an encoder is not a store, so a :neural kind is FactorVSA's to
                     register, not HMH's.
    :tensor          MORKTensorNetworks already re-exports MORK's space ops and its ShardZipper offers
                     `partition_trie(space, l_max) → Vector{Vector{UInt8}}` — which IS JeTTa's `chunks`,
                     the one primitive the survey §3 said no body but JeTTa had. It is the natural
                     provider of `partition = true`.

  Neither is registered here on purpose: Core/Project.toml depends on MORK, PathMap and
  MorkSupercompiler only, and inverting that to reach outward for a constructor would be the wrong
  dependency arrow. Each package registers its own kind from its own `__init__`.

  And the big one: NO kind above except :vector answers `evaluate`. That is compile-arrow 6
  (docs/specs/COMPILE_ARROW_STATUS.md) — the trie-backed store loads but does not evaluate. Creating
  MORK-backed spaces is solved; RUNNING MeTTa against one is not.
"""
)
