"""
LibPolicy — read a MeTTa library's POLICY CONSTANTS out of a live space, through the COMPILER lane.

## Why this exists

Policy constants in this system are MeTTa atoms on purpose. `lib/ecan/ECAN_Policies.metta:5`:
"ALL values here are live atoms — the AGI can rewrite them without restarting Julia", under a header
that reads "Spreading Parameters (overridden by self-evolution)". Hyperon Whitepaper 2026 v5 §6.11
puts exactly this class — "attention thresholds / routing weights" — on the lowest rung of its
self-modification ladder ("may auto-adjust within bounds"), and §7.7 assigns "policy semantics" to
MeTTa while warning that the host-language adapter "does not become a second hidden policy engine."

Julia had no way to ASK for one of those values. That is not a gap in tidiness, it is the documented
cause of the defect class: `WorldModel/src/PLNCore.jl:189` — "Being unable to reach the canonical
formula is exactly what made someone write it out again." It happened three times.

  2026-07-22  PLN truth formulas transcribed into `Beliefs.jl` (`c_new = n/(n+1)` beside a comment
              naming the canonical `Truth_w2c` it was copying).
  2026-05-10  `MORKTensorNetworks/src/ecan/ECANTensorBridge.jl` implemented ECAN in Julia without
              anyone opening `lib/ecan/`.
  2026-08-05  while fixing that, `hebbian_max_allocation = 0.05f0` was hardcoded there against
              `lib/ecan/ECAN_Policies.metta`'s `(hebbian-max-allocation-percentage) 0.5` — a 10x
              silent divergence, written the same day, by someone who had read the audit note.

Each time the constant was unreachable and got rewritten. This module makes it reachable.

## A POLICY READ IS A QUERY, NOT A REDUCTION — and that is the architecturally load-bearing choice

`(= (max-spread-percentage) 0.3)` is a FACT in the Atomspace. Reading it is a `match` against the
trie — a layer-2 Knowledge-Representation operation (Whitepaper Figure 1: "Atomspaces, Spaces, truth
values, goals, procedures") — not a computation to be compiled and run.

Getting this wrong is easy and was nearly done here. The obvious implementation is
`!(max-spread-percentage)` through `mc_run`, letting the `(=)` rule reduce. But `mc_run`'s `:direct`
lane routes `(=)` through `mm2_route!`, i.e. it LOWERS MeTTa DIRECTLY TO MM2 — and Figure 2 has no
such arrow. MeTTa and PyMeTTa compile to **MeTTa-IL**; MM2 kernels are a separate, hand-authored
input that *runs on* the MORK Atomspace (dashed edge, labelled "runs on"). There is no sanctioned
MeTTa→MM2 compile path, and a policy reader must not add a consumer of one.

Nor can the MeTTa-IL lane serve it today: `metta_il_run!` begins with `_il_assert_all_rewrites`, so
it takes `~>` rewrites, and `metta_il_run_pipeline!` takes `def`/`match`/`emit`. Neither reduces a
nullary `(=)` head.

`match` dissolves the problem rather than working around it. No `(=)` reduction, so no lowering
question, so nothing to migrate when the executor moves to MeTTa-IL at layer 5. Reading a stored
fact was never a compilation problem.

⚠️ CONSEQUENCE, stated so it is not discovered as a bug: a policy atom must be a LITERAL,
`(= (name) <number>)`. A computed policy — `(= (name) (* 2 (other)))` — will not be reduced by this
reader and will fail loudly rather than silently returning the unreduced form. That is the intended
contract: a constant that needs evaluating is a derived quantity, and derived quantities belong in
the rules that consume them, not in a shared constants file that many callers read cheaply.

⚠️ `WorldModel/src/PLNCore.jl`'s `_policy_num` predates this and still uses the interpreter
(`metta_run` over a private `Space()`). Migrating it is a separate change; do not copy it as the
pattern.

## THE EXECUTOR WILL CHANGE — `lib_policy` is the durable surface

MeTTa-IL sits at layer 5, the ASI:Chain Runtime Environment (Figure 1), with Rholang, RSpace and
provenance. ECAN is a layer-3 algorithm and its constants are layer-1/2 atoms. So "the executor
becomes MeTTa-IL" is a layer-5 change that must not reach a layer-3 caller.

The CONTRACT is `lib_policy(space, name) -> Float64`. Everything under it is absorbed here. Same
principle TECAN Stage T7 states for its own worker IR: "Durable semantics should live in portable
facts rather than backend-private state… this allows an initial PeTTa orchestration layer to be
replaced later by a MeTTa-IL executor without changing the architecture."

Reading the trie directly, rather than reducing, shrinks that exposure to almost nothing: the
implementation is one call to `core_rules`, the space's own rule scanner. There is no executor in
the path to migrate.

## ⚠️ TWO STORES — aim at the right one

Core has TWO atom stores, and they are easy to confuse because both are called "space":
  - the OLD interpreter store — a pure-Julia `Vector{Atom}`, what `&self` resolves to;
  - the NEW `CoreSpace` — the MORK byte trie, what `load_core_lib!` writes.

MEASURED 2026-08-05 while building this: `load_core_lib!(cs, :ecan)` puts the constants in the trie,
`core_atoms(cs)` shows `(= (max-spread-percentage) 0.3)` plainly — and
`mc_run(cs, "", "!(match &self (= (max-spread-percentage) \$v) \$v)")` returns **empty**, for all 30
constants, because `&self` was pointed at the old store. Nothing errors. An empty result from the
wrong store is indistinguishable from a missing atom, and "the atom is missing" is exactly the
premise that leads someone to hardcode the value in Julia.

So: read through `core_rules`/`core_atoms` on the `CoreSpace`. Do not route policy reads through
`&self`.

## WHICH SPACE — the part that is easy to get wrong

The whole point is that the value can be REWRITTEN at runtime. A reader bound to a private space
would return the file's declared default forever and never see a self-evolution edit — which looks
identical to working. So the primary method takes the space you actually run in:

    lib_policy(cs, "max-spread-percentage")            # reads YOUR space — sees rewrites
    lib_policy(:ecan, "max-spread-percentage")         # convenience: a private, lib-only space

Use the second only for the DECLARED DEFAULT (tests, tooling, a bootstrap value). Anything inside a
cognitive loop must pass its own space, or it is reading a constant with extra steps.

## Generic, not ECAN-specific

Every `lib/` module gets this for free — `ecan`, `pln`, `MOSES`, `metamo`, `subrep`, `quantale`,
`hyperseed`. The defect recurred across subsystems, so the fix is at the subsystem-agnostic layer
rather than a set of hand-written ECAN accessors. `lib_policy_names` enumerates what a library
declares, which is what an audit (or TECAN Stage T0's cost annotation) needs.
"""

const _POLICY_SPACES = Dict{Symbol, Any}()

"""
    policy_space(lib) -> CoreSpace

The private, lazily-built `CoreSpace` for `lib`, holding only that library's DECLARED defaults.
Built once per library per process via `load_core_lib!`.

⚠️ This space is NOT the agent's space. Values here never change unless something rewrites them
*here*. For anything that must observe self-evolution, pass your own space to [`lib_policy`](@ref).
"""
function policy_space(lib::Symbol)
    get!(_POLICY_SPACES, lib) do
        cs = new_core_space()
        load_core_lib!(cs, lib)
        cs
    end
end

"Forget the cached private space for `lib` (or all of them) — for tests, and after a lib file edit."
function reset_policy_space!(lib::Union{Symbol, Nothing} = nothing)
    lib === nothing ? empty!(_POLICY_SPACES) : delete!(_POLICY_SPACES, lib)
    nothing
end

"""
    lib_policy(cs::CoreSpace, name) -> Float64
    lib_policy(lib::Symbol,  name) -> Float64

Read the policy atom `(name)` out of `cs` (or out of `lib`'s private default space) and return its
numeric value.

Implemented as a MATCH against the space, not a reduction — `(= (name) <literal>)` is a stored fact.
See the module docstring for why that distinction is architectural and not stylistic.

Throws — deliberately — if the atom is absent or is not a literal number. A policy reader that
silently returns a fallback is the "second hidden policy engine" §7.7 warns against; a missing atom
is a broken configuration, not a default.
"""
function lib_policy(cs, name::AbstractString)::Float64
    # `core_rules` is the MORK trie's own rule scanner: it walks `(= (head args...) body)` atoms in
    # THIS CoreSpace. Not `mc_run` + `!(match &self ...)` — `&self` resolves to the OLD interpreter
    # `Vector{Atom}` store, which `load_core_lib!` never writes, so that query returns empty while
    # the atom sits in the trie (measured 2026-08-05: `core_atoms` showed it, the match did not).
    # Not `core_match` with a string pattern either — it takes a PARSED SExprConvertible, and its own
    # docstring notes "MORK's arity-1 fast-path returns the pattern itself, which would never match
    # real rules."
    #
    # `core_rules` is also CACHED PER HEAD with the cache invalidated by `core_add!`/`core_remove!`,
    # which is precisely the property this reader lives or dies on: a self-evolution rewrite must be
    # visible on the next read.
    rules = core_rules(cs, Symbol(name))
    isempty(rules) && error(
        "lib_policy: no rule `(= ($name) …)` in this space. Either the library declaring it was " *
        "never loaded here (load_core_lib!), or the name is wrong. Do NOT substitute a Julia " *
        "constant — that is the failure this module exists to prevent.")
    for (args, body) in rules
        isempty(args) || continue            # nullary only: `(= (name) <literal>)`
        v = body isa Number ? Float64(body) : tryparse(Float64, strip(string(body)))
        v === nothing && error(
            "lib_policy: `($name)` has body `$body`, not a literal number. A COMPUTED policy is " *
            "unsupported by design — see the module docstring.")
        return v
    end
    error("lib_policy: `($name)` exists but takes arguments — it is a function, not a policy " *
          "constant. Arities found: $([length(a) for (a, _) in rules]).")
end

lib_policy(lib::Symbol, name::AbstractString) = lib_policy(policy_space(lib), name)

"""
    lib_policy_int(cs_or_lib, name) -> Int

`lib_policy` rounded to an `Int`, for budgets, counts and depth limits — and for TECAN's typed fuel
ledger, whose vectors are `ℕ^T` (integer counters), not floats.
"""
lib_policy_int(target, name::AbstractString) = round(Int, lib_policy(target, name))

"""
    lib_policy_names(lib) -> Vector{String}

Every nullary numeric constant `(= (name) <number>)` DECLARED in `lib`'s `.metta` sources, sorted.

Read from the FILES, not from a space — this answers "what does this library declare?", which is an
audit and tooling question (what to annotate, what to cross-check against Julia). For the current
VALUE of any of them, use [`lib_policy`](@ref), which reads the space and therefore sees rewrites.
The distinction matters: a rewritten atom is invisible here, by design.
"""
function lib_policy_names(lib::Symbol)::Vector{String}
    dir = nothing
    for d in Interpreter._MODULE_PATH[]
        cand = joinpath(d, String(lib))
        isdir(cand) && (dir = cand; break)
    end
    dir === nothing && error("lib_policy_names: no directory for library `$lib` on the module path")
    names = String[]
    rx = r"^\s*\(=\s*\(([a-zA-Z0-9!?*/+<>=-]+)\)\s+-?[0-9]*\.?[0-9]+\s*\)"
    for f in sort(filter(f -> endswith(f, ".metta"), readdir(dir; join = true)))
        for ln in eachline(f)
            m = match(rx, ln)
            m === nothing || push!(names, m.captures[1])
        end
    end
    sort!(unique!(names))
end

export policy_space, reset_policy_space!, lib_policy, lib_policy_int, lib_policy_names
