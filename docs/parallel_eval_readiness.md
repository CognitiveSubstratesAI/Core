# Parallel-Eval Readiness — Interpreter Thread-Safety Map (2026-06-25)

The live `StandardMeTTa.Interpreter` is **single-threaded by design**; the warm MettaJam server runs every
eval under one `ReentrantLock` (`server.jl`), so the global mutable state below is safe *today* only because
access is serialized. This note maps what must change before eval can run on more than one thread — so the
work starts from the real blocker, not the easy piece.

> **Status: analysis only.** No parallel-eval driver exists. Per the measured-need discipline, do NOT
> implement these piecemeal — especially not an atomic `_VAR_COUNTER`, which would tax the freshvar hot path
> (just optimized) for a capability nothing uses and would leave the interpreter thread-unsafe anyway.

## Eval-mutated state, classified

| state | site | mutated during eval | fix | difficulty |
|-------|------|---------------------|-----|-----------|
| **`Space.atoms` / `.index` / `.wildcard`** | `add_atom!`/`remove_atom!` (Interpreter.jl:341/347) | **yes** — every `add-atom`/`remove-atom` | concurrent Space **or** per-task spaces | **hard — the blocker** |
| `_REDUCE_DEPTH` | :908/910/922 (recursion-depth guard) | yes | **task-local** (per eval context) | medium |
| `_METTA_STEPS` | :937 (step-limit) | yes | **task-local** | medium |
| `_DIAG_STEPS` | :733 (diagnostic) | yes | task-local or drop | easy |
| `_VAR_COUNTER` | :358/359 (freshvar — unique-var correctness) | yes | atomic **or** per-task id range | **trivial** |
| `_GROUNDED_OP_TYPE_CACHE` | :808/814 (lazy parse cache) | yes — `get!` | eager pre-fill (read-only) or lock | trivial |
| `_MODULE_PATH` | import! / tests | yes (during import) | task-local or locked | easy |
| `TOKEN_REGISTRY`, `_GROUNDED_OP_TYPES`, `_METTA_MAX`/`_INTERPRET_MAX`/`_METTA_DEBUG` | load-time / config | **no** (read-only during eval) | none | **safe** |

## The two real blockers (everything else is minor)

1. **Shared mutable `Space`.** `mutable struct Space { atoms::Vector, index::Dict, wildcard::Vector }`;
   `add-atom`/`remove-atom` push/delete on all three. Parallel eval over one Space data-races them. This is
   *why* the server holds one LOCK. Options:
   - **per-task spaces** — each parallel eval gets its own Space; simplest, but cross-task `add-atom` isn't
     shared (fine for independent queries, wrong for a shared KB).
   - **concurrent Space** — fine-grained-locked or lock-free `atoms`/`index`; correct for a shared KB, hard.
   - **read-parallel / serialize-writes** — parallel `match`/`query` (read-only), funnel mutations through a
     lock; matches the common workload (many reads, few writes).
2. **Per-task eval state** — `_REDUCE_DEPTH`/`_METTA_STEPS` are per-*evaluation* (recursion depth, step
   count). Making them atomic is WRONG — two parallel evals would corrupt each other's depth guard. They must
   become **task-local** (`Base.@task_local`/`TaskLocalValues`), i.e. threaded through the eval context.

## The trivial tail (do LAST, when a driver exists)

`_VAR_COUNTER` → `Threads.Atomic{UInt64}` or per-thread id ranges (avoids the hot-path atomic-contention tax);
`_GROUNDED_OP_TYPE_CACHE` → eager pre-fill so it's read-only during eval; `_MODULE_PATH` → task-local.

## Conclusion
Thread-safety here is a **design effort gated on the Space**, not a counter tweak. The 1.12 concurrency
primitives (`OncePerProcess` for the registries/cache, `@task_local` for the eval counters, atomics for
`_VAR_COUNTER`) are the right tools for the *tail* — but they're only worth wiring once (a) there's an actual
parallel-eval workload that needs it, and (b) the Space-concurrency model is chosen. Until then this is a map,
not a TODO. See also `interpreter_perf_findings.md` (the perf track that flagged parallel eval as a future
direction) and the wedged-server note (one LOCK serializing all sessions = the *current* concurrency pain,
better addressed by per-session spaces or a second server than by interpreter threading).
