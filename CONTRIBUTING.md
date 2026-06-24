# Contributing to MeTTaCore.jl

This project follows the [ColPrac](https://github.com/SciML/ColPrac) contributor's guide and
the [Blue](https://github.com/invenia/BlueStyle) code style (`.JuliaFormatter.toml`).

## Development setup

MeTTaCore dev-links its substrate (`MORK`, `PathMap`, `MorkSupercompiler`) as **siblings** via
relative `[sources]` paths. Check those repos out next to this one:

```
CognitiveSubstratesAI/
├── Core/        (this repo)
├── MORK/
├── PathMap/
└── MorkSupercompiler/
```

```julia
using Pkg
Pkg.develop(path = ".")
Pkg.test("MeTTaCore")
```

## Warm-REPL workflow (recommended)

Cold `julia` startup pays ~30–90 s of JIT each time. Develop against a warm session with
`Revise`, re-including changed `.metta`/`.jl` rather than restarting:

```julia
using Revise, MeTTaCore
space = new_core_space()
ef = e -> to_sexpr(eval_metta(from_sexpr(e), space))
register_all_primitives!(); _register_atom_ops!(ef); load_stdlib!(space)
run_metta("!(+ 2 3)", space)
```

## Tests & formatting

- `Pkg.test("MeTTaCore")` (or `julia --project=. test/runtests.jl`) must pass before a PR.
- Format with Blue before committing: `using JuliaFormatter; format(".")`.

## Code style

- Cognitive logic belongs in MeTTa (`lib/`, `stdlib/`); Julia is the hardware-primitive layer.
- MeTTa functions: one-line description + `;; (name args) → result` example +
  head-destructured clauses + an immediate test.
- **Type declarations are tier-dependent.** MeTTa is gradually typed (declarations optional;
  no auto-checking pass). Fully type the *stdlib / grounded-op* tier (`src/standard/stdlib.metta`);
  keep *domain-algorithm libraries* (`lib/**`, e.g. PLN/ECAN/quantale) **bare** — bare symbolic
  constructors, reuse built-in types (`Number`/`Bool`/`Atom`/`Expression`), and **no custom
  `(: X Type)`** unless the algorithm is *about* types (GADT/dependent dispatch). Over-typing a
  domain lib is non-idiomatic (verified against the MeTTa spec + hyperon-experimental + CeTTa).
  See [MeTTa Typing Conventions](docs/src/typing-conventions.md).
