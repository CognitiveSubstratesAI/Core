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
- MeTTa functions: type + one-line description + `;; (name args) → result` example +
  head-destructured clauses + an immediate test.
