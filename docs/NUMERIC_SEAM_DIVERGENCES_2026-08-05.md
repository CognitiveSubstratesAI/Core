# Numeric seam: three measured divergences from the reference, and why no gate caught them

**Date**: 2026-08-05 · **Status**: MEASURED, unfixed. No decision taken.
**Companions**: [`CORE_NUMERIC_BACKEND_SPEC.md`](CORE_NUMERIC_BACKEND_SPEC.md) ·
[`CORE_VS_HYPERON_BY_LAYER.md`](CORE_VS_HYPERON_BY_LAYER.md)

Recorded because all of this was derived once, at cost, and none of it is visible from any green
check. Core passes **234/234 hyperon conformance**, **LeaTTa 270/270 with CORE_BUG = 0**, health
gate **5/5**, and the full suite — with every divergence below live.

---

## The three divergences

Measured directly (`q("!(…)")` on the live engine), against the reference read from source.

| # | expression | Core | hyperon-experimental 0.2.10 | LeaTTa (proved spec) | CeTTa 1.3.2-dev |
|---|---|---|---|---|---|
| 1 | `(/ 7 2)` | **`3.5`** | `Number::Integer(3)` | `Ground.int 3` | int, promotes |
| 1b | `(/ 4 2)` | **`2.0`** (Float) | `Number::Integer(2)` | `Ground.int 2` | int |
| 2 | `(% 7 0)` | **raw Julia `DivideError` escapes** | `ExecError` (guarded) | `Error (% 7 0) DivisionByZero` atom | guarded |
| 3 | `9223372036854775808` | **`9.223372036854776e18`** (silent Float) | hard parse error | — | promotes to bignum |
| 3b | `99999999999999999999999` | **`1.0e23`** | hard parse error | — | promotes to bignum |

### 1 — integer division returns Float

`Interpreter.jl:403 _num_binop("/", /)` uses Julia's `/`, which promotes `Int÷Int` to `Float64`.
hyperon's `/` is hand-written and its Integer/Integer branch returns `Number::Integer(a / b)`
(`lib/src/metta/runner/stdlib/arithmetics.rs:154-155`) — Rust truncating integer division.

Note `(/ 4 2)` → `2.0`: the **atom type** differs even when the value is exact. hyperon's `Number`
equality is loose, so `2.0 == 2` may still hold, but `get-type` and any type-directed dispatch see
different things.

### 2 — division by zero leaks a host exception

A Julia `DivideError` escapes the evaluator. Under MeTTa's partial semantics a bad argument should
reduce to inert or to an error atom so nondeterministic evaluation continues on other branches —
never crash the host.

This one was **already known and half-handled**: `Primitives.jl:44-46` declines rather than throwing
on the MORK lane, with the comment *"The interpreter's own `%` DOES currently throw here; tracked
separately, since changing it needs the hyperon oracle to say what `(% 7 0)` should produce."*

**The oracle now answers.** hyperon guards `DivisionByZero` for `/`
(`arithmetics.rs:154`); LeaTTa's `modOp` (`MettaHyperonFull/Minimal/Stdlib.lean:95-101`) returns
`Error (% a b) DivisionByZero` for a zero divisor, docstring citing *"Hyperon's `checked_div`"*.

### 3 — an out-of-range literal silently becomes a Float

`Parser.jl:108-112` does `tryparse(Int, token)`; on failure it falls through to
`tryparse(Float64, token)`. So `9223372036854775808` parses as a `Float64` with precision gone.
hyperon registers the integer literal as a **fallible** token specifically so this can fail
(`arithmetics.rs:163-164`) and errors with *"Could not parse integer: … number too large to fit in
target type"*.

---

## Why no gate caught them

**Not bad luck — a structural coverage gap in each gate.**

**LeaTTa's oracle gate.** Its design (`test/oracle/leatta/README.md`) is transitive: the corpus is
Hyperon's own unmodified 270 directives, LeaTTa *proves* every one passes, so "Core passes directive
d" ≡ "Core computes the proved-correct value." Elegant — and it inherits Hyperon's coverage exactly.
Across all 270 directives the seam appears **twice**:

```
c1_grounded_basic.metta:12    (- 8 (/ 4 6.4))     ← `/` with a FLOAT operand; never Int ÷ Int
c1_grounded_basic.metta:16    (% 21 17)           ← `%` with a NON-ZERO divisor
```

and there is **no integer above 6 digits** in the corpus. LeaTTa's `divOp`/`modOp` specify the
zero-divisor branch precisely, in Lean, with kernel-checked proofs — and nothing that gates us ever
invokes it. The README's claim *"the strongest oracle in the fleet by provenance"* is true about
provenance and silent about coverage.

⚠️ The corpus is vendored **verbatim** from upstream, so it cannot be extended to cover this. Any
test for these must be Core-side.

**LeaTTa's metatheory.** `MettaHyperonFull/Proofs.lean:104` proves `numBin_isNumber` — arithmetic is
closed on `Number`. `3.5` is a `Number`. The theorem holds while the answer is wrong; it is about
typing, not value. (The separate `MeTTaIL/` layer models no numbers at all — its AST is
`var | sexp | subst`.)

**The hyperon conformance matrix (234/234).** Same shape: a feature corpus, not an edge-case corpus.

---

## The open decision (NOT taken)

**Silent i64 wraparound is CONFORMANT.** hyperon is `Number { Integer(i64), Float(f64) }`
(`hyperon-atom/src/gnd/number.rs:7-11`) with plain Rust operators — no `wrapping_`/`checked_`/
`saturating_` — and ships release builds with `overflow-checks = false`. Measured on upstream's own
prebuilt release binary:

```
!(* 99999999999 99999999999)  ->  1864711849423024129     # BYTE-IDENTICAL to Core
```

So "make overflow loud" would now be a **divergence**, not a fix. Upstream's own comment
(`lib/src/metta/text.rs:868-871`) says *"…an integer that overflows the type's capacity **before we
implement bigint**"* — bigint is stated intent they have not reached.

**CeTTa already reached it**, and shares our MORK/PathMap substrate. One numeric tower in
`src/grounded.c`, not per-dialect: `int64_t` fast path, promoting to GMP `mpz_t` on overflow,
detected by `__int128` widening (`grounded.c:1651-1674`) — not by wrapping, not by
`__builtin_*_overflow`:

```c
__int128 sum = (__int128)ai + (__int128)bi;
if (sum >= INT64_MIN && sum <= INT64_MAX) return atom_int(a, (int64_t)sum);
return eval_integer_binary_gmp(...);
```

Pinned by `tests/test_integer_overflow_regression.metta`. GMP on by default (`Makefile:28`).

In Julia the same pattern is cheaper than in C — native `Int128`, native `BigInt`, no linkage:

```julia
r = Int128(a) + Int128(b)
typemin(Int64) <= r <= typemax(Int64) ? Int64(r) : big(a) + big(b)
```

**The question is not conformance vs capability.** It is whether Core tracks the reference's
*current behaviour* (wrap) or its *stated direction* (promote), on a point where our closest sibling
has already chosen. Owner decision; deliberately left open here.

---

## What to do, in order

1. **Core-side seam tests** for all three. Needed under *any* resolution — right now nothing would
   notice if these answers changed again. Cannot live in the vendored LeaTTa corpus.
2. **The boundary layer that does not currently exist.** `+ - * / %` have TWO lowerings —
   `Interpreter.jl:403 _num_binop` and `Primitives.jl:32 _register_arithmetic!` — in different files,
   already disagreeing on `(% 7 0)`. They should sit side by side in one module that owns the three
   decisions above (result type, partiality, literal range), so both lanes are provably the same
   operation. `NumpyOps.jl` shrinks to its ~10 marshalling lines once that exists.
3. **The bignum decision**, then implement whichever way it goes.

Divergences 1 and 2 are worth fixing **regardless** of the bignum decision — both hyperon AND LeaTTa
AND CeTTa agree against us on integer division and on the zero divisor. Only #3's *wrapping* half is
a genuine three-way split.
