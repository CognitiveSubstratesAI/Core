# Dialect gaps — porting PeTTa-targeted algorithms

MeTTaCore is the Julia MeTTa-on-MORK runtime, **faithful to
[hyperon-experimental](https://github.com/trueagi-io/hyperon-experimental)**. That
faithfulness is *load-bearing*: the conformance suite and the unit corpus only
*mean* something because Core matches hyperon's evaluation semantics. So the
governing rule when porting an algorithm written for another MeTTa implementation
is:

!!! warning "Never change Core's evaluator to match another dialect"
    When a ported algorithm misbehaves, the fix lives in the **port** (`.metta`),
    not in Core. Bending Core toward another dialect would make it a worse copy of
    that dialect *and* an unfaithful hyperon — and would void the conformance
    guarantees.

This page captures a concrete, recurring trap — **PeTTa**-targeted algorithms — so
future ports recognize it immediately.

## Why PeTTa differs

[PeTTa](https://github.com/trueagi-io/PeTTa) transpiles MeTTa to **Prolog**. That
gives it semantics that are PeTTa's *distinguishing characteristic*, not a missing
capability in Core. The canonical example:

| | `filter-atom`'s predicate is applied to … |
|---|---|
| **PeTTa** | **bound** elements (Prolog `include/3`) |
| **hyperon** | the **free (sealed) variable** — *cascades* if the predicate has a computation body |
| **Core** | the free var too — **faithful to hyperon** |

So a predicate written in PeTTa's idiom — e.g. `isLiteral` calling `(car-atom $e)` —
works on PeTTa (where `$e` is a bound atom) but **cascades / errors on both hyperon
*and* Core** (where the stdlib `filter-atom` rule evaluates it against a free var,
and `car-atom $var` is undefined).

## The three-oracle diagnostic

When a PeTTa-targeted algorithm misbehaves on Core, run the *same program* on three
runtimes (all installed locally — see the oracle setup) and read the pattern:

| Result | Diagnosis | Fix |
|---|---|---|
| fails on **Core only**, works on hyperon | **a Core bug** — Core diverges from its spec | fix **Core** |
| fails on **Core *and* hyperon**, works on PeTTa | **a dialect gap** — Core is faithful; the algorithm relies on PeTTa-specific (Prolog) semantics | dialect-adapt the **algorithm**, not Core |

The second row is the trap. "Fails on Core" alone is ambiguous; bringing
**hyperon in as the third leg** is what disambiguates it. If Core fails *identically
to hyperon*, Core is exonerated — it's faithful, and PeTTa is the odd one out.

!!! note "Worked example — MOSES"
    The MOSES port (a 1:1 port of iCog's PeTTa-targeted `metta-moses`) hit exactly
    this. The upstream `filter-atom`/`isLiteral` idiom **failed on both hyperon and
    Core** (cascade) and worked on PeTTa. That "failed on both" was the *good*
    outcome — it proved the dialect gap rather than a Core bug. Adapted MOSES-side
    (not in Core) → `test_moses` 227/227, and MOSES learns the target programs
    end-to-end.

## How to dialect-adapt (fix patterns)

Rewrite the PeTTa idiom into a hyperon-faithful form that produces *the same result*:

1. **Use Core's grounded, element-wise templates** — `(filter-atom $list $e (pred $e))`,
   `(map-atom $list $e (f $e))`, `(foldl-atom $list $init $acc $e (g $acc $e))`. These
   apply the body over the **bound** elements (the `include/3` behaviour), never the
   free var.
2. **Make predicates free-var-safe** — guard any structural call with
   `(== (get-metatype $e) Symbol)` (or a `case`) *before* `car-atom`/`cdr-atom`, so the
   predicate never errors on a variable.
3. **Inline / function-wrap** the body where a bare rule-predicate doesn't survive
   (inline grounded expression, function-wrapped predicate, or a direct-value body).
4. **Verify each rewrite against the hyperon oracle** — hyperon is the arbiter of
   "faithful"; PeTTa tells you only what the algorithm *targeted*.

## Other divergence classes to watch

The same "Core is faithful; adapt the port" discipline applies beyond `filter-atom`:

- **`True`/`False` are symbols**, not grounded booleans — check via
  `get-metatype … Grounded` / symbol comparison, per hyperon's idiom.
- **Non-determinism / set-ops** — PeTTa/MeTTaLog `(collapse (filter … (superpose $x)))`
  fan-out does **not** fork through application in Core's eager evaluator; port set-ops
  to the grounded `filter-atom`/`map-atom` + `union-atom`/`subtraction-atom` templates.
- **Higher-order list ops** — Core eagerly reduces a bare MeTTa-defined fn symbol passed
  as an arg and won't apply a var-head `($f x)`; use the grounded template ops instead.
- **`let` vs `let*`** — plain `let` does not destructure a tuple pattern; only `let*` does.

## The takeaway

A PeTTa-aimed package will have dialect divergences **by construction** — that's
PeTTa being PeTTa, not Core being broken. Run the three-oracle diagnostic on any
misbehavior, fix it in the port's `.metta`, keep it verified against hyperon, and
**leave Core's evaluator faithful**.
