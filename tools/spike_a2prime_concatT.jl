#!/usr/bin/env julia
# tools/spike_a2prime_concatT.jl — A2′ de-risk spike (METTA_COMPILATION_INTEGRATION_2026-06-17.md).
#
# Question: does compiling a `direct_call_safe` SYMBOLIC MeTTa function to a native Julia
# method eliminate the per-step interpreter overhead (the ~80% of reduce-to's 134s that the
# first-arg index could NOT touch)? `concatT` is the textbook case — a deterministic, single-
# pattern recursive list op that the reduct hammers.
#
# We hand-write the Julia method `concatT` *would* compile to (operating on Minimal's Atom
# types) and benchmark it vs Minimal interpreting `(concatT a b)`, same input. If native is
# ~free, A2′ is validated. Run:  julia --project=. tools/spike_a2prime_concatT.jl
using MeTTaCore
const SM = MeTTaCore.Eval
const SA = MeTTaCore.StandardMeTTa
using .SA: Atom, Sym, Expression

# ── the MeTTa def (for the interpreted side) ─────────────────────────────────
const CONCATT_DEF = """
(= (concatT \$a \$b)
   (if (== \$a ())
       \$b
       (let \$rest (concatT (cdr-atom \$a) \$b)
            (cons-atom (car-atom \$a) \$rest))))
"""

# ── the hand-written native compilation of concatT (what A2′ would emit) ─────
# (= (concatT $a $b) (if (== $a ()) $b (cons-atom (car-atom $a) (concatT (cdr-atom $a) $b))))
function concatT_native(a::Atom, b::Atom)::Atom
    (a isa Expression && isempty(a.children)) && return b
    ax = a::Expression
    rest = concatT_native(Expression(ax.children[2:end]), b)::Expression
    Expression(vcat(Atom[ax.children[1]], rest.children))
end

# ── helpers ──────────────────────────────────────────────────────────────────
parse1(s) = SM.parse_program(s)[1][2]                    # one expr → Atom (strip directive flag)
mklist(n) = parse1("(" * join(("e$i" for i in 1:n), " ") * ")")

function bench(f, reps)
    f()                                                   # warmup (exclude first-call JIT)
    t = @elapsed for _ in 1:reps; f(); end
    t / reps
end

# ── setup ─────────────────────────────────────────────────────────────────────
sp = SM.Space(); SM.load_core_stdlib!(sp); SM.load_metta!(sp, CONCATT_DEF)

println("n   native(µs)   interp(µs)    speedup    ok"); flush(stdout)
for n in (5, 10, 20)
    a = mklist(n); b = mklist(n)
    call = Expression(Atom[Sym("concatT"), a, b])

    native_res = concatT_native(a, b)
    interp_res = SM.metta_run(call, sp)[1]
    ok = string(native_res) == string(interp_res)

    tn = bench(() -> concatT_native(a, b), 50_000) * 1e6   # native is fast → many reps
    ti = bench(() -> SM.metta_run(call, sp), 30)    * 1e6  # interpreted is slow → few reps

    println(rpad(n,4), rpad(round(tn; digits=3),13), rpad(round(ti; digits=1),14),
            rpad(string(round(ti/tn; digits=0), "×"),11), ok ? "✓" : "✗ MISMATCH"); flush(stdout)
end
