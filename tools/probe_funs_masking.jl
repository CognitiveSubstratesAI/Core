# probe_funs_masking.jl — WHICH CONSTRUCTS DOUBLE WHEN `funs` IS WIDENED?
#
# WHY. Attempt #4 at the whole-program pre-pass (2026-09-03) was reverted by the corpus with ANSWER
# DOUBLING: `(= (w) (function (return (nd))))` answered ["a","a","b","b"] against the interpreter's
# ["a","b"]. The mechanism is in `ANormal.jl:556-564` — for `eval`/`function`/`return`, but not
# `chain`, an argument is BOTH hoisted into a goal AND re-rendered inside the verbatim node, so a
# nondeterministic call runs twice. That was harmless only while cross-head calls were classified as
# DATA and never hoisted.
#
# 🔴 THE OPEN QUESTION THIS ANSWERS. Masking is a property of the NARROW `funs` SET, not a fact about
# that one interaction. Every construct that behaves differently for a CALL than for DATA is a
# candidate, and `(nd)` under `function`/`return` is simply the one the corpus happened to cover.
# Enumerating them by reading is how the last three attempts each found exactly one. So: measure.
#
# USAGE — run it TWICE, and the DELTA is the answer:
#     julia --project=. tools/probe_funs_masking.jl          # baseline, current HEAD
#     …apply the pre-pass locally, uncommitted…
#     julia --project=. tools/probe_funs_masking.jl          # every new ✗ is a prerequisite
#
# `chain` is the known-safe control (`_KEEP_WHOLE`); `eval`/`function`/`return` are known-unsafe once
# hoisting happens. Anything ELSE that flips is a defect nobody has named yet.
using MeTTaCore

const ND_SYM = "(= (nd) a)\n(= (nd) b)\n"        # nondeterministic, symbolic
const ND_NUM = "(= (ndn) 1)\n(= (ndn) 2)\n"      # nondeterministic, numeric

"Interpreter answers for `program`, sorted, flattened."
function interp(program::AbstractString)::Vector{String}
    E = MeTTaCore.Eval
    sp = E.Space(); E.load_core_stdlib!(sp)
    out = String[]
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        res = E.load_metta!(sp, bang ? "!" * f : f)
        bang && append!(out, String[string(x) for y in res
                                   for x in (y isa AbstractVector ? y : [y])])
    end
    sort(out)
end

"Compiled answers for `program`, sorted, plus the decline count."
function compiled(program::AbstractString)
    r = MeTTaCore.compile_run(program; max_steps = 512_000)
    (sort(String[string(a) for (_, ans) in r.answers for a in ans]),
        r.compiled, r.fell_back)
end

# Each case puts a NONDETERMINISTIC call in one syntactic position. If widening `funs` makes that
# call BOTH a hoisted goal and a re-rendered term, the answers double and this catches it.
const CASES = [
    ("chain           (CONTROL: _KEEP_WHOLE)", ND_SYM * "(= (w) (chain (nd) \$v \$v))\n",            "!(w)"),
    ("eval            (known-unsafe)",         ND_SYM * "(= (w) (eval (nd)))\n",                     "!(w)"),
    ("function/return (known-unsafe)",         ND_SYM * "(= (w) (function (return (nd))))\n",        "!(w)"),
    ("return          (bare)",                 ND_SYM * "(= (w) (function (return (nd))))\n",        "!(w)"),
    ("let  VALUE",                             ND_SYM * "(= (w) (let \$v (nd) \$v))\n",              "!(w)"),
    ("let* VALUE",                             ND_SYM * "(= (w) (let* ((\$v (nd))) \$v))\n",         "!(w)"),
    ("if   THEN-ARM",                          ND_SYM * "(= (w) (if (== 1 1) (nd) z))\n",            "!(w)"),
    ("if   CONDITION",                         ND_NUM * "(= (w) (if (== (ndn) 1) yes no))\n",        "!(w)"),
    ("case SCRUTINEE",                         ND_SYM * "(= (w) (case (nd) ((a A) (b B))))\n",       "!(w)"),
    ("superpose ARG",                          ND_SYM * "(= (w) (superpose ((nd) z)))\n",            "!(w)"),
    ("collapse  ARG",                          ND_SYM * "(= (w) (collapse (nd)))\n",                 "!(w)"),
    ("quote     ARG",                          ND_SYM * "(= (w) (quote (nd)))\n",                    "!(w)"),
    ("match     PATTERN",                      ND_SYM * "(= (w) (match &self (nd) matched))\n",      "!(w)"),
    ("grounded  ARG (cons-atom)",              ND_SYM * "(= (w) (cons-atom (nd) ()))\n",             "!(w)"),
    ("grounded  ARG (arith)",                  ND_NUM * "(= (w) (+ (ndn) 10))\n",                    "!(w)"),
    ("nested CALL ARG",                        ND_SYM * "(= (id \$x) \$x)\n(= (w) (id (nd)))\n",     "!(w)"),
    ("TWO nd in one body",                     ND_NUM * "(= (w) (+ (ndn) (ndn)))\n",                 "!(w)"),
]

function main()
    println("─"^92)
    println(rpad("CONSTRUCT", 40), rpad("COMPILED", 26), rpad("INTERP", 18), "VERDICT")
    println("─"^92)
    ndoubled = 0
    ndiff = 0
    for (name, defs, q) in CASES
        prog = defs * q * "\n"
        i = interp(prog)
        c, ncomp, nfb = try
            compiled(prog)
        catch e
            (["<EXC $(typeof(e))>"], 0, 0)
        end
        same = c == i
        # DOUBLING is the specific shape: same SET, larger MULTISET.
        doubled = !same && sort(unique(c)) == sort(unique(i)) && length(c) > length(i)
        verdict = same ? "ok" : (doubled ? "✗ DOUBLED" : "✗ DIFFERS")
        same || (ndiff += 1)
        doubled && (ndoubled += 1)
        println(rpad(name, 40), rpad(string(c), 26), rpad(string(i), 18),
            verdict, nfb > 0 ? "   (declined $(nfb))" : "")
    end
    println("─"^92)
    println("cases: $(length(CASES))   differing: $(ndiff)   of which DOUBLED: $(ndoubled)")
    println()
    println("Run again with the pre-pass applied locally. EVERY NEW ✗ IS A PREREQUISITE for")
    println("attempt #5, named up front instead of found by a fourth-hour suite run.")
end

main()
