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

"Closure-lane answers: emit Julia per head, register at the seam, then ask.

Rules are ALSO loaded into the space, so a head the emitter DECLINES still answers via the
interpreter — otherwise a decline would read as a wrong answer. `rule_results` short-circuits on a
compiled head, so a head that IS compiled cannot also answer from the space (no doubling from the
harness itself; verified 2026-09-03)."
function closure(program::AbstractString)
    E = MeTTaCore.Eval
    sp = E.Space(); E.load_core_stdlib!(sp)
    toks = E.tokenize(program); i = Ref(1); atoms = MeTTaCore.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
        push!(atoms, E.parse_from(toks, i, sp.tokens))
    end
    cls = MeTTaCore.CompilerANormal.translate_program(MeTTaCore.CompilerFrontend.lower_program(atoms))
    heads = MeTTaCore.CompilerEmitJulia.emit_julia_program(cls)
    E.uncompile_all!()
    s2 = E.Space(); E.load_core_stdlib!(s2)
    out = String[]
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        bang || E.load_metta!(s2, f)              # rules in the space: declines still answer
    end
    for (h, fn) in heads
        E.compile_head!(h, fn, UInt64(1))
    end
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        if bang
            res = E.load_metta!(s2, "!" * f)
            append!(out, String[string(x) for y in res for x in (y isa AbstractVector ? y : [y])])
        end
    end
    # 🔴 THE HEAD UNDER TEST IS `w`, AND ONLY ITS STATUS MEANS ANYTHING. An earlier version of this
    # probe reported total `fired` across all heads and called `case`/`collapse` GREEN in this lane.
    # They were not: the emitter declined `w` and emitted only the `nd` CALLEE, so the answer came
    # from the SPACE — i.e. from the interpreter — while `nd` firing made the row look compiled.
    # A differential that passes because the thing under test fell back proves the interpreter equals
    # itself. MEASURED 2026-09-03; the fix is to report `w` specifically.
    wfired = haskey(heads, :w) ? E.fired(:w) : 0
    E.uncompile_all!()
    (sort(out), haskey(heads, :w), wfired)
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
    println(rpad("CONSTRUCT", 34), rpad("INTERP", 17), rpad("IL LANE", 24), "CLOSURE LANE")
    println("─"^92)
    ndoubled = 0
    ndiff = 0
    il_bad = String[]
    cl_bad = String[]
    cl_unproven = String[]
    for (name, defs, q) in CASES
        prog = defs * q * "\n"
        i = interp(prog)
        c, ncomp, nfb = try
            compiled(prog)
        catch e
            (["<EXC $(typeof(e))>"], 0, 0)
        end
        cl, w_emitted, w_fired = try
            closure(prog)
        catch e
            (["<EXC $(typeof(e))>"], false, 0)
        end
        same = c == i
        samecl = cl == i
        doubled = !same && sort(unique(c)) == sort(unique(i)) && length(c) > length(i)
        same || (ndiff += 1); doubled && (ndoubled += 1)
        same || push!(il_bad, name); samecl || push!(cl_bad, name)
        iltag = same ? "ok" : (doubled ? "✗ DOUBLED" : "✗ " * string(c))
        # "ok" only counts when the head UNDER TEST compiled and fired. Otherwise the answer came
        # from the space and the row says nothing about this lane.
        cltag = if !w_emitted
            "— DECLINED w"
        elseif w_fired == 0
            "— w emitted, NOT fired"
        elseif samecl
            "ok  [w fired $(w_fired)]"
        else
            "✗ " * string(cl)
        end
        samecl && w_emitted && w_fired > 0 || push!(cl_unproven, name)
        println(rpad(name, 34), rpad(string(i), 17), rpad(iltag, 24), cltag)
    end
    println("─"^92)
    println("IL lane wrong:      ", isempty(il_bad) ? "none" : join(il_bad, ", "))
    println("CLOSURE lane wrong: ", isempty(cl_bad) ? "none" : join(cl_bad, ", "))
    println("CLOSURE NOT PROVEN (declined / never fired — the row says nothing):")
    println("   ", isempty(cl_unproven) ? "none" : join(cl_unproven, ", "))
    println()
    println("🔑 THE READING THAT DECIDES THE ARCHITECTURE QUESTION:")
    println("   red in IL, GREEN in closure  ⇒ the goal-list IR's SHAPE is the cause; the lane matters.")
    println("   red in BOTH                  ⇒ the seam is NOT the IR's shape. A rewrite buys nothing,")
    println("                                  and the boundary itself is what has to be fixed.")
end

main()
