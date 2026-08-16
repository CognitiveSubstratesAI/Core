# il_coverage_survey.jl — ARROWS 1-4 (THE COMPILE ARROW) coverage on the REAL libraries.
#
# 🔴 MEASURED 2026-08-15, and it corrects a number this repo had wrong by ~3x:
#     ECAN  115 defs -> EmitIL compiles 114   (99.1%),  1 declined
#     PLN   283 defs -> EmitIL compiles 266   (94.0%), 17 declined
#     TOTAL 398 defs -> 380 COMPILE (95.5%),           18 declined,  0 raised
#
# 🔴 RE-MEASURED 2026-08-16 after `21bd63b` (binder scopes + PeTTa's middle clause). The TOTAL barely
# moves (380 -> 381) but the COMPOSITION changes completely, and both directions are CORRECTNESS:
#     ECAN  115 defs -> 101 (87.8%), 14 declined     (was 1)
#     PLN   283 defs -> 280 (98.9%),  3 declined     (was 17)
#
#   * PLN 17 -> 3: **the 13 `|-` inference rules now COMPILE** — the target of roadmap 0.2.
#   * ECAN 1 -> 14: **ALL 14 are binder-related, and they were previously MIS-COMPILED.** Measured
#     with binders disabled, `sum-prob-weights` emitted
#         (unify ($Pr $w) $pt (chain (metta (+ $acc $w) …) $__t1
#                               (chain (metta (foldl-atom $pvec 0.0 $acc $pt $__t1) …) …)))
#     — `$acc`/`$pt` FREE, the fold TEMPLATE hoisted OUT and evaluated EAGERLY, and `foldl-atom`
#     handed a VALUE where it expects a TEMPLATE. ⇒ this "regression" turns silent WRONG ANSWERS
#     into safe DECLINES. Do not read a coverage drop here as a loss.
#
# ⚠️ SO COVERAGE % IS THE WRONG HEADLINE FOR THIS TOOL TOO. Read the composition, and check whether a
# decline is a MISSING CAPABILITY or a REFUSAL TO MIS-COMPILE.
#
# THE "27% COVERAGE" FIGURE WAS DOUBLY WRONG:
#   (1) WRONG CORPUS  — it is the 26 hyperon CONFORMANCE scripts (interpreter tests, deliberately
#       hard language edge cases), not the algorithm libraries we ship.
#   (2) WRONG ARROW   — `compiled=71 fell_back=192` is quoted off the corpus test, but the ranking
#       work it fed was aimed at `Emit.jl` (arrow 6, IL->MORK = DEPLOY/RUN). **Figure 2's COMPILE
#       arrow ENDS AT MeTTa-IL.** The compiler's number is EmitIL's, and on real code it is 95.5%.
#
# ⇒ "COMPILER PRIMARY" (standing directive, 4x) has been satisfied for a while and nobody measured it.
#   What remains on the compile arrow is 18 NAMED definitions, not a coverage programme.
#
# allow-new-artifact: preserves a measured survey; CODEMAP + whitepaper §3 consulted this session

using MeTTaCore
const MC = MeTTaCore
const CIL = MeTTaCore.CompilerEmitIL
const CF = MeTTaCore.CompilerFrontend
const AN = MeTTaCore.CompilerANormal
LIB = joinpath(dirname(pathof(MeTTaCore)), "..", "lib")
function clauses_for(sp, form)
    toks = MC.Eval.tokenize(form); i = Ref(1); out = MC.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
        push!(out, MC.Eval.parse_from(toks, i, sp.tokens))
    end
    prog = CF.lower_program(out); isempty(prog.definitions) && return nothing
    AN.translate_program(prog)
end
println("=== ARROWS 1-4 (THE COMPILE ARROW): what does EmitIL decline on the REAL libs? ===\n")
for lib in ["ecan","pln"]
    dir = joinpath(LIB, lib); sp = MC.Eval.Space(); MC.Eval.load_core_stdlib!(sp)
    ndef=0; ok=0; dec=0; err=0
    for f in sort(readdir(dir))
        endswith(f,".metta") || continue
        for form in MC._cs_split_top_level(read(joinpath(dir,f),String))
            startswith(strip(form),"(=") || continue
            ndef += 1
            try
                cls = clauses_for(sp, form)
                cls === nothing && (dec += 1; continue)
                r = CIL.emit_il_program(cls)
                (r.emitted == length(cls) && isempty(r.declined)) ? (ok += 1) : (dec += 1)
            catch e; err += 1 end
        end
    end
    pct = round(100*ok/max(ndef,1), digits=1)
    println("── ", rpad(lib,5), " defs=", ndef, "  COMPILE (EmitIL) ok=", ok,
            "  declined=", dec, "  raised=", err, "   => ", pct, "% of the real library COMPILES")
end
