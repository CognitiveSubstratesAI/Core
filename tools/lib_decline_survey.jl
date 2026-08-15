# lib_decline_survey.jl — decline classes on the REAL in-tree libraries, not the 26-script corpus.
#
# MEASURED 2026-08-15 (warm :7702). 398 definitions, ZERO front-end failures:
#
#   ECAN  115 defs   98 declining paths   146 clauses expanded by expand_control (35 here)
#         call_in_body 38/15   residual 33/33   mixed_arithmetic 17/8   structural_unify 9/3   control_flow 1/1
#   PLN   283 defs  181 declining paths   (111 expanded)
#         residual 61/57   structural_unify 42/11   mixed_arithmetic 39/24   call_in_body 38/17   control_flow 1/1
#                                                                            (paths/fully)
#
# 🔴 THIS INVERTS THE AIM. The 26-script conformance corpus gives call_in_body 27 / residual 24, and
# the scoped next step was a tail-call emitter change targeting call_in_body. On REAL libraries
# `residual` fully-unblocks 90 clauses (33 ECAN + 57 PLN) against call_in_body's 32 — and PLN's top
# class, structural_unify at #2, is not near the top of the corpus at all. `fully` is the aiming
# number (see Emit.jl:918): a clause blocked by TWO classes appears in NEITHER row, so fixing one
# class does not unblock it.
#
# ⚠️ DO NOT compute "compiling clauses" as total - sum(fully). That was in the first version of this
# script and it OVERCOUNTS, for exactly the reason above (multi-class clauses are in no `fully` row).
# decline_histogram does not return a declining-CLAUSE count; add one before quoting a coverage %.
#
# ⚠️ control_flow = 1 in both, with 146 clauses expanded, is `expand_control` working at scale —
# consistent with the corpus measurement (7 -> 0) that Emit.jl:918 records.
#
# Run: curl -s -X POST http://localhost:7702/julia --data-binary @Core/tools/lib_decline_survey.jl
#
# allow-new-artifact: preserves a measured survey; CODEMAP + spec consulted this session

using MeTTaCore
const MC = MeTTaCore
const CE = MeTTaCore.CompilerEmit
const CF = MeTTaCore.CompilerFrontend
const AN = MeTTaCore.CompilerANormal
LIB = joinpath(dirname(pathof(MeTTaCore)), "..", "lib")

# Mirror compile_definition's FRONT HALF (98-125) exactly, but keep the clauses instead of emitting.
function clauses_for(sp, form::AbstractString)
    toks = MC.Eval.tokenize(form); i = Ref(1)
    out = MC.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
        push!(out, MC.Eval.parse_from(toks, i, sp.tokens))
    end
    prog = CF.lower_program(out)
    isempty(prog.definitions) && return nothing
    AN.translate_program(prog)
end

function survey(name; show_first_error = true)
    dir = joinpath(LIB, name)
    files = sort([f for f in readdir(dir) if endswith(f, ".metta")])
    sp = MC.Eval.Space(); MC.Eval.load_core_stdlib!(sp)
    allcl = AN.ANClause[]; ndefs = 0; nfail = 0; firsterr = ""
    for f in files, form in MC._cs_split_top_level(read(joinpath(dir, f), String))
        startswith(strip(form), "(=") || continue
        ndefs += 1
        try
            cls = clauses_for(sp, form)
            cls === nothing ? (nfail += 1) : append!(allcl, cls)
        catch e
            nfail += 1
            if show_first_error && isempty(firsterr)
                firsterr = string(f, " :: ", first(strip(form), 90), "\n           -> ",
                                  typeof(e), ": ", first(sprint(showerror, e), 160))
            end
        end
    end
    println("── ", rpad(name, 6), " files=", length(files), "  defs=", ndefs,
            "  clauses=", length(allcl), "  front-end failures=", nfail)
    isempty(firsterr) || println("     first failure: ", firsterr)
    isempty(allcl) && return
    h = CE.decline_histogram(allcl)
    tot = sum(values(h.paths); init = 0)
    println("     declining paths=", tot, "  expanded=", h.expanded,
            "  COMPILING clauses=", length(allcl) - sum(values(h.fully); init = 0))
    println("     ", rpad("reason", 20), rpad("paths", 8), "fully")
    for k in sort(collect(keys(h.paths)), by = x -> -h.paths[x])
        println("     ", rpad(string(k), 20), rpad(string(h.paths[k]), 8), get(h.fully, k, 0))
    end
end

println("=== DECLINE CLASSES ON REAL IN-TREE LIBRARIES ===")
for n in ["ecan", "pln"]
    try survey(n) catch e
        println("── ", n, " RAISED ", typeof(e), ": ", first(sprint(showerror, e), 200))
    end
end
