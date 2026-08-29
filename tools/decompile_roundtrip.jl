#!/usr/bin/env julia
# decompile_roundtrip.jl — the compile lane's STRUCTURAL oracle.
#
#   julia --project=. tools/decompile_roundtrip.jl [dir-or-file ...]
#
# For every `(= head body)` in the corpus: compile it with the live lane, decompile the emitted
# MeTTa-IL back to surface, and compare. Three outcomes, and only one of them is a defect:
#
#   EXACT       decompile(compile(P)) == P           string-identical, incl. variable NAMES
#   VARIANT     decompile(compile(P)) =@= P          same up to variable renaming — UPSTREAM'S CONTRACT
#   DECLINED    the inverse is not implemented       a COVERAGE number, not a failure
#   MISMATCH    it inverted, and got something else  🔴 structurally different
#
# ⚠️ THE COMPARISON IS `=@=`, NOT `==`, AND THAT IS UPSTREAM'S CHOICE, NOT A WEAKENING. Every one of
# SWI-Prolog's own decompiler tests compares with `=@=` (`tests/core/test_moved_ubody.pl`, testset
# `moved_decompile`, 10 tests) because a decompiler recovers STRUCTURE, never variable names. We
# happen to be exact today — the A-normal inverse substitutes producers back, so source names
# survive — so both numbers are reported and the stronger one is watched for regression.
#
# WHY THIS EXISTS: the corpus differential compares ANSWERS, so it is blind to a lowering that
# changes a clause's meaning while still answering correctly on the corpus's inputs. `EmitIL.jl`
# records three such defects in its own comments — the `eval`/`metta` confusion "survived a coverage
# ratchet, a corpus differential AND a fuzz differential" because "the shape is right, the values are
# wrong only in composition". This compares SHAPE, so it sees that class directly.
#
# 🔴 AND WHAT A MISMATCH MEANS IS NARROWER THAN "A DEFECT" — SWI PROVES IT. Its `decomp8` asserts
#     s7(X) :- X = f(A), q(A).      decompiles to      s7(f(A)) :- q(A).
# The compiler MOVED the unification into the head, so `clause/2` legitimately returns a clause that
# is not the source. `decompile ∘ compile ≡ id` therefore holds only for a STRUCTURE-PRESERVING
# lowering. Ours is one TODAY (EmitIL performs no such hoisting), which is why the gate asserts zero
# mismatches. If an optimization that moves work is ever added, a mismatch becomes EXPECTED and this
# oracle must be re-read as "the lowering is no longer structure-preserving" — not as a bug.
#
# EXIT CODE is the point (a piped `julia -i` always exits 0 — see tools/run_tests.sh): non-zero iff
# a MISMATCH exists. Declines never fail the run; they are printed as a histogram so the next piece
# of inverse work is chosen by measurement rather than by guess.

using MeTTaCore
const M = MeTTaCore
const D = MeTTaCore.CompilerDecompile

"Every `(= …)` definition in `path`, as parsed atoms. Non-definitions and `!` execs are skipped."
function definitions(path::AbstractString)::Vector{M.StandardMeTTa.Atom}
    out = M.StandardMeTTa.Atom[]
    text = try read(path, String) catch; return out end
    forms = try M.Eval.parse_program(text) catch; return out end
    for (is_exec, a) in forms
        is_exec && continue
        a isa M.StandardMeTTa.Expression || continue
        ch = (a::M.StandardMeTTa.Expression).children
        length(ch) == 3 || continue
        (ch[1] isa M.StandardMeTTa.Sym && (ch[1]::M.StandardMeTTa.Sym).name === :(=)) || continue
        push!(out, a)
    end
    out
end

function main(args::Vector{String})
    roots = isempty(args) ? ["test/oracle/leatta/corpus", "test/standard/conformance"] : args
    files = String[]
    for r in roots
        isdir(r) ? append!(files, sort([joinpath(r, f) for f in readdir(r) if endswith(f, ".metta")])) :
                   (isfile(r) && push!(files, r))
    end

    sp = M.Eval.Space()
    n_def = n_compiled = n_exact = n_variant = n_multi = 0
    mismatches = Tuple{String, String, String}[]     # (file, source, got)
    declines = Dict{String, Int}()

    for f in files
        for a in definitions(f)
            n_def += 1
            src = string(a)
            r = try M.compile_definition(sp, src) catch; nothing end
            r === nothing && continue
            n_compiled += 1
            # A source form may lower to SEVERAL clauses (`superpose` → one clause per branch). No
            # single clause can round-trip to the whole form then, so this is counted apart rather
            # than reported as a mismatch — that would be blaming the oracle for the lowering.
            if length(r.atoms) != 1
                n_multi += 1
                continue
            end
            d = D.decompile_clause(r.atoms[1])
            if D.declined(d)
                declines[d.reason] = get(declines, d.reason, 0) + 1
            elseif string(d.atom) == src
                n_exact += 1
            elseif M.Eval.variant_eq(d.atom::M.StandardMeTTa.Atom, a)
                # `=@=` — correct by upstream's contract, differing only in variable naming.
                n_variant += 1
            else
                push!(mismatches, (f, src, string(d.atom)))
            end
        end
    end

    println("═"^92)
    println("DECOMPILE ROUND-TRIP — ", length(files), " files")
    println("═"^92)
    println("  (=) definitions found      : ", n_def)
    println("  compiled by the lane       : ", n_compiled)
    println("  multi-clause (not 1:1)     : ", n_multi)
    inv = n_compiled - n_multi
    println("  invertible candidates      : ", inv)
    good = n_exact + n_variant
    pct = inv == 0 ? 0.0 : round(100 * good / inv; digits=1)
    println("  ✅ ROUND-TRIPPED (=@=)     : ", good, "  (", pct, "% of candidates)")
    println("       of which EXACT (==)   : ", n_exact)
    println("       of which VARIANT only : ", n_variant, "  (upstream's contract; SWI compares =@=)")
    println("  🔴 MISMATCH                : ", length(mismatches))

    if !isempty(declines)
        println("\n  DECLINED — where the next inverse work is, ranked by frequency:")
        for (why, k) in sort(collect(declines); by=last, rev=true)
            println("    ", lpad(k, 5), "  ", why)
        end
    end
    if !isempty(mismatches)
        println("\n  🔴 MISMATCHES (a defect in EmitIL or Decompile — NOT a coverage gap):")
        for (f, s, g) in mismatches
            println("    ", f); println("      src ", s); println("      got ", g)
        end
    end
    println("═"^92)
    exit(isempty(mismatches) ? 0 : 1)
end

main(String[a for a in ARGS])
