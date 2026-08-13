# ============================================================================================
# `Core/lib` COMPILED-vs-INTERPRETED differential — the gate that did not exist.
#
# The three behavioural corpora (conformance, LeaTTa, metta-ref) cover `test/`, not `Core/lib`. But
# `lib` is the LARGEST body of compiled clauses — the coverage ratchet measures 360 of 888 clauses
# emitted there — and nothing asked whether those compiled clauses ANSWER the same as the interpreter.
# Coverage was measured; correctness was not.
#
# That gap has a known occupant: A-normalization hoists computations out of NON-STRICT argument
# positions (`docs/specs/binder_template_hoisting_defect.md`), which is a wrong answer, and 57 lib
# definitions using `foldl-atom`/`map-atom`/`filter-atom` compile today.
#
# WHY GENERATED QUERIES. `lib` is a LIBRARY: 71 of its 73 files contain no `!` directive at all, so
# there is nothing to run. Queries are therefore SYNTHESISED — each definition head called with fresh
# dummy symbols. The answers are often meaningless, and that is fine: this asserts LANE AGREEMENT, not
# correctness. A disagreement is a compiler bug whatever the answer means; an agreed-upon error is not.
#
# ⚠️ SCOPE, BOUNDED ON PURPOSE. Restricted to the files that use binder ops — the motivating risk — with
# a per-file query cap and a low step limit. An unbounded version OOM-killed a 7 GB warm server while
# being prototyped: a fresh stdlib-loaded space per query is expensive, and `lib` has 73 files.
# Widening this is a deliberate decision with a memory measurement attached, not a default.
# ============================================================================================

using Test
using MeTTaCore
const _LD_V = MeTTaCore.Eval
const _LD_SM = MeTTaCore.StandardMeTTa

const _LD_LIB = joinpath(@__DIR__, "..", "..", "lib")
const _LD_BINDER_OPS = ("foldl-atom", "map-atom", "filter-atom")
const _LD_MAX_STEPS = 2_000
const _LD_MAX_FILES = 3
const _LD_MAX_QUERIES_PER_FILE = 2

"Every `(= (name \$a \$b …) …)` head in `src`, as a call with fresh dummy arguments."
function _ld_synth_queries(src::AbstractString)::Vector{String}
    out = String[]
    for (bang, form) in MeTTaCore.mm2_split_forms(src)
        bang && continue
        m = match(r"^\(=\s+\((\S+)((?:\s+\$\S+)*)\)", replace(String(form), "\n" => " "))
        m === nothing && continue
        name = m.captures[1]
        occursin(r"[()]", name) && continue                     # compound head — not a plain call
        nargs = length(collect(eachmatch(r"\$\S+", m.captures[2])))
        push!(out, "(" * name * join([" d$i" for i in 1:nargs]) * ")")
    end
    unique(out)
end

# 🔴 BOTH LANES, BOTH CAPS — and there are TWO caps, which is what made this hang twice.
#
#     _METTA_MAX     (metta_max_steps!)      reduce chain            default 0 = UNLIMITED
#     _INTERPRET_MAX (interpret_max_steps!)  minimal `interpret` loop default 512_000
#
# `compile_run` sets `interpret_max_steps!(max_steps)` (CompileLane.jl:184). A first version of this
# file set `metta_max_steps!` on the interpreter side — THE OTHER ONE — so the interpreter still ran up
# to 512 000 minimal-machine steps on synthesised nonsense, and the file timed out at 560s twice.
# PHASE-TIMED to find it: per-query cost after JIT warmup is ~2 ms and `load_core_stdlib!` is ~1 ms, so
# the cost was never per-query — it was specific queries running to a bound I had not set.
#
# ⚠️ AND EQUAL FUEL IS A CORRECTNESS REQUIREMENT, not just a speed one: with different caps per lane a
# "disagreement" can be a fuel artifact rather than a compiler bug, which is precisely the false finding
# this gate exists to avoid producing.
function _ld_with_fuel(f)
    _LD_V.metta_max_steps!(_LD_MAX_STEPS)
    _LD_V.interpret_max_steps!(_LD_MAX_STEPS)
    try
        f()
    catch
        nothing                                                  # threw or hit a bound — "threw"
    finally
        _LD_V.metta_max_steps!(0)                                # restore the documented defaults
        _LD_V.interpret_max_steps!(512_000)
    end
end

_ld_interp(prog) = _ld_with_fuel() do
    sp = _LD_V.Space(); _LD_V.load_core_stdlib!(sp)
    sort(string.(_LD_V.load_metta!(sp, prog)))
end

_ld_compiled(prog) = _ld_with_fuel() do
    r = MeTTaCore.compile_run(prog; max_steps = _LD_MAX_STEPS)
    sort(vcat([a for (_, a) in r.answers]...))
end

# 🔴 MEASURED NON-TERMINATORS — skipped, with the reason, because THE STEP CAPS DO NOT BOUND THEM.
#
# `(chem-chain d1)` never returns under `metta_max_steps!(2000)` AND `interpret_max_steps!(2000)` set
# together — killed at 240 s by an external timeout. Its body is
#     (let $rules (collapse (match &self (ChemRule $p $r $w) …)) (foldl-atom $rules $data …))
# so the work happens inside GROUNDED collapse/match, where neither counter ticks: `_METTA_MAX` bounds
# the reduce chain and `_INTERPRET_MAX` the minimal machine, and grounded execution is under both.
#
# ⚠️ THE GENERAL LESSON, since this cost three timeouts before being found: OVER GENERATED INPUT, STEP
# CAPS ARE NOT A TERMINATION GUARANTEE. A curated corpus can assume well-behaved programs; a synthesiser
# cannot. Julia cannot safely interrupt in-process computation, so the honest options were an explicit
# skip list or a subprocess-per-query harness — this takes the skip list and names each entry.
#
# Found by println-tracing the loop: printing BEFORE each query (and flushing) made the hang name
# itself, where the previous two timeouts had produced no output at all.
const _LD_SKIP = Set{String}([
    "chemistry.metta (chem-chain d1)",
])

# 🔴 KNOWN DISAGREEMENTS — the defects this gate was built to make visible, pinned so it can run green
# while they stand. TWO-SIDED, like the wire ledger: an unlisted disagreement FAILS (a regression), and a
# listed one that stops appearing ALSO fails, so a fix cannot land silently.
#
# `boost-successful-rules!` was the FIRST query this differential ever ran, and it disagreed:
#     interp   ["done"]
#     compiled ["(foldl-atom ((Empty MeTTaCore.StandardMeTTa.Bindings(…"
# The compiled lane returns an UNREDUCED `foldl-atom` — and leaks internal Julia `Bindings` objects into
# a MeTTa answer, which is a second defect riding on the first. This is the binder-template hoisting
# diagnosed in `docs/specs/binder_template_hoisting_defect.md`, live in `Core/lib`, in a definition that
# compiles today. It is exactly what "57 definitions compile and nothing checks their answers" meant.
const _LD_KNOWN = Set{String}([
    "bridges.metta (boost-successful-rules! d1)",
])

@testset "Core/lib — compiled lane answers agree with the interpreter" begin
    files = String[]
    for (root, _, fs) in walkdir(_LD_LIB), f in fs
        endswith(f, ".metta") || continue
        p = joinpath(root, f)
        src = try read(p, String) catch; continue end
        any(b -> occursin(b, src), _LD_BINDER_OPS) && push!(files, p)
    end
    sort!(files)
    @test !isempty(files)                                        # anti-vacuity: the scan found targets

    observed = String[]; detail = String[]
    nq = 0; nboth_threw = 0
    for f in first(files, _LD_MAX_FILES)
        src = read(f, String)
        for q in first(_ld_synth_queries(src), _LD_MAX_QUERIES_PER_FILE)
            (basename(f) * " " * q) in _LD_SKIP && continue
            print("     … ", basename(f), " ", q, "\r"); flush(stdout)   # a hang names itself
            prog = src * "\n!" * q * "\n"
            i = _ld_interp(prog)
            c = _ld_compiled(prog)
            nq += 1
            if i === nothing && c === nothing
                nboth_threw += 1                                 # agreed failure is agreement
            elseif i != c
                push!(observed, basename(f) * " " * q)
                push!(detail,
                      basename(f) * " " * q * "\n      interp  : " * first(string(i), 110) *
                      "\n      compiled: " * first(string(c), 110))
            end
        end
    end

    println("\n  ── Core/lib differential: $(nq) synthesised queries over " *
            "$(min(length(files), _LD_MAX_FILES)) of $(length(files)) binder-op files ──")
    for d in first(detail, 6)
        println("     ", (split(d, "\n")[1] in _LD_KNOWN ? "•" : "✗"), " ", d)
    end
    isempty(detail) && println("     no disagreement")

    # ANTI-VACUITY. A differential that runs no queries, or whose every query throws on both sides,
    # proves nothing while reporting success — the exact failure this file exists to stop elsewhere.
    # Floor equals the MEASURED count (3 after the skip), not an aspiration. It should rise as the
    # skip list shrinks or the file cap grows — both of which need a termination story first.
    @test nq >= 3
    @test nboth_threw < nq

    # (1) nothing outside the ledger.
    unexpected = setdiff(Set(observed), _LD_KNOWN)
    for d in detail
        split(d, "\n")[1] in unexpected &&
            @info "NEW Core/lib LANE DISAGREEMENT — compiled answer differs from the interpreter" detail=d
    end
    @test isempty(unexpected)
    # (2) every ledgered disagreement STILL observed — a fix must update this deliberately.
    gone = setdiff(_LD_KNOWN, Set(observed))
    for g in gone
        @info "LEDGERED lib disagreement no longer observed — fixed, or no longer reached" query=g
    end
    @test isempty(gone)
end
