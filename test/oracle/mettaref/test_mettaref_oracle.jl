# ============================================================================================
# MeTTapedia `metta-ref` differential — a THIRD corpus, chosen for what our other two do not cover.
#
# Source: MeTTapedia (github.com/…/MeTTapedia, MIT, vendored from `~/JuliaAGI/dev-zone/MeTTapedia`
# @ 23bede4e), subtree `cakeml/metta-ref` — a HOL4 specification of MeTTa "M1" with an SML reference
# interpreter (`sml/metta_m1.sml`) and a curated test set.
#
# WHY THIS CORPUS AND NOT THE REST OF MeTTapedia. The flagship Lean library is a formal-mathematics
# development (probability, PLN, AIXI); it cannot state, let alone check, the properties our compiler
# gets wrong — those are about our own representations agreeing with each other. What `metta-ref` has
# that theory does not is EXECUTABLE CASES, and its 24 files have ZERO filename overlap with either
# corpus we already run. Fourteen of them are `nondet_*_bag` — superpose / collapse / chain / case /
# switch / let* / match nondeterminism, which is precisely where the compile lane is thinnest: the
# `eval`-vs-`metta` choice in `EmitIL._instr(::GCall)`, the `collapse` wrapper, and chain sequencing
# are all nondeterminism-shaped. A proved oracle only guarantees what its corpus exercises, so new
# coverage in our weakest area beats more theory over the areas already covered.
#
# TWO HALVES, DIFFERENT STRENGTHS — kept apart because they license different conclusions:
#
#   `curated/` (4 files)  — ships `.expected` GOLDENS produced by the HOL4-specified M1 reference
#       (`tests/run_metta_file.sml`). An EXTERNAL oracle: a disagreement is evidence about US.
#   `cetta_selected/` (20 files) — no goldens. Run as a COMPILED-vs-INTERPRETED differential, the same
#       contract as `test_compile_lane_corpus.jl`: the compiled lane may not do worse than the
#       interpreter on the same script. That is a self-consistency check, NOT an oracle, and it is
#       labelled as such below so a green run is not over-read.
#
# 🔴 STRUCTURAL COMPARISON, NOT TEXT DIFFING. The goldens are text (`[b]`, `[(pair hello hello)]`) and
# `test/oracle/leatta/README.md` records why freezing an oracle's OUTPUT and string-diffing it is a
# trap: it fails on render-format differences (quoting, Float-vs-Int, variable alpha-renaming) that are
# not semantic disagreements. So both sides are PARSED into atoms and compared structurally. This
# session supplied a fresh reason to distrust rendered text as an equality witness — `show` turned out
# to be lossy for grounded strings, `Space` and `StateCell` alike.
# ============================================================================================

using Test
using MeTTaCore
const _MR_V = MeTTaCore.Eval
const _MR_SM = MeTTaCore.StandardMeTTa

const _MR_CURATED = joinpath(@__DIR__, "curated")
const _MR_SELECTED = joinpath(@__DIR__, "cetta_selected")
const _MR_MAX_STEPS = 40_000

"Parse a golden line — `[b]`, `[(pair hello hello)]` — into the atoms it denotes."
function _mr_parse_expected(line::AbstractString)::Vector{_MR_SM.Atom}
    s = strip(line)
    (startswith(s, "[") && endswith(s, "]")) ||
        error("golden line is not a bracketed bag: $(repr(line))")
    inner = strip(s[nextind(s, 1):prevind(s, lastindex(s))])
    # ⚠️ FAILS LOUDLY on a separator this has never seen. Every golden in the vendored set is a
    # single-result bag, so the multi-result separator the M1 printer uses is UNOBSERVED. Guessing it
    # would silently mis-parse the first multi-result golden that arrives; this stops instead.
    occursin(",", inner) &&
        error(
            "golden bag appears comma-separated — the separator was never observed when this " *
            "was written; confirm M1's printer and extend `_mr_parse_expected`: $(repr(line))"
        )
    isempty(inner) && return _MR_SM.Atom[]
    sp = _MR_V.Space()
    toks = _MR_V.tokenize(String(inner))
    i = Ref(1)
    out = _MR_SM.Atom[]
    while i[] <= length(toks)
        push!(out, _MR_V.parse_from(toks, i, sp.tokens))
    end
    out
end

"Run each `!`-directive of `src` separately, returning one result-bag per directive."
function _mr_run_directives(src::AbstractString)::Vector{Vector{_MR_SM.Atom}}
    sp = _MR_V.Space()
    _MR_V.load_core_stdlib!(sp)
    bags = Vector{_MR_SM.Atom}[]
    for (bang, form) in MeTTaCore.mm2_split_forms(src)
        if bang
            push!(bags, _MR_V.load_metta!(sp, "!" * form))
        else
            _MR_V.load_metta!(sp, form)
        end
    end
    bags
end

@testset "metta-ref curated goldens — HOL4-specified M1 reference as EXTERNAL oracle" begin
    files = sort([f for f in readdir(_MR_CURATED) if endswith(f, ".metta")])
    @test length(files) == 4                      # the corpus is intact, not silently shrunk

    mismatches = String[]
    ndirectives = 0
    for name in files
        src = read(joinpath(_MR_CURATED, name), String)
        golden = filter(
            !isempty,
            strip.(
                split(
                    read(joinpath(_MR_CURATED,
                            replace(name, ".metta" => ".expected")), String), '\n')
            )
        )
        got = _mr_run_directives(src)
        if length(got) != length(golden)
            push!(
                mismatches,
                "$name: $(length(got)) directives ran, $(length(golden)) goldens"
            )
            continue
        end
        for (k, (bag, line)) in enumerate(zip(got, golden))
            ndirectives += 1
            want = _mr_parse_expected(line)
            # Order-insensitive: a result BAG is a multiset. M1 prints in its own evaluation order and
            # a different order is not a disagreement about values.
            if sort(string.(bag)) != sort(string.(want))
                push!(mismatches, "$name #$k: got $(string.(bag)) want $(string.(want))")
            end
        end
    end
    for m in mismatches
        @info "METTA-REF ORACLE DISAGREEMENT — evidence about Core, not a formatting difference" detail=m
    end
    @test isempty(mismatches)
    @test ndirectives >= 6        # anti-vacuity: directives actually ran and were compared
end

@testset "metta-ref cetta_selected — compiled lane vs interpreter, ANSWER BAGS (self-consistency)" begin
    files = sort([f for f in readdir(_MR_SELECTED) if endswith(f, ".metta")])
    @test length(files) == 20

    # 🔴 COMPARES THE BAGS, NOT THE ERROR COUNTS. The first version of this testset asserted only
    # "the compiled lane raises no more errors than the interpreter" — the contract
    # `test_compile_lane_corpus.jl` uses. On THIS corpus that is close to vacuous: every script here is
    # nondeterministic and error-free in both lanes (measured: 0 → 0 on all twenty), so a lane that
    # returned the WRONG BAG — dropped a branch of a `superpose`, collapsed in the wrong order, lost a
    # `case` alternative — would have passed silently. The whole reason to adopt this corpus is bag
    # semantics, so the test has to be able to SEE a bag difference.
    worse = String[]
    total_compiled = 0
    total_fell_back = 0
    ncompared = 0
    nonempty = 0
    println(
        "\n  ── metta-ref nondeterminism corpus (compiled / fell-back · bags compared) ──"
    )
    for name in files
        src = read(joinpath(_MR_SELECTED, name), String)
        print("     … $name\r")
        flush(stdout)
        interp = try
            [sort(string.(bag)) for bag in _mr_run_directives(src)]
        catch e
            push!(worse, "$name: interpreter threw $(first(sprint(showerror, e), 70))")
            continue
        end
        got = try
            MeTTaCore.compile_run(src; max_steps=_MR_MAX_STEPS)
        catch e
            push!(worse, "$name: compiled lane threw $(first(sprint(showerror, e), 70))")
            continue
        end
        total_compiled += got.compiled
        total_fell_back += got.fell_back
        comp = [sort(collect(answers)) for (_, answers) in got.answers]
        agree =
            length(comp) == length(interp) &&
            all(comp[k] == interp[k] for k in eachindex(comp))
        ncompared += min(length(comp), length(interp))
        nonempty += count(!isempty, interp)
        println(
            "     $(agree ? " " : "✗") $(rpad(name, 38)) $(lpad(got.compiled, 3))/$(lpad(got.fell_back, 3))" *
            "   bags=$(length(interp))" * (agree ? "" : "   interp=$interp compiled=$comp")
        )
        flush(stdout)
        agree || push!(worse, "$name: interp $interp vs compiled $comp")
    end
    for w in worse
        @info "metta-ref BAG DEVIATION" detail=w
    end
    @test isempty(worse)
    println(
        "     TOTAL compiled=$total_compiled  fell_back=$total_fell_back  bags compared=$ncompared"
    )
    # ANTI-VACUITY, both directions: bags were actually compared, and they are not all empty (an
    # evaluator that returned nothing for everything would otherwise "agree" with itself).
    @test ncompared >= 20
    @test nonempty >= 15
end
