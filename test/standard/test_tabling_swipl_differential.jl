# test_tabling_swipl_differential.jl — SWI §7.1 (memoizing) and §7.2 (non-termination),
# differentialled against a LIVE SWI-Prolog.
#
# ─── WHY ─────────────────────────────────────────────────────────────────────────────────────────
# The roadmap targets ALL of SWI manual §7, and §7.1/§7.2 are the two we claim to HAVE already. That
# claim rested on "fib returns 832040", which is not a comparison — it is one number matching one
# expectation. This file makes it a real differential: it RUNS `swipl` on the manual's own examples
# and asserts Core agrees. If SWI's answer changes, this goes red.
#
# Modelled on `test_wfs_swipl_differential.jl`, including both of its guards:
#   1. swipl absent ⇒ a LOUD `@test_skip` naming the reason, never a bare `return` (indistinguishable
#      from success in the summary).
#   2. swipl present but the parse yields nothing ⇒ a POSITIVE CONTROL asserts the expected shape
#      BEFORE any comparison, so a testset cannot read green having checked nothing.
#      `[[feedback_oracle_must_observe_the_defect_class]]`.
#
# ─── WHAT IS AND IS NOT COMPARED ─────────────────────────────────────────────────────────────────
# §7.1 is an exact VALUE comparison — both sides compute the same function N ↦ F (base cases
# fib(0)=0, fib(1)=1 on both, so the relation matches MeTTa's `(if (< $n 2) $n …)`).
#
# §7.2 is a TERMINATION property, and is asserted as such rather than as an answer-set comparison.
# The Prolog program is symmetric AND left-recursive, so it does not terminate under plain SLD; the
# oracle's 16-pair closure is recorded, but Core's relational encoding of the same graph is NOT
# clause-for-clause identical to Prolog's (MeTTa dispatches by `match`, Prolog by clause resolution),
# so an answer-SET equality here would be comparing two different programs. What IS comparable, and
# is what §7.2 exists to show, is that a LEFT-RECURSIVE tabled goal TERMINATES and answers.
#
# ⚠️ SET SEMANTICS IS EXPECTED ON BOTH SIDES, not a divergence to flag: tabling dedups by design
# everywhere (the delimited-control paper's `store_answer/2` "only store it in case it has not"; SWI
# structurally, via the answer trie). Where MeTTa's MULTISET semantics differs is roadmap 2.0, which
# is pinned by its own test — deliberately not re-litigated here.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

"Run a MeTTa program then one query on a fresh space, with `heads` tabled. Tabling state is global."
function _tab_run(
    prog::AbstractString, query::AbstractString, heads::Vector{Symbol}
)::Vector{Atom}
    Eval.untable_all!()
    s = Space()
    load_core_stdlib!(s)
    load_metta!(s, prog)
    for h in heads
        Eval.table!(h)
    end
    try
        load_metta!(s, query)
    finally
        Eval.untable_all!()
    end
end

"""Run `swipl -q <pl_file>` and parse `name(args) => value` lines into a Dict.

Returns an EMPTY dict on ANY failure (missing binary, non-zero exit, unparseable output) — the
caller's positive control turns that into a visible failure rather than a silent pass."""
function _swipl_pairs(pl_file::AbstractString)::Dict{String, String}
    out = Dict{String, String}()
    swipl = Sys.which("swipl")
    swipl === nothing && return out
    txt = try
        read(`$swipl -q $pl_file`, String)
    catch
        return out
    end
    for line in split(txt, '\n')
        m = match(r"^\s*([a-z_]+\([^)]*\))\s*=>\s*(\S+)\s*$", line)
        m === nothing && continue
        out[m.captures[1]] = m.captures[2]
    end
    out
end

const _TAB_ORACLE = normpath(joinpath(@__DIR__, "..", "oracle", "tabling"))

@testset "SWI §7.1 memoizing — LIVE differential vs SWI-Prolog" begin
    pl = joinpath(_TAB_ORACLE, "fib_71.pl")
    swipl = Sys.which("swipl")
    if swipl === nothing
        @test_skip "swipl NOT ON PATH — the §7.1 differential did not run. NOT a pass."
    elseif !isfile(pl)
        @test_skip "oracle missing: $pl — the §7.1 differential did not run. NOT a pass."
    else
        oracle = _swipl_pairs(pl)
        ns = [0, 1, 2, 5, 10, 20, 25, 30]

        # ── POSITIVE CONTROL: prove the oracle produced all 8 goals before trusting agreement.
        @test length(oracle) == length(ns)
        @test sort(collect(keys(oracle))) == sort(["fib($n)" for n in ns])

        prog = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n"
        for n in ns
            want = oracle["fib($n)"]
            got = _tab_run(prog, "!(fib $n)\n", [:fib])
            @test length(got) == 1
            @test string(got[1]) == want          # EXACT value agreement with SWI
        end
    end
end

@testset "SWI §7.2 avoiding non-termination — a LEFT-RECURSIVE tabled goal terminates" begin
    pl = joinpath(_TAB_ORACLE, "conn_72.pl")
    swipl = Sys.which("swipl")
    if swipl === nothing
        @test_skip "swipl NOT ON PATH — the §7.2 oracle did not run. NOT a pass."
    elseif !isfile(pl)
        @test_skip "oracle missing: $pl — the §7.2 oracle did not run. NOT a pass."
    else
        # POSITIVE CONTROL on the oracle: it must TERMINATE and report its closure size. Without
        # tabling this program does not finish at all, so a `count` line is itself the §7.2 property
        # holding on the Prolog side.
        oracle = _swipl_pairs(pl)
        @test haskey(oracle, "count()") || haskey(oracle, "count( )") ||
            any(startswith(k, "count") for k in keys(oracle)) ||
            begin  # the program prints `count => 16`, which has no parens — read it directly
                txt = read(`$swipl -q $pl`, String)
                occursin(r"count\s*=>\s*16", txt)
            end

        # ── CORE: the §7.2 SHAPE — a directly LEFT-RECURSIVE tabled rule. Untabled this cannot
        # terminate; tabled, suspend-on-variant must complete it and answer.
        prog = raw"""
(edge amsterdam schiphol)
(edge schiphol leiden)
(= (conn $x $y) (match &self (edge $x $y) True))
(= (conn $x $y) (conn $y $x))
""" * "\n"
        got = _tab_run(prog, "!(conn schiphol amsterdam)\n", [:conn])
        @test !isempty(got)                                   # TERMINATED and answered
        @test any(a -> string(a) == "True", got)              # …and the symmetric edge is found
    end
end
