# test_aggregation.jl — mode-directed tabling (SWI §7.3) differentialled against a LIVE SWI-Prolog.
#
# ─── SCOPE, STATED UP FRONT ──────────────────────────────────────────────────────────────────────
# This compares AGGREGATION SEMANTICS, not an end-to-end tabled query. `Aggregation.jl` is not yet
# wired into `tabled_eval`'s merge point — that merge point is §1.0's `tabled_eval` rewire, in
# progress separately. So the differential feeds our `merge_answers` the SAME derivation multiset
# the Prolog program produces and asserts the AGGREGATED RESULT matches what swipl computed.
#
# A green file therefore means: given the same answers, our lattice/po folding agrees with upstream.
# It does NOT mean MeTTa can run `:- table path(_,_,min)` yet. `[[feedback_report_green_against_the_arrow_not_the_test_list]]`
#
# Guards carried over from the §7.1/§7.2 differential, for the same reasons:
#   1. swipl absent ⇒ a LOUD `@test_skip` naming the reason, never a bare `return`.
#   2. a POSITIVE CONTROL asserts the oracle produced every expected goal BEFORE any comparison, so
#      the testset cannot read green having compared nothing.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _AG = Eval

"Parse `name(args) => value` lines from a swipl run. Empty dict on ANY failure — the positive
control below turns that into a visible failure rather than a silent pass."
function _agg_pairs(pl_file::AbstractString)::Dict{String,String}
    out = Dict{String,String}()
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

const _AGG_ORACLE = normpath(joinpath(@__DIR__, "..", "..", "oracle", "tabling", "modes_73.pl"))

_mode(spec::Atom) = _AG.parse_mode(spec)
_idx()  = _mode(Sym(:index))
_ans(head::Symbol, key::Symbol, v) = Expression(Atom[Sym(head), Sym(key), Grounded(v)])

"Fold `vals` (the derivations upstream produced for one key) under `modes`, return the value slot."
function _fold(head::Symbol, key::Symbol, vals::Vector, modes::Vector{<:_AG.TableMode})
    answers = Atom[]
    for v in vals
        answers, _ = _AG.merge_answers(answers, Atom[_ans(head, key, v)], modes)
    end
    length(answers) == 1 || return nothing
    a = answers[1]
    (a isa Expression && length((a::Expression).children) == 3) || return nothing
    (a::Expression).children[3]
end

@testset "SWI §7.3 mode-directed tabling — LIVE differential vs SWI-Prolog" begin
    swipl = Sys.which("swipl")
    if swipl === nothing
        @test_skip "swipl NOT ON PATH — the §7.3 differential did not run. NOT a pass."
    elseif !isfile(_AGG_ORACLE)
        @test_skip "oracle missing: $_AGG_ORACLE — the §7.3 differential did not run. NOT a pass."
    else
        oracle = _agg_pairs(_AGG_ORACLE)

        # ── POSITIVE CONTROL: every goal must be present before any agreement is claimed.
        want = ["path(a,b)", "path(a,c)", "path(a,d)", "tot(k)", "tot(m)", "best(k)", "keep(k)"]
        @test sort(collect(keys(oracle))) == sort(want)

        # ── lattice(min): the shortest-path example. a→c derives 9 directly and 3 via b; upstream
        # keeps 3, which is the whole point of §7.3 — the direct edge is subsumed.
        @test _fold(:path, :c, [9, 3], _AG.TableMode[_idx(), _mode(Sym(:min))]) ==
              Grounded(parse(Int, oracle["path(a,c)"]))
        @test _fold(:path, :b, [1],    _AG.TableMode[_idx(), _mode(Sym(:min))]) ==
              Grounded(parse(Int, oracle["path(a,b)"]))
        @test _fold(:path, :d, [10, 4], _AG.TableMode[_idx(), _mode(Sym(:min))]) ==
              Grounded(parse(Int, oracle["path(a,d)"]))

        # ── lattice(sum): 1+2+4 on key k, and a single derivation on key m.
        @test _fold(:tot, :k, [1, 2, 4], _AG.TableMode[_idx(), _mode(Sym(:sum))]) ==
              Grounded(parse(Int, oracle["tot(k)"]))
        @test _fold(:tot, :m, [10],      _AG.TableMode[_idx(), _mode(Sym(:sum))]) ==
              Grounded(parse(Int, oracle["tot(m)"]))

        # ── lattice(max)
        @test _fold(:best, :k, [1, 2, 4], _AG.TableMode[_idx(), _mode(Sym(:max))]) ==
              Grounded(parse(Int, oracle["best(k)"]))

        # ── po(leq/2): upstream expands to `(Call -> S2 = S0 ; S2 = S1)`, i.e. KEEP THE STORED value
        # when the test holds. Getting that branch backwards yields `last` and still type-checks.
        @test _fold(:keep, :k, [1, 2, 4],
                    _AG.TableMode[_idx(), _mode(Expression(Atom[Sym(:po), Sym(:leq)]))]) ==
              Grounded(parse(Int, oracle["keep(k)"]))
    end
end

@testset "§7.3 port details that no oracle line would catch" begin
    # ── 🔴 THE FIXPOINT CATCH the roadmap recorded. An aggregating merge changes a VALUE while
    # leaving the COUNT fixed, so `Tabling.jl`'s `length(_PARTIAL[m]) != n0` test reports "no growth"
    # and the completion loop terminates early with a half-aggregated table. `merge_answers` returns
    # `changed` computed from values for exactly this reason; assert the two DISAGREE here, because
    # a test that only checked `changed == true` would pass even on a cardinality implementation.
    ms = _AG.TableMode[_idx(), _mode(Sym(:sum))]
    before, _   = _AG.merge_answers(Atom[], Atom[_ans(:p, :k, 1)], ms)
    after, chg  = _AG.merge_answers(before, Atom[_ans(:p, :k, 2)], ms)
    @test length(after) == length(before)      # cardinality: NO growth
    @test chg                                   # value: CHANGED — the disagreement is the point
    @test after[1] == _ans(:p, :k, 3)

    # ── min/max are on the STANDARD ORDER (`@<`/`@>`), not numeric `<`, so they are total over
    # arbitrary terms. A numeric implementation throws here instead of ordering.
    symmodes = _AG.TableMode[_idx(), _mode(Sym(:min))]
    got, _ = _AG.merge_answers(Atom[Expression(Atom[Sym(:q), Sym(:k), Sym(:zed)])],
                               Atom[Expression(Atom[Sym(:q), Sym(:k), Sym(:alpha)])], symmodes)
    @test got == Atom[Expression(Atom[Sym(:q), Sym(:k), Sym(:alpha)])]

    # ── the standard-order ladder itself: Var @< Number @< String @< Atom @< Term (pl-prims.c:1788).
    xs = Atom[Expression(Atom[Sym(:f), Sym(:a)]), Sym(:zed), Grounded("s"), Grounded(3), Var("x", UInt64(1))]
    @test sort(xs, lt=_AG.std_lt) ==
          Atom[Var("x", UInt64(1)), Grounded(3), Grounded("s"), Sym(:zed), Expression(Atom[Sym(:f), Sym(:a)])]
    @test _AG.std_lt(Grounded(1.0), Grounded(1))        # equal value ⇒ FLOAT first (pl-prims.c:1777)
    # compounds compare on ARITY before name — a name-first implementation disagrees here.
    @test _AG.std_lt(Expression(Atom[Sym(:z), Sym(:a)]), Expression(Atom[Sym(:a), Sym(:a), Sym(:b)]))

    # ── an all-`index` declaration must be a NO-OP, degrading to plain set semantics.
    noagg = _AG.TableMode[_idx(), _idx()]
    @test !_AG.has_aggregation(noagg)
    kept, _ = _AG.merge_answers(Atom[_ans(:p, :a, 1)], Atom[_ans(:p, :a, 2), _ans(:p, :a, 1)], noagg)
    @test kept == Atom[_ans(:p, :a, 1), _ans(:p, :a, 2)]

    # ── an unknown mode is a DOMAIN ERROR (boot/tabling.pl:1512), never a silent fallback to index —
    # a mistyped mode that quietly becomes a key argument reads as "aggregation did nothing".
    @test_throws ArgumentError _AG.parse_mode(Sym(:bogus))
    @test_throws ArgumentError _AG.parse_mode(Expression(Atom[Sym(:lattice), Sym(:nosuch)]))
end
