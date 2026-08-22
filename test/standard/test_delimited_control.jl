# Delimited control over the CPS frame chain — tabling roadmap §1.0, step 1 of 4.
#
# WHAT THIS GATES. Desouter et al. (TPLP 2015) implement tabling in 577 Prolog lines of which the
# delimited-control CONTROL FLOW is 60 (§5.1, Table 1); the other 85% is tries and dequeues Prolog
# lacks and Julia supplies. `Continuation`/`capture_continuation`/`resume_continuation` are that 60,
# and this file is their oracle. The engine move they enable — replacing `_leader_pass`'s RECOMPUTATION
# (the "extension table" design the paper names and rejects) with dependency-driven RESUMPTION — is
# what 7.7 incremental, 7.8 monotonic and 7.11 restraints all need structures for.
#
# ⚠️ WHAT THIS DOES *NOT* CLAIM. Nothing here is wired into `tabled_eval` yet: the primitives are
# tested standalone, driving `interpret_stack` from outside exactly as the feasibility probe did.
# A green file means capture-and-resume is sound on this machine, NOT that tabling uses it.
#
# 🔴 AND IT IS NOT A FIX FOR ROADMAP 2.0. Tabling collapses multiplicity because tabling is
# SET-SEMANTICS BY DESIGN in every implementation (this paper dedups in `store_answer/2` §4.4; SWI
# dedups structurally via the answer trie). That is a language-level mismatch — tabling is set, MeTTa
# is multiset — and moving the base does not touch it. Claimed once, retracted 2026-08-16; the
# multivalued guard is still owed after this lands.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _DC = Eval

_dc_parse(src::AbstractString, sp) =
    (toks=_DC.tokenize(src); _DC.parse_from(toks, Ref(1), sp.tokens))
_dc_root(goal::Atom) = Tuple{_DC.Frame, _DC.Bindings}[
    (
    _DC.Frame(goal, _DC.collect_vars(goal), nothing, _DC.no_handler, false, 0),
    _DC.Bindings()
)]
_dc_show(rs) = sort!(String[string(_DC.subst(a, b)) for (a, b) in rs])

# Drive the machine, but SUSPEND at `(metta (mark …) …)` — the literal `shift/1`: yield control,
# capture the remainder, produce no answer. Returns (results-that-still-finished, continuations).
function _dc_run_capturing(goal::Atom, space)
    plan = _dc_root(goal)
    caught = _DC.Continuation[]
    out = Tuple{Atom, _DC.Bindings}[]
    while !isempty(plan)
        f, fb = pop!(plan)
        if !f.finished && f.atom isa Expression &&
            length((f.atom::Expression).children) >= 2 &&
            (f.atom::Expression).children[1] == Sym("metta")
            g = (f.atom::Expression).children[2]
            if g isa Expression && !isempty(g.children) && g.children[1] == Sym("mark")
                push!(caught, _DC.capture_continuation(fb, f.prev, g))
                continue
            end
        end
        for (nf, nb) in _DC.interpret_stack(f, fb, space)
            if (nf.finished && nf.prev === nothing)
                push!(out, (nf.atom, nb))
            else
                push!(plan, (nf, nb))
            end
        end
    end
    (out, caught)
end

@testset "delimited control — capture and resume over the CPS frame chain (§1.0)" begin

    # ── `_run_plan` is THE driver, and `interpret` is a seed on top of it ────────────────────────
    # Extraction guard: if someone re-inlines the loop into `interpret`, `resume_continuation` silently
    # stops observing the step cap and the diagnostic counter. Assert the two agree on a real program.
    @testset "one driver: interpret === _run_plan(root seed)" begin
        s = Space()
        load_core_stdlib!(s)
        load_metta!(s, raw"(= (tw $x) (T $x))")
        goal = _DC._metta(_dc_parse("(tw q)", s), _DC.UNDEF)
        @test _dc_show(_DC.interpret(goal, s)) == _dc_show(_DC._run_plan(_dc_root(goal), s))
        @test _dc_show(_DC.interpret(goal, s)) == ["(T q)"]      # anti-vacuity: it actually reduced
    end

    # ── the core property: ONE continuation, resumed once per answer ─────────────────────────────
    @testset "capture once, resume per answer — the dependency mechanism" begin
        s = Space()
        load_core_stdlib!(s)
        load_metta!(s, raw"(= (g $x) (Result $x))  (= (mark) M1)  (= (mark) M2)")
        goal = _DC._metta(_dc_parse("(g (mark))", s), _DC.UNDEF)

        baseline = _dc_show(_DC.interpret(goal, s))
        @test baseline == ["(Result M1)", "(Result M2)"]

        (partial, caught) = _dc_run_capturing(goal, s)
        @test length(caught) == 1                  # exactly one suspension point
        @test isempty(partial)                     # shift produces NO answer (§4.2)
        @test caught[1].prev !== nothing           # a real pending chain was captured
        @test caught[1].goal == _dc_parse("(mark)", s)

        # RE-ENTRANT: the same Continuation is resumed twice, because a dependency fires on every new
        # answer of its source table. This is the property the whole base move rests on.
        c = caught[1]
        resumed = String[]
        for ans in (Sym("M1"), Sym("M2"))
            append!(resumed, _dc_show(_DC.resume_continuation(c, ans, s)))
        end
        @test sort!(resumed) == baseline

        # ANTI-VACUITY: resumption must USE its answer. A `resume` that ignored the argument, or that
        # replayed a memo, would pass every assertion above.
        @test _dc_show(_DC.resume_continuation(c, Sym("ZZZ"), s)) == ["(Result ZZZ)"]
        # …and resuming a THIRD time still works — capture is not consumed by use.
        @test _dc_show(_DC.resume_continuation(c, Sym("M1"), s)) == ["(Result M1)"]
    end

    # ── the captured bindings are ISOLATED from the resumptions ─────────────────────────────────
    # Not load-bearing on today's single-threaded engine (`merge_bindings` trail-undoes its in-place
    # fold on every exit path, `Atoms.jl:224-252`) — asserted anyway because roadmap 7.9 shared
    # tabling is IN SCOPE, and under threading a live capture sits inside that trail window.
    @testset "capture copies its Bindings — entries unchanged across resumptions" begin
        s = Space()
        load_core_stdlib!(s)
        load_metta!(
            s, raw"(= (g (F $x)) (Result $x))  (= (mark) (F M1))  (= (mark) (F M2))"
        )
        goal = _DC._metta(_dc_parse("(g (mark))", s), _DC.UNDEF)
        (_, caught) = _dc_run_capturing(goal, s)
        @test length(caught) == 1
        c = caught[1]
        before = length(c.b.entries)
        for ans in (_dc_parse("(F M1)", s), _dc_parse("(F M2)", s))
            @test _dc_show(_DC.resume_continuation(c, ans, s)) ==
                ["(Result " * string((ans::Expression).children[2]) * ")"]
        end
        @test length(c.b.entries) == before        # the capture was not extended by either resume
    end

    # ── the Dependency record (§4.2) ────────────────────────────────────────────────────────────
    @testset "Dependency carries source, continuation and target" begin
        s = Space()
        load_core_stdlib!(s)
        load_metta!(s, raw"(= (g $x) (Result $x))  (= (mark) M1)")
        goal = _DC._metta(_dc_parse("(g (mark))", s), _DC.UNDEF)
        (_, caught) = _dc_run_capturing(goal, s)
        src = _dc_parse("(mark)", s)
        tgt = _dc_parse("(g (mark))", s)
        d = _DC.Dependency(src, caught[1], tgt)
        @test d.source == src
        @test d.target == tgt
        @test _dc_show(_DC.resume_continuation(d.cont, Sym("M1"), s)) == ["(Result M1)"]
        # the store is keyed by SOURCE — a new answer there is what fires the dependency
        empty!(_DC._DEPS)
        push!(get!(_DC._DEPS, d.source, _DC.Dependency[]), d)
        @test length(_DC._DEPS[src]) == 1
        _DC._table_reset!()
        @test isempty(_DC._DEPS)                   # reset clears it with the rest of the tabling state
    end
end
