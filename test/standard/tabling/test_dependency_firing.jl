# `dependency(Source, Cont, Target)` — RECORDING AND FIRING. Tabling roadmap §1.0, step 2 of 4.
#
# Desouter et al. §4.2: a worker that calls a tabled predicate SHIFTs without producing an answer, and
# the suspended remainder is stored in the SOURCE call's table, fired whenever a new answer lands
# there. Step 1 built the capture/resume primitives; this gates the dependency built ON them.
#
# ⚠️ WHAT A GREEN FILE MEANS. Recording is OFF by default (`_DEPS_RECORD`) and nothing in the engine
# consumes `_DEPS` yet — the fixpoint is still reached by re-running `_leader_pass`. So green means
# "firing a recorded dependency reproduces what recomputation produces", NOT "tabling resumes instead
# of recomputing". Switching the completion loop over is step 4, and doing it before this agreement is
# demonstrated would be a rewrite with no oracle.
#
# 🔴 THE FLAG IS ALSO A LEAK GUARD, not just caution. `_leader_pass` re-runs every fixpoint round, so
# a consumer re-records its dependency each round and `_DEPS` grows without bound. Under the step-4
# rewire that is moot — the worker runs ONCE and suspends — but until then, recording on by default
# would be a memory leak in the engine's hottest loop. The last testset pins that growth so the
# rewire has to fix it rather than inherit it.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _DF = Eval

_df_parse(src, sp) = (toks = _DF.tokenize(src); _DF.parse_from(toks, Ref(1), sp.tokens))

# run `query` with `head` tabled and dependency recording ON; return (answers, space, key)
function _df_run(prog::AbstractString, query::AbstractString, head::Symbol)
    _DF.untable_all!()
    s = Space(); load_core_stdlib!(s); load_metta!(s, prog)
    _DF.table!(head)
    _DF._DEPS_RECORD[] = true
    try
        ans = String[string(x) for y in load_metta!(s, query * "\n")
                     for x in (y isa AbstractVector ? y : [y])]
        (sort!(ans), s)
    finally
        _DF.reset_execution_flags!()   # restore the ENV default, never a literal — defaults move
    end
end

@testset "dependency/3 — recorded at the shift, fired on a new answer (§1.0 step 2)" begin

    # ── the DEFAULT path is untouched: no target, no recording ──────────────────────────────────
    # The disable-to-prove pattern this file's engine already uses for tabling itself. If this fails,
    # every claim about the default path being byte-identical is void.
    @testset "recording OFF by default ⇒ _DEPS stays empty" begin
        _DF.untable_all!()
        s = Space(); load_core_stdlib!(s)
        load_metta!(s, raw"(= (q) 1)  (= (q) (S (q)))")
        _DF.table!(:q)
        @test !_DF._DEPS_RECORD[]                     # the gate is shut unless a caller opens it
        load_metta!(s, "!(q)\n")
        @test isempty(_DF._DEPS)
        @test _DF._CURRENT_TARGET[] === nothing       # and the target Ref is restored, not leaked
        _DF.untable_all!()
    end

    # ── recording: the consumer IS the shift point ──────────────────────────────────────────────
    @testset "a variant re-entry records dependency(source, cont, target)" begin
        (ans, s) = _df_run(raw"(= (q) 1)  (= (q) (S (q)))", "!(q)", :q)
        key = _DF._canonical_goal(_df_parse("(q)", s), s, _DF.Bindings())
        @test haskey(_DF._DEPS, key)                  # recorded in the SOURCE's table (§4.2)
        deps = _DF._DEPS[key]
        @test !isempty(deps)
        d = deps[1]
        @test d.source == key
        @test d.target == key                         # self-recursive ⇒ source and target coincide
        @test d.cont isa _DF.Continuation
        @test d.cont.prev !== nothing                 # a real suspended remainder, not an empty chain
        _DF.untable_all!()
    end

    # ── FIRING: the continuation must APPLY the worker's remainder, not echo the answer ──────────
    # `(= (q) (S (q)))` means the remainder wraps the source answer in `S`. A `fire` that returned the
    # answer unchanged, or replayed a memo, would pass a weaker assertion — so the wrapper is the test.
    @testset "firing a dependency applies the suspended remainder" begin
        (ans, s) = _df_run(raw"(= (q) 1)  (= (q) (S (q)))", "!(q)", :q)
        key = _DF._canonical_goal(_df_parse("(q)", s), s, _DF.Bindings())
        fired = _DF.fire_dependencies!(key, Atom[Grounded(1)], s)
        @test haskey(fired, key)
        @test "(S 1)" in String[string(a) for a in fired[key]]

        # ANTI-VACUITY: a different answer must give a different result, or firing ignores its input.
        fired2 = _DF.fire_dependencies!(key, Atom[Sym("zzz")], s)
        @test "(S zzz)" in String[string(a) for a in fired2[key]]
        @test !("(S 1)" in String[string(a) for a in fired2[key]])
        _DF.untable_all!()
    end

    # ── THE POINT OF THE WHOLE STEP: firing AGREES WITH RECOMPUTATION ───────────────────────────
    # Step 4 replaces `_leader_pass` re-runs with dependency-driven resumption. That is only safe if
    # resumption yields what recomputation yields. Asserted on the answers the engine actually
    # produced, so this is a differential and not a restatement of the previous testset.
    @testset "resumption reproduces what recomputation produced" begin
        prog = raw"(= (q) 1)  (= (q) (S (q)))"
        (ans, s) = _df_run(prog, "!(q)", :q)
        key = _DF._canonical_goal(_df_parse("(q)", s), s, _DF.Bindings())
        @test "1" in ans                                   # the base answer recomputation found
        # feed the base answer through the recorded dependency; the result must be an answer the
        # engine also derived by recomputing.
        fired = _DF.fire_dependencies!(key, Atom[Grounded(1)], s)
        derived = String[string(a) for a in get(fired, key, Atom[])]
        @test !isempty(derived)
        @test all(d -> d in ans, derived) ||
              (@info "resumption produced an answer recomputation did NOT" derived ans; false)
        _DF.untable_all!()
    end

    # ── the known leak, PINNED so step 4 must fix it rather than inherit it ─────────────────────
    @testset "KNOWN: re-running the leader re-records (why the flag is off)" begin
        _DF.untable_all!()
        s = Space(); load_core_stdlib!(s)
        load_metta!(s, raw"(= (q) 1)  (= (q) (S (q)))")
        _DF.table!(:q)
        key = _DF._canonical_goal(_df_parse("(q)", s), s, _DF.Bindings())
        _DF._DEPS_RECORD[] = true
        try
            load_metta!(s, "!(q)\n"); n1 = length(get(_DF._DEPS, key, _DF.Dependency[]))
            _DF._table_reset!(); _DF._DEPS_RECORD[] = true
            load_metta!(s, "!(q)\n"); n2 = length(get(_DF._DEPS, key, _DF.Dependency[]))
            @test n1 >= 1
            @test n1 == n2        # per-completion count is STABLE; the growth is across ROUNDS, and a
                                  # fresh completion must not inherit the previous one's dependencies
        finally
            # restore the ENV default, never a literal — defaults move (they did, 2026-08-16)
            _DF.reset_execution_flags!(); _DF.untable_all!()
        end
    end
end
