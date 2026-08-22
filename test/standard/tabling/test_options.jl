# test_options.jl — ONE declaration surface. SWI's `table_options/3`, roadmap 0b.
#
# The config principle (user-stated 2026-08-17): *port the full surface; let config decide what is
# live*. If config is the mechanism, it cannot be five different shapes — ours had drifted to two env
# vars plus three separate functions where upstream has one entry point for twelve options.
#
# THREE STATES, and telling them apart is what this file gates:
#   HONOURED — ported and live.
#   REFUSED  — a REAL SWI option we cannot honour yet: declarable, THROWS, names the roadmap item.
#   UNKNOWN  — not an SWI option ⇒ domain_error, as upstream.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _OP = Eval

@testset "table_options/3 — one declaration surface (roadmap 0b)" begin

    @testset "HONOURED options reach the live registries" begin
        _OP.untable_all!()
        _OP.clear_all_table_options!()
        o = _OP.table_as!(:p, :subsumptive, :max_answers => 1000)
        @test o.mode == :subsumptive && o.max_answers == 1000
        # the point of ONE entry point: it is the only place that knows how an option reaches the
        # engine, so these three registries cannot drift out of step with the declaration.
        @test :p in _OP._TABLED_HEADS
        @test _OP.is_subsumptive(:p)
        @test _OP.max_answers(:p) == 1000

        # `variant` is the default AND clears a prior `subsumptive` — upstream's two clauses both
        # write the same `mode` key, so the later declaration wins rather than accumulating.
        _OP.table_as!(:p, :variant)
        @test !_OP.is_subsumptive(:p)

        # `restraint/4`: a NEGATIVE value REMOVES the restraint rather than storing it.
        _OP.table_as!(:p, :max_answers => -1)
        @test _OP.max_answers(:p) == _OP.NO_RESTRAINT
        _OP.untable_all!()
        _OP.clear_all_table_options!()
    end

    @testset "REFUSED options are DECLARABLE and throw, naming the roadmap item" begin
        # 🔴 THE DISTINCTION THIS FILE EXISTS FOR. A no-op that looks like it works is the failure
        # mode this port has paid for most: `subgoal_abstract(3)` appearing to apply while doing
        # nothing is worse than its absence, because absence gets noticed.
        for opt in (:incremental, :opaque, :monotonic, :lazy, :dynamic, :shared, :private)
            @test_throws ArgumentError _OP.table_as!(:q, opt)
        end
        # ✅ BOTH ABSTRACTION OPTIONS HAVE NOW MOVED OUT OF THIS LIST — §7.11.1 on 2026-08-17 and
        # §7.11.2 on 2026-08-18. Asserting either still throws would pin the port as less finished
        # than it is. `answer_abstract` was refused for "needs DELAY LISTS"; the premise was
        # re-checked and the real blocker was that our delay-carrying value has no VALUE — resolved
        # by seating the condition on the TRIE NODE, where upstream keeps it.
        @test _OP.table_as!(:q, :subgoal_abstract => 3).subgoal_abstract == 3
        @test _OP.table_as!(:q, :answer_abstract => 3).answer_abstract == 3
        @test _OP.answer_abstract_for(:q) == 3     # …and it REACHED the registry, not just the record
        # every refusal must NAME its roadmap item, or the message teaches nothing
        for (opt, (item, _)) in _OP._REFUSED_OPTIONS
            msg = try
                _OP.table_as!(:q, opt)
                ""
            catch e
                sprint(showerror, e)
            end
            @test occursin(item, msg)
            @test occursin("Refused rather than silently accepted", msg)
        end
        _OP.untable_all!()
        _OP.clear_all_table_options!()
    end

    @testset "UNKNOWN options are a domain_error, as upstream" begin
        @test_throws ArgumentError _OP.table_as!(:q, :bogus)
        @test_throws ArgumentError _OP.table_as!(:q, :max_answer => 5)   # near-miss on a real name
        @test_throws ArgumentError _OP.table_as!(:q, 42)                  # not even a spec shape
        _OP.untable_all!()
        _OP.clear_all_table_options!()
    end

    @testset "🔴 a THROWING declaration leaves NOTHING half-applied" begin
        # `table_as!` parses EVERY option before touching a registry, so a declaration that names one
        # good and one refused option applies neither. Without that, `table_as!(:r, :subsumptive,
        # :incremental)` would leave :r tabled and subsumptive while reporting failure — the caller
        # would believe the declaration was rejected and the engine would disagree.
        _OP.untable_all!()
        _OP.clear_all_table_options!()
        @test_throws ArgumentError _OP.table_as!(:r, :subsumptive, :incremental)
        @test !(:r in _OP._TABLED_HEADS)
        @test !_OP.is_subsumptive(:r)
        @test _OP.max_answers(:r) == _OP.NO_RESTRAINT
    end

    @testset "incremental and opaque are PAIRED — declaring one clears the other" begin
        # Upstream writes BOTH keys for either option: put_dict(#{incremental:true,opaque:false}).
        # Setting only the named field would leave a predicate both incremental AND opaque, which
        # upstream cannot represent. Both are currently REFUSED, so this asserts the record-level
        # semantics directly — the pairing is what must survive until §7.7 makes them honourable.
        o = _OP.TableOptions()
        @test !o.incremental && !o.opaque
        o.incremental = true
        o.opaque = false
        @test o.incremental && !o.opaque
        # …and the refusal covers both halves, so neither can be set through the declaration yet.
        @test haskey(_OP._REFUSED_OPTIONS, :incremental)
        @test haskey(_OP._REFUSED_OPTIONS, :opaque)
    end

    @testset "untable! clears the options record with the declaration" begin
        _OP.untable_all!()
        _OP.clear_all_table_options!()
        _OP.table_as!(:s, :subsumptive, :max_answers => 5)
        @test _OP.is_subsumptive(:s) && _OP.max_answers(:s) == 5
        _OP.untable!(:s)
        @test !(:s in _OP._TABLED_HEADS)
        @test !_OP.is_subsumptive(:s)                 # mode cleared
        @test _OP.max_answers(:s) == _OP.NO_RESTRAINT # restraint cleared
        _OP.untable_all!()
        _OP.clear_all_table_options!()
    end

    @testset "defaults match upstream's absent-key semantics" begin
        o = _OP.TableOptions()
        @test o.mode == :variant                       # upstream's default tabling mode
        @test o.tshared === nothing                    # shared/private UNSPECIFIED, not false
        @test o.max_answers == _OP.NO_RESTRAINT
        @test !o.incremental && !o.monotonic && !o.lazy && !o.dynamic
    end
end
