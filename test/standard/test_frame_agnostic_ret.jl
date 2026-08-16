# CONTINUATION SAFETY — every `Frame.ret` closure must be FRAME-AGNOSTIC.
#
# WHY THIS EXISTS. Tabling roadmap §1.0 captures a pending frame chain and resumes it, possibly many
# times (`Continuation`, `resume_continuation`). `7ed21a2` argued that aliasing a chain is safe because
# the whole tree holds exactly ONE `Frame` field write. **THAT IS THE SYMPTOM, NOT THE GUARANTEE**, and
# the distinction was raised by a peer session and re-verified here from the closure bodies.
#
# The real guarantee: every `ret` closure takes `self::Frame` as a PARAMETER and closes over nothing
# but immutables, so re-running a chain cannot observe state left behind by an earlier run. MEASURED
# — four distinct closure types occur in a real run and none captures a Frame:
#     no_handler                        captures NOTHING
#     setup_chain's  `cont`   (:952)    depth::Int64, propagate::Bool, templ::Atom, var::Var
#     setup_function's `fret` (:968)    atom::Expression, depth::Int64
#
# ⚠️ A WRITE-COUNTING CHECK CANNOT SEE A VIOLATION. An added `Frame(` site whose closure captured an
# OUTER frame — `f -> … outer_frame …`, the natural reach when wiring `dependency/3` firing — breaks
# continuation safety while adding ZERO field writes. `test_delimited_control.jl` cannot see it either:
# it gates capture/resume BEHAVIOUR, which a frame-capturing closure would pass on a single run and
# violate only on the second resume. This file is the guard for the invariant itself.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _FA = Eval

# A Julia closure IS a struct; its captured environment IS `fieldtypes(typeof(f))`. Flag any captured
# slot that could HOLD a Frame — the type itself, an abstract/Any slot a Frame fits in, or a container.
_captures_frame_type(T::Type)::Bool = any(fieldtypes(T)) do t
    t === _FA.Frame || t === Any || t === Union{_FA.Frame,Nothing} ||
        (isabstracttype(t) && _FA.Frame <: t) || (t <: AbstractArray) || (t <: AbstractDict)
end
_captures_a_frame(f)::Bool = _captures_frame_type(typeof(f))

_fa_parse(src, sp) = (toks = _FA.tokenize(src); _FA.parse_from(toks, Ref(1), sp.tokens))

# Sweep a real evaluation and collect every distinct `ret` closure TYPE the machine builds.
function _fa_sweep!(seen::Set{Any}, goal::Atom, space)
    plan = Tuple{_FA.Frame,_FA.Bindings}[
        (_FA.Frame(goal, _FA.collect_vars(goal), nothing, _FA.no_handler, false, 0), _FA.Bindings())]
    guard = 0
    while !isempty(plan) && (guard += 1) < 50_000
        f, fb = pop!(plan)
        for fr in (f, f.prev)
            fr === nothing || push!(seen, typeof(fr.ret))
        end
        for (nf, nb) in _FA.interpret_stack(f, fb, space)
            (nf.finished && nf.prev === nothing) || push!(plan, (nf, nb))
        end
    end
    seen
end

@testset "continuation safety — every Frame.ret closure is FRAME-AGNOSTIC" begin

    # ── THE INVARIANT, over every closure a real run constructs ──────────────────────────────────
    @testset "no ret closure captures a Frame" begin
        s = Space(); load_core_stdlib!(s)
        load_metta!(s, raw"""
            (= (g $x) (Result $x))  (= (mark) M1)  (= (mark) M2)
            (= (f2 $x) (function (return (W $x))))
            (= (rec 0) done)  (= (rec $n) (rec (- $n 1)))
        """)
        seen = Set{Any}()
        for q in ("(g (mark))", "(f2 q)", "(rec 3)")
            _fa_sweep!(seen, _FA._metta(_fa_parse(q, s), _FA.UNDEF), s)
        end
        # ANTI-VACUITY FIRST: a sweep that observed nothing would pass the invariant trivially.
        @test length(seen) >= 3
        @test typeof(_FA.no_handler) in seen          # the plain-pop continuation really was exercised
        # THE INVARIANT, per closure type, so a failure names the offender
        for T in seen
            @test !_captures_frame_type(T) ||
                  (@info "ret closure CAPTURES A FRAME" type=T fields=fieldtypes(T); false)
        end
    end

    # ── THE GUARD MUST SEE THE DEFECT CLASS — three real capture shapes ─────────────────────────
    # Without this the file is a tautology: a checker that flagged nothing would pass the testset
    # above. `[[feedback_verify_the_oracle_runs]]` / `[[feedback_oracle_must_observe_the_defect_class]]`.
    @testset "MUTATION: the checker flags a frame-capturing closure" begin
        vf() = _FA.Frame(Sym("v"), _FA.EMPTY_VARS, nothing, _FA.no_handler, true, 0)
        # A — a captured local Frame, exactly what a careless `dependency/3` wiring would produce
        bad_local = let victim = vf()
            (self::_FA.Frame, r::Atom, rb::_FA.Bindings) -> (victim, rb)
        end
        # B — smuggled through an ::Any slot
        bad_any = let hidden::Any = vf()
            (self::_FA.Frame, r::Atom, rb::_FA.Bindings) -> (hidden, rb)
        end
        # C — reachable inside a captured container
        bad_box = let box = Any[vf()]
            (self::_FA.Frame, r::Atom, rb::_FA.Bindings) -> (box[1], rb)
        end
        @test _captures_a_frame(bad_local)
        @test _captures_a_frame(bad_any)
        @test _captures_a_frame(bad_box)
        # CONTROLS — shaped like the real closures; must NOT be flagged, or the guard is unusable
        good = let depth = 3, templ = Sym("t")
            (self::_FA.Frame, r::Atom, rb::_FA.Bindings) ->
                (_FA.Frame(templ, _FA.EMPTY_VARS, self.prev, _FA.no_handler, true, depth), rb)
        end
        @test !_captures_a_frame(good)
        @test !_captures_a_frame(_FA.no_handler)
    end

    # ── THE COUNT OF Frame( SITES IS PINNED, so a new one is a DECISION ─────────────────────────
    # The invariant sweep only sees closures a run actually reaches. A new construction site on a
    # rarely-taken branch could carry a bad closure and never be swept — so the count is pinned too:
    # adding a site fails here and forces the author to confirm its closure is frame-agnostic.
    @testset "Frame( construction sites are pinned at 8 (+1 inner constructor)" begin
        src = read(joinpath(@__DIR__, "..", "..", "src", "standard", "Eval.jl"), String)
        sites = Tuple{Int,String}[]
        for (i, line) in enumerate(split(src, '\n'))
            startswith(strip(line), "#") && continue
            code = split(line, '#')[1]
            for m in eachmatch(r"\bFrame\(", code)
                j = m.offset
                j >= 3 && code[max(1, j-2):j-1] == "::" && continue
                j >= 2 && code[j-1] in ('{', ',') && continue
                push!(sites, (i, strip(line)))
            end
        end
        # 9 matches = 8 real constructions + the inner constructor's own definition (`Frame(a::Atom,…)`)
        ctor  = [s for s in sites if occursin("a::Atom", s[2])]
        built = [s for s in sites if !occursin("a::Atom", s[2])]
        @test length(ctor) == 1
        @test length(built) == 8 ||
              (@info "Frame( construction count MOVED — confirm each new closure is frame-agnostic, then update this pin" built; false)
    end
end

# ── KNOWN BLIND SPOT, stated rather than left implicit ────────────────────────────────────────────
# A closure referencing a MODULE-LEVEL GLOBAL that holds a Frame is NOT caught: Julia resolves the
# global at call time instead of capturing it, so `fieldtypes` is empty. MEASURED — the first version
# of the mutation battery used a top-level `victim` and the checker returned false, which is how this
# limitation was found rather than assumed. It is out of reach for a field-based check, and it is a
# far louder smell than a captured local (a `const` Frame at module scope in `Eval.jl` would not
# survive review). The three shapes above are the ones reachable from ordinary closure-writing.
