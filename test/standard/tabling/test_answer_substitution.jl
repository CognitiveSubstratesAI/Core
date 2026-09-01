# test_answer_substitution.jl — THE ANSWER TABLE STORES VALUES WHERE SLG REQUIRES SUBSTITUTIONS.
#
# ⚠️ THIS IS NOT THE INTERCEPT-POSITION INVARIANT, and it deliberately does not live in
# `test_intercept_position.jl`. That file's three instances are all ONE shape — "the intercept sits
# above a stage, so the stage is skipped" — and all three are closed by moving the intercept (the
# type-check hoist). This defect is in the table's ANSWER REPRESENTATION and the hoist does not touch
# it. Different mechanism, different fix, different file.
#
# ── WHAT IS WRONG (measured 2026-09-01) ──────────────────────────────────────────────────────────
# `_ANSWER_TABLE` stores a bare answer VALUE. SLG requires an answer SUBSTITUTION over the call
# variables. `Continuation`'s own docstring already states the intended design — "answers are stored
# in the canonical key's variables and must be `_project`ed back" — so the intent is right and the
# projection is what does not constrain.
#
# The table dump is the evidence, and it is IDENTICAL for both symptoms below:
#
#     key = (eq $_v#1 b)  ->  1 answer:  [T]        <- ONE answer. The COUNT is correct.
#     key = (g $_v#1)     ->  2 answers: [1, 2]
#
# So the loss is in PROJECTION, not in the cached answer set: `T` holds only under {$_v#1 |-> b},
# and nothing records that. A substitution-valued answer both BINDS and CHECKS; a bare value does
# neither, which is why one root cause shows up as two different-looking failures:
#
#   * `$u` UNBOUND at replay -> fails to BIND  $u = b  -> the constraint never applies (symptom A)
#   * `$u` ALREADY BOUND to a -> fails to CHECK a = b  -> a FALSE ASSERTION       (symptom B)
#
# ONE fix closes both. Do not treat them as two bugs — that was the working hypothesis and the table
# dump refuted it.
#
# ── THE OPTION SPACE IS THREE, NOT TWO ──────────────────────────────────────────────────────────
# (1) SUBSTITUTION-VALUED ANSWERS — what SLG requires, what `Continuation`'s docstring already claims
#     the design is, and the same rewrite as converting `tabled_eval` from a BYPASS into a WRAPPER.
#
# (2) NARROW THE PREDICATE AT LOAD TIME — extend `auto_table!`'s existing refusals. ⚠️ This does not
#     work, and the reason is specific: the predicate would have to be "this head can be called with
#     a variable in a position the match binds" — a property of the CALL, not of the head. ANY head
#     can be called that way, and `auto_table!` sees heads. Same reason the NotReducible gap could
#     not be closed by refusing more heads (`CompileLane.jl`'s own comment).
#
# (3) DECIDE AT COMPILE TIME instead of load time — and note the (2) objection DOES NOT APPLY here,
#     because a compile-time decision has the CALL SITES in hand. Not hypothetical: Core has a
#     compile lane. JeTTa is a working existence proof — `JettaMemo` (runtime/…/JettaMemo.kt) tables
#     a function only when the compiler proves it "pure, deterministic and state-independent (no
#     match/IO/mutation, PRIMITIVE args + result, transitively pure callees)", decided at COMPILE
#     time on the AOT closed-world path, and `Generator.kt:166` additionally refuses `isMultivalued`
#     functions. Narrow on two axes by construction, and nobody upstream treats that as a defect —
#     the substitution defect below is simply UNREACHABLE there, since a variable is never primitive.
#     ⚠️ BUT THE AXIS IS *WHEN*, NOT MERELY HOW NARROW, so the predicate is not portable as-is:
#     `auto_table!` decides at LOAD time over a MUTABLE space — which is why `_ANSWER_STAMP` carries
#     `(objectid(space), revision)` for eviction — while JeTTa has no space and nothing to
#     invalidate. "Primitive args + result" is what makes CLOSED-WORLD decidable, not primarily a
#     fence against variables. Adopting it wholesale would also exclude essentially everything the
#     cognitive libs table (`Map.find`, `InsertionSort`, `DecayedConfidence` all take structured
#     arguments), and it does nothing for the INTERPRETER lane.
#
# ── UPSTREAM PREDICTED THIS ──────────────────────────────────────────────────────────────────────
# MeTTapedia `Languages/MeTTa/HE/VariantQueryCorrectness.lean` proves `canonical_legacy_cache_reusable`
# for the LEGACY one-way `simpleMatch` model ONLY, and its `## Boundary` section refuses to carry it
# to the faithful `matchAtoms`/`mergeBindings` interface because that interface "can expose
# equality-threading". We are variant-keyed over a bidirectional matcher. This is that exposure,
# measured. There is therefore NO upstream soundness certificate for our variant tabling.
#
# ── TEST DISCIPLINE ──────────────────────────────────────────────────────────────────────────────
# Plain `@test` pins TODAY'S WRONG VALUE so a NEW mechanism turns this file RED instead of hiding in
# the Broken count; `@test_broken` records the CORRECT answer so a real fix flips it to Pass.
# Anti-vacuity is asserted per case: `auto_table!` must actually have tabled the head, or the
# comparison is between two identical untabled runs. That check is not optional here — an earlier
# pass of this investigation reported "0 divergences" from exactly that mistake.
using MeTTaCore
using MeTTaCore.Eval
using Test

const _AS_DEFS = "(= (eq \$x \$x) T)\n(= (g a) 1)\n(= (g b) 2)\n"

# NOTE: deliberately NOT named `run`/`match`/`parse`/`eval` — those shadow Base silently and a
# String return then destructures into CHARACTERS, producing output that looks like data. Measured.
"""
Answer `q` against `defs`; returns (sorted answer strings, tabled heads, answer-table size).

⚠️ Returns a SORTED Vector of per-answer strings, never one rendered `string(::Vector)`. MeTTa is
MULTISET and nothing contracts traversal ORDER, so asserting `"Atom[(, T 2), (, T 1)]"` would go red
on an order flip that has nothing to do with this defect — and a test that cries wolf gets disabled.
Same reason MORK's dump comparisons sort.
"""
function _as_ask(q::AbstractString, tab::Bool; defs::AbstractString=_AS_DEFS)
    Eval.untable_all!()
    s = Eval.Space(); load_core_stdlib!(s); load_metta!(s, defs)
    info = tab ? Eval.auto_table!(s) : nothing
    answers = load_metta!(s, q)
    n = length(Eval._ANSWER_TABLE)
    Eval.untable_all!()
    (sort!([string(a) for a in answers]), info === nothing ? Symbol[] : info.tabled, n)
end

@testset "answer substitution: the table stores VALUES, not SUBSTITUTIONS" begin
    @testset "control — GROUND calls are correct in both arms" begin
        # The defect needs a VARIABLE in a position the match binds. Ground calls never hit it, and
        # this control is what localises the bug: it is not `eq` being wrong in general.
        # `want` is a Vector of per-answer strings — `_as_ask` returns sorted answers, never a
        # rendered `string(::Vector)`. See its docstring for why.
        for (q, want) in [("!(eq a b)\n", ["(eq a b)"]), ("!(eq b b)\n", ["T"]),
                          ("!(eq a a)\n", ["T"])]
            @test _as_ask(q, false)[1] == want
            @test _as_ask(q, true)[1] == want
        end
    end

    @testset "🔑 MINIMAL — no conjunction: the caller sees an UNBOUND variable" begin
        # The cleanest instance, and the one a four-construct sweep MISSED. The body returns the
        # variable alongside the tabled call, so the lost substitution is visible DIRECTLY in the
        # answer — `$w` where `b` belongs — with no conjunction machinery at all. Only `eq` is
        # tabled here (one table key), so this is also the minimal reproduction.
        d = "(= (eq \$x \$x) T)\n(= (m2 \$u) (pair \$u (eq \$u b)))\n"
        (u, _, _)  = _as_ask("!(m2 \$w)\n", false; defs=d)
        (t, tb, _) = _as_ask("!(m2 \$w)\n", true;  defs=d)
        @test !isempty(tb)                          # ANTI-VACUITY
        @test u == ["(pair b T)"]                   # untabled CORRECT: (eq \$u b) binds \$u = b
        @test length(t) == 1                        # same answer COUNT — the set is not truncated…
        @test t != u                                # …but TODAY it differs: the binding is gone
        @test !occursin("(pair b T)", only(t))      # pinned: \$w is left unbound
        @test_broken t == u                         # the fix: the answer must carry {\$u |-> b}
    end

    @testset "symptom A — replay does not BIND (constraint lost)" begin
        q = "!(, (eq \$u b) (g \$u))\n"
        (u, _, _)  = _as_ask(q, false)
        (t, tb, n) = _as_ask(q, true)
        @test !isempty(tb)                       # ANTI-VACUITY: tabling really engaged
        @test n == 2                             # …and the cache really was populated
        # Assert the PROPERTY (how many answers survive), not the rendering or the order.
        @test length(u) == 1                     # untabled CORRECT: eq threads \$u = b
        @test length(t) == 2                     # TODAY'S WRONG VALUE: constraint never applied
        @test_broken length(t) == length(u)      # the fix: replay must BIND \$u = b
    end

    @testset "symptom B — replay does not CHECK (FALSE ASSERTION)" begin
        # The serious one: tabling makes `(eq a b)` reduce to `T`, i.e. it asserts a === b.
        # Counts are EQUAL here (2 vs 2) — only the CONTENT differs, so a count-based check would
        # miss this entirely. That is also why a count-based corpus filter would conflate this
        # defect with `_reduced_goal`'s `rs[1]` truncation. Assert on content.
        q = "!(, (g \$u) (eq \$u b))\n"
        (u, _, _)  = _as_ask(q, false)
        (t, tb, n) = _as_ask(q, true)
        @test !isempty(tb)
        @test n == 2
        @test any(a -> occursin("(eq a b)", a), u)    # untabled: stays NotReducible
        @test !any(a -> occursin("(eq a b)", a), t)   # TODAY'S WRONG VALUE: it became T
        @test_broken sort(t) == sort(u)                # the fix: replay must CHECK a = b
    end

    @testset "the tabled goal ALONE — incomplete, but the loss is invisible here" begin
        # `!(eq $u b)` yields T and should ALSO bind \$u = b. With nothing downstream to observe the
        # binding, a bare value is indistinguishable from a substitution — which is precisely why
        # this defect needs a CONJUNCTION to expose and survived every single-goal test.
        (r, tb, _) = _as_ask("!(eq \$u b)\n", true)
        @test !isempty(tb)
        @test r == ["T"]
    end

    @testset "SCOPE — binding the variable BEFORE the tabled call is SAFE" begin
        # ⚠️ THIS BOUNDS THE DEFECT, SO READ THE BOUND PRECISELY. These four constructs all bind the
        # variable BEFORE the call, so the goal is GROUND at call time and gets its own ground key.
        # That is ONE family and it is safe. It is NOT evidence that "a conjunction is required" —
        # the minimal testset above has no conjunction and IS wrong. An earlier pass drew exactly
        # that too-strong conclusion from these four negatives alone.
        #
        # THE ACTUAL PRECONDITION: the tabled call is made with the variable UNBOUND, *and* the
        # binding it establishes is OBSERVED — by a sibling conjunct, or by the enclosing term that
        # returns the variable. Bind-before-call never enters the general key, so it never applies.
        B = "(= (eq \$x \$x) T)\n"
        for (d, q, why) in [
            (B*"(= (f \$y) (eq \$y b))\n",    "!(f a)\n",              "wrapper fn binds \$y first"),
            (B,                                "!(let \$u a (eq \$u b))\n", "let-bound, then eq"),
            (B*"(= (k \$y) (eq b \$y))\n",    "!(k a)\n",              "wrapper, threaded from the left"),
        ]
            (u, _, _)  = _as_ask(q, false; defs=d)
            (t, tb, _) = _as_ask(q, true;  defs=d)
            @test !isempty(tb)          # ANTI-VACUITY — without this the comparison is untabled-vs-untabled
            @test t == u                # ground key ⇒ correct
        end
    end

    @testset "PROPERTY — a ground call gets its OWN key and does not consult the general one" begin
        # Independent of the defect, and it is WHY ground calls are safe: `(eq a b)` is keyed
        # separately from `(eq \$_v#1 b)` and is answered on its own (empty) answer set rather than
        # from the more general variant.
        #
        # 🔑 IT IS ALSO A CONSTRAINT ON THE FIX. Once answers are substitution-valued, the general
        # key's answer {\$_v#1 |-> b} COULD answer the ground call `(eq a b)` by checking a = b —
        # which is precisely the subsumptive lookup the current value-only design cannot express and
        # does not attempt. A fix that keeps per-ground-call keys forfeits that.
        Eval.untable_all!()
        s = Eval.Space(); load_core_stdlib!(s); load_metta!(s, "(= (eq \$x \$x) T)\n")
        tb = Eval.auto_table!(s).tabled
        @test !isempty(tb)
        general = load_metta!(s, "!(eq \$u b)\n")          # populates (eq \$_v#1 b) -> [T]
        ground  = load_metta!(s, "!(eq a b)\n")             # must NOT be answered from it
        @test [string(a) for a in general] == ["T"]
        @test [string(a) for a in ground]  == ["(eq a b)"]  # correct: general key did not leak
        @test length(Eval._ANSWER_TABLE) == 2               # two DISTINCT keys, not one
        Eval.untable_all!()
    end
end
