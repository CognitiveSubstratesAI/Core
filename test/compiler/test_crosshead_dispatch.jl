# test_crosshead_dispatch.jl — INCREMENT 2: a call to another head must dispatch through THAT
# head's definition entry, and must AGREE WITH THE INTERPRETER while doing so.
#
# 🔴 THIS FILE FOUND A LIVE UNSOUNDNESS IN THE NATIVE LANE. It was written to prove a MISSING
# FEATURE and instead measured WRONG ANSWERS. The three premises it started from were all false,
# and each was corrected by running it rather than by reading:
#
#   WRONG: "a head calling another user head cannot compile."  MEASURED: it compiles NATIVE.
#   WRONG: "`nested_head` is what declines `(= (snd (P $a $b)) $b)`."  MEASURED: `nested_head` is
#          FALSE; that clause declines CODEGEN (its head arg is not a variable) and compiles on the
#          PLAN lane. `nested_head` means the head's own head is an expression — `((f $x) $y)`.
#   WRONG: "the cross-head call is a `GCall` that line 471 blocks."  MEASURED: in TAIL position it
#          is not a goal at all (it becomes the clause output, which the interpreter then reduces),
#          and in an ARGUMENT position it stays a NESTED `IRExpression` inside another call's args.
#
# ─── THE DEFECT, MEASURED AGAINST THE INTERPRETER AS ORACLE ─────────────────────────────────────
#   (= (g $x) (+ $x 1))  (= (t3 $x) (+ 1 (g $x)))   !(t3 5)
#       interpreter : 7              compiled : (+ 1 6)      lane native, fired 1
#   (= (snd (P $a $b)) $b)  (= (t2 $p) (+ 1 (snd $p)))   !(t2 (P 1 2))
#       interpreter : 3              compiled : (+ 1 2)      lane native, fired 1
# `fired` moves, so the compiled entry really answered — this is not a fallback and not a decline.
#
# ─── WHY: A-NORMAL FORM IS NOT REACHED FOR USER-HEAD APPLICATIONS ───────────────────────────────
# `(= (t3 $x) (+ 1 (g $x)))` translates to ONE goal:
#     GCall(+, [IRGrounded(1), IRExpression(g $x)]) -> __t1
# The inner user call is NOT hoisted into its own goal, though making every call's arguments atomic
# is the defining property of the form. So codegen never consults `compilable`, never reaches the
# enforcement point at `EmitJuliaCode.jl:471`, builds `(g $x)` as a LITERAL ATOM, and passes it to
# `+`, which cannot add an expression and returns the application unreduced.
#
# ⇒ the native lane is not merely EMPTY for cross-head calls, it is UNSOUND for them, and the suite
# is green because nothing compared a compiled answer with an interpreted one for this shape.
# 🔴 AND IT IS A BLOCKER FOR THE FIRST-CALL TRIGGER: today `jit_head!` runs only from
# `(compile-head …)` in tests, so the defect is LATENT. The trigger compiles on first call, which
# makes every head of this shape answer wrongly in production — the same latency the cross-space
# collision had.
#
# ─── WHAT A FIX MUST COVER ──────────────────────────────────────────────────────────────────────
#   1. HOIST a user-head application out of an argument position into its own `GCall` goal, so the
#      form is actually A-normal and the enforcement point becomes reachable;
#   2. THEN increment 2's dispatch through the definition entry, so a callee that declines resolves
#      to the interpreter instead of disqualifying its caller.
# A fix that does only (2) leaves these differentials red, because (2) is downstream of the miss.
using Test
using MeTTaCore
using MeTTaCore.Eval
const EV = MeTTaCore.Eval
const EJ = MeTTaCore.CompilerEmitJulia
const EJC = MeTTaCore.CompilerEmitJuliaCode
const AN  = MeTTaCore.CompilerANormal
const F   = MeTTaCore.CompilerFrontend
const ST  = MeTTaCore.StandardMeTTa   # `Atom`/`Sym` are NOT in Main at this path

"Answers as plain strings. ⚠️ NOT `string(::Vector{Atom})` — that renders the module qualifier only
when the type is out of scope, so a COLD process and a WARM one disagree on a value unrelated to the
code under test. It turned `test_intercept_position.jl` red under `warm_suite.sh` while the identical
tree was green cold."
_xh(sp, q) = [string(x) for x in EV.load_metta!(sp, q)]

@testset "increment 2 — cross-head dispatch through definition entries" begin

"Interpret `q`, then compile `head`, then interpret `q` again. The INTERPRETER IS THE ORACLE: the
only thing that matters is that compiling did not change the answer."
function _xh_diff(prog, head, q)
    EV.uncompile_all!(); EV.reset_jit_declined!(); EV.reset_compiled_fallbacks!()
    sp = EV.Space(); EV.load_core_stdlib!(sp); EV.load_metta!(sp, prog)
    interp = _xh(sp, q)
    ok = EJ.jit_head!(head, sp)
    f0 = EV.fired(head)
    compiled = _xh(sp, q)
    r = (interp = interp, compiled = compiled, jit = ok,
         lane = ok ? EV.head_lane(head) : :none, fired = EV.fired(head) - f0)
    EV.uncompile_all!()
    r
end

@testset "🔴 a NON-TAIL call to another head must AGREE WITH THE INTERPRETER" begin
    # 🔴 THE CENTRAL GATE, AND IT FAILS TODAY WITH A WRONG ANSWER, not with a decline.
    d = _xh_diff("(= (g \$x) (+ \$x 1))\n(= (t3 \$x) (+ 1 (g \$x)))\n", :t3, "!(t3 5)\n")
    # ANTI-VACUITY, THREE WAYS: the head must really have compiled, on the NATIVE lane, and the
    # compiled entry must really have answered. Without `fired`, a decline would satisfy the
    # agreement assertion trivially and the gate would pass while testing nothing.
    @test d.jit == true
    @test d.fired >= 1
    @test d.interp == ["7"]                 # the oracle, pinned — if this moves, the case changed
    # 🔴 THE SOUNDNESS GATE. Answered ["(+ 1 6)"] before the guard; the guard makes codegen DECLINE
    # the clause and the PLAN lane answers it correctly instead.
    @test d.compiled == d.interp
    @test d.lane === :plan                  # where the guard moved it — still compiled, not dropped
    # 🔴 THE HOIST'S TARGET, kept as `@test_broken` so it is not forgotten: once a user-head
    # application in an argument is hoisted into its own goal, this shape belongs on the NATIVE lane.
    # Julia reports "Unexpectedly Passed" when that lands, which is the signal to drop `_broken`.
    @test_broken d.lane === :native

    # The same shape where the callee declines CODEGEN and compiles on the PLAN lane instead. Listed
    # separately because the fix must route through the DEFINITION ENTRY, which is what makes the
    # callee's lane irrelevant to its caller.
    d2 = _xh_diff("(= (snd (P \$a \$b)) \$b)\n(= (t2 \$p) (+ 1 (snd \$p)))\n", :t2, "!(t2 (P 1 2))\n")
    @test d2.jit == true
    @test d2.fired >= 1
    @test d2.interp == ["3"]
    @test d2.compiled == d2.interp          # answered ["(+ 1 2)"] before the guard
    @test_broken d2.lane === :native        # the hoist's target here too

    # NEGATIVE CONTROLS — the shapes that are CORRECT today must stay correct. Without these, a
    # "fix" that simply stopped compiling anything would turn the gates above green.
    d3 = _xh_diff("(= (snd (P \$a \$b)) \$b)\n(= (t1 \$p) (snd \$p))\n", :t1, "!(t1 (P 1 2))\n")
    @test d3.compiled == d3.interp == ["2"]           # TAIL position: the clause output
    d4 = _xh_diff("(= (inc \$x) (+ \$x 1))\n", :inc, "!(inc 41)\n")
    @test d4.compiled == d4.interp == ["42"]          # no cross-head call at all
    @test d4.lane === :native                         # and still native — not fixed by retreating
    @test EV.jit_errors() == 0
end

@testset "🔴 a user-head application in an ARGUMENT must be its own A-normal goal" begin
    # The CAUSE, asserted directly, so a fix at the wrong layer cannot turn the differential green
    # by accident. A-normal form's defining property is that every call's arguments are ATOMIC;
    # `(+ 1 (g $x))` violates it by keeping `(g $x)` as a nested `IRExpression` argument.
    EV.uncompile_all!()
    sp = EV.Space(); EV.load_core_stdlib!(sp)
    EV.load_metta!(sp, "(= (g \$x) (+ \$x 1))\n(= (t3 \$x) (+ 1 (g \$x)))\n")
    rules = ST.Atom[]
    for a in EV.all_atoms(sp)
        a isa ST.Expression && length(a.children) == 3 || continue
        h = a.children[1]
        (h isa ST.Sym && String(h.name) == "=") || continue
        lhs = a.children[2]
        hd = lhs isa ST.Expression && !isempty(lhs.children) ? lhs.children[1] : lhs
        (hd isa ST.Sym && Base.Symbol(hd.name) === :t3) && push!(rules, a)
    end
    @test !isempty(rules)                             # anti-vacuity: the clause was really found
    cls = [c for c in AN.translate_program(F.lower_program(rules)) if c.name === :t3]
    @test length(cls) == 1
    calls = [g for g in cls[1].goals if g isa AN.GCall]
    @test !isempty(calls)
    # 🔴 THE GATE. Today ONE goal, `GCall(+)`, whose arg2 is `IRExpression(g $x)`.
    @test_broken any(g -> g.head === :g, calls)
    @test [g.head for g in calls] == [:+]   # today's shape, pinned
    # and no remaining goal may carry a user-head application nested inside an argument
    # ⚠️ `IRExpression` has `head`/`args`, NOT `children` — `children` is the STANDARD `Expression`'s
    # field, and reaching for it here raised a FieldError the first time this ran.
    nested_user_call(a) = a isa MeTTaCore.CompilerIR.IRExpression &&
        a.head isa MeTTaCore.CompilerIR.IRSymbol && a.head.name === :g
    @test_broken !any(g -> any(nested_user_call, g.args), calls)
    @test any(g -> any(nested_user_call, g.args), calls)   # today: the call is nested in an arg
end

@testset "🔴 a REPEATED HEAD VARIABLE must not make a non-matching call match" begin
    # FOUND BY `workflows/compiled_head_differential.jl` on the first corpus it was pointed at —
    # `conformance/b1_equal_chain.metta` defines `(= (eq $x $x) T)`:
    #     !(eq Green Blue)   interpreter -> (eq Green Blue)      compiled -> T
    # `_bindargs` binds head arguments positionally AND BY NAME (`x = _a[1]; x = _a[2]`), so the
    # second binding overwrites the first and the constraint that both arguments be EQUAL is never
    # emitted. A NON-MATCHING CALL WRONGLY MATCHED — the worst shape of all, because the head
    # answers where it should have stayed unreduced.
    d = _xh_diff("(= (eq \$x \$x) T)\n", :eq, "!(eq Green Blue)\n")
    @test d.jit == true                               # still compiled — on the plan lane
    @test d.fired >= 1                                # and the compiled entry really answered
    @test d.interp == ["(eq Green Blue)"]             # the oracle: no rule matches, so it is itself
    @test d.compiled == d.interp                      # 🔴 answered ["T"] before the decline
    # THE MATCHING CALL MUST STILL WORK — a "fix" that broke `(eq Green Green)` would satisfy the
    # line above while losing the rule entirely.
    m = _xh_diff("(= (eq \$x \$x) T)\n", :eq, "!(eq Green Green)\n")
    @test m.interp == ["T"]
    @test m.compiled == m.interp
    # 🔴 THE TARGET: emitting the equality check is part of HEAD PATTERNS (the 229-head blocker),
    # at which point this shape belongs on the native lane again.
    @test_broken d.lane === :native
end

@testset "a TABLED callee must still route through TABLING (forward guard)" begin
    # ⚠️ THIS PASSES TODAY, AND SAYS SO. `go`'s call to `reach` is in TAIL position, so it is not a
    # goal at all: the interpreter reduces the clause output and tabling is reached normally. It
    # becomes a LIVE test the moment argument-position calls are hoisted and dispatched natively,
    # which is exactly when the bypass it guards against becomes possible. Recorded as a guard
    # rather than deleted, because deleting it would lose the constraint.
    EV.uncompile_all!(); EV.untable_all!()
    sp = EV.Space(); EV.load_core_stdlib!(sp)
    # `reach` is LEFT-RECURSIVE: untabled it recurses forever, tabled it completes with {1}.
    EV.load_metta!(sp, "(= (reach \$x) (reach \$x))\n(= (reach \$x) \$x)\n(= (go \$x) (reach \$x))\n")
    EV.table!(:reach)
    EV.reset_compiled_fallbacks!()
    try
        @test _xh(sp, "!(go 1)\n") == ["1"]          # anti-vacuity: tabling already carries it
        @test EJ.jit_head!(:go, sp) == true
        f0 = EV.fired(:go)
        @test _xh(sp, "!(go 1)\n") == ["1"]          # still terminates, still right
        @test EV.fired(:go) > f0
        # 🔴 THE ASSERTION THAT KEEPS THIS HONEST. A bypass of tabling would recurse until the depth
        # budget fired, and the budget's fallback RE-INTERPRETS the head — which tables correctly and
        # returns ["1"]. So THE ANSWER ALONE WOULD PASS FOR A BROKEN IMPLEMENTATION. What must hold
        # is that tabling carried it and the budget never fired at all.
        @test EV.COMPILED_FALLBACK_DEPTH[] == 0
    finally
        EV.untable_all!()                             # `_TABLED_HEADS` is PROCESS-GLOBAL
        EV.uncompile_all!()
    end
end

@testset "🔴 the DEPTH BUDGET must count ACROSS LANES" begin
    EV.uncompile_all!()
    sp = EV.Space(); EV.load_core_stdlib!(sp)
    # An ALTERNATING chain: `down` compiles native, `mid` declines codegen on its non-variable head
    # argument, and each calls the other. Every re-entry into native code arrives through the seam
    # with `_d = 0` — `_codegen_seam_fn` passes a literal 0 — so the budget restarts on every hop
    # while the HOST STACK keeps growing.
    #
    # ⚠️ NO LITERAL IN A HEAD ARGUMENT: `(= (down 0) bottom)` would make `down` itself decline
    # codegen (EmitJuliaCode.jl:670/691 take positional variables only), so the base case is an `if`.
    EV.load_metta!(sp, "(= (down \$n) (if (== \$n 0) bottom (mid (W \$n))))\n" *
                       "(= (mid (W \$n)) (down (- \$n 1)))\n")
    saved = EJC._MAX_CALL_DEPTH[]
    EV.reset_compiled_fallbacks!()
    try
        # 🔴 THE BUDGET IS SHRUNK RATHER THAN THE CHAIN LENGTHENED, DELIBERATELY. Reaching the real
        # 4000 through two lanes risks an actual StackOverflowError, which Julia says may leave
        # program state corrupted and is not catchable in any way code may depend on — it would take
        # the suite process down. A budget of 40 against a 200-deep chain observes the SAME property
        # with no stack risk.
        EJC._MAX_CALL_DEPTH[] = 40
        @test EJ.jit_head!(:down, sp) == true
        @test _xh(sp, "!(down 200)\n") == ["bottom"]
        # 🔴 THE GATE. 200 deep against a budget of 40, so the budget MUST have fired. Today it
        # stays 0: each hop re-enters at `_d = 0` and never reaches 40, so the budget bounds nothing.
        @test_broken EV.COMPILED_FALLBACK_DEPTH[] > 0
        @test EV.COMPILED_FALLBACK_DEPTH[] == 0   # today: the budget restarts every hop
    finally
        EJC._MAX_CALL_DEPTH[] = saved                 # another session-scoped global
        EV.uncompile_all!()
    end
end

end
