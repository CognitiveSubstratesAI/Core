# bench_recursion_lanes.jl — WHICH LANE OWNS FUNCTIONAL RECURSION?
#
# Four ways to run a MeTTa function are compared on recursive workloads:
#   L1  ZAM reduction fast lane   MeTTaCore.mm2_zam_answers          (MM2Router.jl:428)
#   L2  MeTTa-IL saturation       metta_il_run!(...; saturate=true)  (MeTTaIL.jl:51)
#   L3  MeTTa-IL congruence       metta_il_normalize                 (MeTTaIL.jl:118)
#   L4U Eval, untabled     load_metta!                        (Eval.jl:2443)
#   L4T Eval + auto_table! auto_table!                        (Eval.jl:988)
#
# HARNESS CONTRACT (B0):
#   * CORRECTNESS BEFORE TIMING. A cell whose answer fails its oracle is emitted with
#     status=WRONG/REJECTED/DIVERGE and is NEVER timed.
#   * Every cell is one machine-readable CELL line; the run prints RUNID START/END sentinels and a
#     final ROWS=<n>. The shell driver asserts sentinels + RUNID + ROWS, so "the script silently
#     never ran" cannot masquerade as a clean run.
#   * bytes is the PRIMARY metric (this box is nproc=2; wall time carries 4x GC spread). Wall time is
#     reported, but flagged UNRELIABLE when gc% > 10 or rep spread > 15%.
#   * Deterministic lanes must produce byte-IDENTICAL reps; otherwise status=NONDET and the cell is void.
#   * Memoisation hygiene: untable_all! + _table_reset! + a FRESH Space before EVERY rep. If any rep
#     allocates < 10% of rep 2, the reset failed => status=MEMOLEAK.
#
# Phases (ENV BENCH_PHASE), each meant to run in a FRESHLY RESTARTED warm session:
#   correctness — LENS A: expressibility + oracles for all 4 lanes x 5 workloads, plus the L1 gate walk
#   gates       — which exact gate clause rejects each workload on L1 (attribution, by execution)
#   peano       — timing: L3 vs L4U vs L4T on add(n,2), n = 4..256
#   append      — timing: L3 vs L4U vs L4T on app(len n, [0]), n = 4..256
#   fib         — timing: L4U vs L4T on fib(n)
#   l1ref       — timing: L1 on the only shape it serves (a non-recursive chain), as a floor reference
#
# Divergence cells (L3 on fib, L3 on a non-ground Peano goal) are NOT run here: they hang or blow the
# Julia stack and would corrupt the session. They run in a separate `timeout`ed child process, driven
# by bench_recursion_lanes.sh.

using MeTTaCore
const MC = MeTTaCore
const IN = MeTTaCore.Eval

const RUNID = get(ENV, "BENCH_RUNID", "noid")
const PHASE = get(ENV, "BENCH_PHASE", "correctness")
const REPS = parse(Int, get(ENV, "BENCH_REPS", "4"))          # rep 1 discarded (JIT)
const CELL_BUDGET_S = parse(Float64, get(ENV, "BENCH_BUDGET", "150.0"))

const ROWS = Ref(0)

# ── programs ────────────────────────────────────────────────────────────────────────────────────
const FIB_EQ = raw"""
(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))
"""
const FIB_IL = raw"""
(~> (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))
"""
const PEANO_EQ = raw"""
(= (add Z $y) $y)
(= (add (S $x) $y) (S (add $x $y)))
"""
const PEANO_IL = raw"""
(~> (add Z $y) $y)
(~> (add (S $x) $y) (S (add $x $y)))
"""
const APP_EQ = raw"""
(= (app Nil $ys) $ys)
(= (app (Cons $x $xs) $ys) (Cons $x (app $xs $ys)))
"""
const APP_IL = raw"""
(~> (app Nil $ys) $ys)
(~> (app (Cons $x $xs) $ys) (Cons $x (app $xs $ys)))
"""
const NATMIX_EQ = raw"""
(= (nat Z) 0)
(= (nat (S $x)) (+ 1 (nat $x)))
"""
const NATMIX_IL = raw"""
(~> (nat Z) 0)
(~> (nat (S $x)) (+ 1 (nat $x)))
"""
const OVERLAP_EQ = raw"""
(= (f a) 1)
(= (f a) 2)
"""
const OVERLAP_IL = raw"""
(~> (f a) 1)
(~> (f a) 2)
"""
const CHAIN_EQ = raw"""
(= (p $x) (q $x))
(= (q $x) (r $x))
"""
const CHAIN_IL = raw"""
(~> (p $x) (q $x))
(~> (q $x) (r $x))
"""

# ── term builders + oracles ─────────────────────────────────────────────────────────────────────
function peano(n::Int)
    t = "Z"
    for _ in 1:n
        t = "(S " * t * ")"
    end
    t
end
function mklist(xs)
    t = "Nil"
    for x in reverse(xs)
        t = "(Cons $x " * t * ")"
    end
    t
end
peano_goal(n, m) = "(add $(peano(n)) $(peano(m)))"
peano_oracle(n, m) = peano(n + m)
app_goal(n) = "(app $(mklist(1:n)) $(mklist([0])))"
app_oracle(n) = mklist(vcat(collect(1:n), [0]))

const FIB_TABLE = Dict(10 => "55", 12 => "144", 14 => "377", 16 => "987", 18 => "2584",
    20 => "6765", 22 => "17711", 24 => "46368", 26 => "121393")

# ── lane runners: each returns (answers::Vector{String}, ok::Bool) ──────────────────────────────
# L1: ZAM. Returns served answers, or the REJECTED marker.
function run_L1(eqprog::String, goal::String)
    r = MC.mm2_zam_answers(eqprog, [goal])
    if isempty(r.served)
        return (String[], :REJECTED)
    end
    (sort(String[a for (_, ans) in r.served for a in ans]), :SERVED)
end

# L2: MeTTa-IL saturation to fixpoint (KBSaturation semi-naive).
function run_L2(ilprog::String, goal::String)
    cs = MC.new_core_space()
    sort(MC.metta_il_run!(cs, goal, ilprog; saturate=true))
end

# L3: MeTTa-IL congruence normalizer (innermost subterm rewriting to fixpoint).
run_L3(ilprog::String, goal::String) = [MC.metta_il_normalize(ilprog, goal)]

# L4: interpreter. tabled=false => untable_all! first (L4U); true => auto_table! (L4T).
function l4_space(eqprog::String)
    sp = IN.Space()
    IN.load_core_stdlib!(sp)
    IN.load_metta!(sp, eqprog)
    sp
end
function run_L4(eqprog::String, goal::String; tabled::Bool=false)
    IN.untable_all!()
    IN._table_reset!()
    sp = l4_space(eqprog)
    tinfo = tabled ? IN.auto_table!(sp) : (tabled=Symbol[], skipped=Symbol[])
    res = IN.load_metta!(sp, "!" * goal)
    (sort(String[string(x) for r in res for x in (r isa AbstractVector ? r : [r])]), tinfo)
end

# ── CELL emission ───────────────────────────────────────────────────────────────────────────────
function cell(; lane, wl, n, rep, ok, t, bytes, gcpct, status, note="")
    ROWS[] += 1
    println(
        "CELL lane=$lane wl=$wl n=$n rep=$rep ok=$(ok ? 1 : 0) t=$(round(t, digits = 6)) ",
        "bytes=$bytes gcpct=$(round(gcpct, digits = 1)) rssMB=$(round(Sys.maxrss() / 2^20, digits = 0)) ",
        "status=$status", isempty(note) ? "" : " note=$note")
    flush(stdout)
end

# Time `f()` REPS times with fresh state; verify each answer against `oracle` (a Set of strings, or
# nothing to skip). Emits one CELL per rep. Returns the rep-2..N byte vector.
function timed_cell(; lane, wl, n, thunk, oracle::Union{Nothing, Set{String}}, note="")
    bs = Int[]
    ts = Float64[]
    gs = Float64[]
    halt = :none
    for rep in 1:REPS
        GC.gc()
        tm = Base.@timed thunk()
        ans = tm.value
        answers = ans isa Tuple ? ans[1] : ans
        ok = oracle === nothing ? true : (Set(answers) == oracle)
        gp = tm.time > 0 ? 100 * tm.gctime / tm.time : 0.0
        push!(bs, tm.bytes)
        push!(ts, tm.time)
        push!(gs, gp)
        extra = note
        if ans isa Tuple && ans[2] isa NamedTuple
            extra = strip(extra * " tabled=$(ans[2].tabled)/skipped=$(ans[2].skipped)")
        end
        if !ok
            cell(; lane, wl, n, rep, ok=false, t=tm.time, bytes=tm.bytes, gcpct=gp,
                status="WRONG", note=strip(extra * " got=" * repr(answers)))
            halt = :wrong
            break
        end
        # memo-leak trap: a rep that allocates < 10% of rep 2 means the table survived a reset
        if rep > 2 && bs[rep] < 0.1 * bs[2]
            cell(; lane, wl, n, rep, ok=true, t=tm.time, bytes=tm.bytes, gcpct=gp,
                status="MEMOLEAK", note=extra)
            halt = :memoleak
            break
        end
        cell(; lane, wl, n, rep, ok=true, t=tm.time, bytes=tm.bytes, gcpct=gp,
            status="OK", note=extra)
        if tm.time > CELL_BUDGET_S
            cell(; lane, wl, n, rep=0, ok=true, t=tm.time, bytes=tm.bytes, gcpct=gp,
                status="TIMEOUT", note="budget=$(CELL_BUDGET_S)s — larger n not attempted")
            halt = :budget
            break
        end
    end
    if halt !== :none || length(bs) < 2
        return (bytes=Int[], halt=halt)
    end
    keep = bs[2:end]
    kt = ts[2:end]
    kg = gs[2:end]
    spread = 100 * (maximum(kt) - minimum(kt)) / minimum(kt)
    println(
        "SUM lane=$lane wl=$wl n=$n bytes=$keep identical=$(length(unique(keep)) == 1) ",
        "tmin=$(round(minimum(kt), digits = 4)) spread=$(round(spread, digits = 1))% ",
        "gcmax=$(round(maximum(kg), digits = 1))% ",
        "t_reliable=$(maximum(kg) <= 10 && spread <= 15)")
    flush(stdout)
    (bytes=keep, halt=:none)
end

# ── PHASES ──────────────────────────────────────────────────────────────────────────────────────
function phase_correctness()
    IN.interpret_max_steps!(0)
    println("\n##### LENS A — EXPRESSIBILITY / ORACLES (correctness before any timing)")

    wls = [
        ("fib", FIB_EQ, FIB_IL, "(fib 10)", Set(["55"])),
        ("peano", PEANO_EQ, PEANO_IL, peano_goal(3, 2), Set([peano_oracle(3, 2)])),
        ("append", APP_EQ, APP_IL, app_goal(4), Set([app_oracle(4)])),
        ("natmix", NATMIX_EQ, NATMIX_IL, "(nat $(peano(3)))", Set(["3"])),
        ("overlap", OVERLAP_EQ, OVERLAP_IL, "(f a)", Set(["1", "2"])),
        ("chain", CHAIN_EQ, CHAIN_IL, "(p a)", Set(["(r a)"]))
    ]
    for (wl, eqp, ilp, goal, oracle) in wls
        println("\n--- workload=$wl goal=$goal oracle=$(sort(collect(oracle)))")
        # L4U is the reference oracle implementation; run it first
        a4u, _ = run_L4(eqp, goal; tabled=false)
        println("  L4U  answers=$(a4u)  ok=$(Set(a4u) == oracle)")
        a4t, ti = run_L4(eqp, goal; tabled=true)
        println(
            "  L4T  answers=$(a4t)  ok=$(Set(a4t) == oracle)  auto_table!=(tabled=$(ti.tabled), skipped=$(ti.skipped))"
        )
        # L1
        a1, st1 = run_L1(eqp, goal)
        println(
            "  L1   $(st1 === :REJECTED ? "REJECTED-BY-GATE (served=[], bang deferred)" : "answers=$(a1)  ok=$(Set(a1) == oracle)  set==L4U:$(Set(a1) == Set(a4u))")"
        )
        # L2 (never diverges: one semi-naive fixpoint)
        a2 = run_L2(ilp, goal)
        println(
            "  L2   answers=$(a2)  ok=$(Set(a2) == oracle)  set==L4U:$(Set(a2) == Set(a4u))"
        )
        # L3 — skip fib (proven non-terminating; measured in a child process instead)
        if wl == "fib"
            println(
                "  L3   NOT RUN IN-SESSION — non-terminating (see DIVERGE child-process cell)"
            )
        else
            a3 = run_L3(ilp, goal)
            println(
                "  L3   answers=$(a3)  ok=$(Set(a3) == oracle)  set==L4U:$(Set(a3) == Set(a4u))  subset_of_L4U:$(issubset(Set(a3), Set(a4u)))"
            )
        end
        ROWS[] += 1
    end

    println(
        "\n##### L3 clause-order sensitivity (MeTTaIL.jl:101-106 returns on FIRST matching rule)"
    )
    o1 = raw"(~> (f a) 1)" * "\n" * raw"(~> (f a) 2)"
    o2 = raw"(~> (f a) 2)" * "\n" * raw"(~> (f a) 1)"
    println("  L3 rules[1,2] -> ", repr(MC.metta_il_normalize(o1, "(f a)")))
    println("  L3 rules[2,1] -> ", repr(MC.metta_il_normalize(o2, "(f a)")))
    ROWS[] += 1

    println(
        "\n##### L3 non-ground adversary: unify-not-match (MorkBridge.jl:16 expr_unify)"
    )
    println("  mork_rule_rewrite(\"(= (g a) hit)\", \"\\\$x\") -> ",
        repr(MC.mork_rule_rewrite(raw"(= (g a) hit)", raw"$x")))
    println("  L3 metta_il_normalize(\"(~> (g a) hit)\", \"(g \\\$x)\") -> ",
        repr(MC.metta_il_normalize(raw"(~> (g a) hit)", raw"(g $x)")))
    spx = IN.Space()
    IN.load_core_stdlib!(spx)
    IN.load_metta!(spx, raw"(= (g a) hit)")
    println("  L4U oracle  !(g \$x) -> ", IN.load_metta!(spx, raw"!(g $x)"))
    ROWS[] += 1

    println(
        "\n##### L3 ground Peano sweep — 91 pairs n in 0:12 x m in 0:6, oracle = exact S-tower"
    )
    nfail = 0
    for n in 0:12, m in 0:6
        r = MC.metta_il_normalize(PEANO_IL, peano_goal(n, m))
        r == peano_oracle(n, m) ||
            (nfail += 1; nfail <= 5 && println("   MISMATCH n=$n m=$m got=$r"))
    end
    println("  L3 ground sweep: ", nfail == 0 ? "91/91 PASS" : "$nfail FAILURES")
    ROWS[] += 1

    println("\n##### L2 mechanism dump — what saturation actually leaves in the space")
    cs = MC.new_core_space()
    r = MC.metta_il_run!(cs, peano_goal(2, 1), PEANO_IL; saturate=true)
    println("  metta_il_run!(saturate=true) -> ", r)
    println("  full space dump:")
    for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
        isempty(strip(l)) || println("    ", strip(l))
    end
    ROWS[] += 1

    println(
        "\n##### L2 CONTROL — transitive closure (the shape saturation DOES close, test_gslt.jl:150-159)"
    )
    tc_il = raw"""
(~> (, (edge $x $y)) (path $x $y))
(~> (, (path $x $y) (edge $y $z)) (path $x $z))
"""
    cs2 = MC.new_core_space()
    rtc = MC.metta_il_run!(cs2, "(edge a b)\n(edge b c)\n(edge c d)", tc_il; saturate=true)
    println("  paths=", rtc, "  count=", length(rtc))
    ROWS[] += 1
end

function phase_gates()
    println("\n##### L1 GATE WALK — which clause rejects which workload (by execution)")
    for (wl, eqp, goal) in [("fib", FIB_EQ, "(fib 10)"),
        ("peano", PEANO_EQ, peano_goal(2, 1)),
        ("append", APP_EQ, app_goal(3)),
        ("tailrec", raw"(= (loop (S $x)) (loop $x))" * "\n", "(loop (S Z))"),
        ("chain", CHAIN_EQ, "(p a)")]
        println("\n--- $wl")
        forms = MC.mm2_split_forms(eqp)
        heads = Set{String}()
        for (bang, f) in forms
            (bang || MC.mm2_head(f) != "=") && continue
            push!(heads, MC.mm2_head(MC.mm2_expr_args(f)[2]))
        end
        p = MC.mm2_partition(eqp; eq_mode=:reduction)
        println("  heads=$(sort(collect(heads)))")
        println("  partition.data=$(p.data)")
        println("  partition.exec=$(p.exec)")
        println("  GATE(1) any((=) in p.data) [MM2Router.jl:436] = ",
            any(f -> MC.mm2_head(f) == "=", p.data))
        for (bang, f) in forms
            (bang || MC.mm2_head(f) != "=") && continue
            a = MC.mm2_expr_args(f)
            lhs, rhs = a[2], a[3]
            println("  rule $(f)")
            println("     mm2_is_relational  [:95]  = ", MC.mm2_is_relational(f))
            println("     mm2_is_arith_body  [:318] = ", MC.mm2_is_arith_body(f))
            println(
                "     GATE(4) head_below_top(LHS) [:474] = ",
                MC._mm2_head_below_top(lhs, heads)
            )
            println(
                "     GATE(4) head_below_top(RHS) [:475] = ",
                MC._mm2_head_below_top(rhs, heads)
            )
            println("     GATE(3) RHS top head in heads (edge) [:476] = ",
                startswith(strip(rhs), "(") && MC.mm2_head(rhs) in heads)
        end
        r = MC.mm2_zam_answers(eqp, [goal])
        println("  mm2_zam_answers -> served=$(r.served) remaining=$(r.remaining)")
        ROWS[] += 1
    end

    println("\n##### mc_run end-to-end routing (the PRODUCTION entry, DualTrack.jl:101)")
    for (wl, eqp, goal) in
        [("fib", FIB_EQ, "(fib 10)"), ("peano", PEANO_EQ, peano_goal(2, 1)),
        ("append", APP_EQ, app_goal(3))]
        cs = MC.new_core_space()
        r = MC.mc_run(cs, "", eqp * "\n!" * goal)
        println("  $wl lane=$(r.lane) results=$(r.results)")
        ROWS[] += 1
    end
end

# BOUNDED evidence for the L3-on-fib divergence: drive `mork_rule_rewrite` by hand at TOP LEVEL only
# (no `_normalize_subterm` recursion => cannot hang) and watch the term GROW. The unbounded run is
# done in a `timeout`ed child process by bench_recursion_lanes.sh.
function phase_l3steps()
    println(
        "\n##### L3 fib — BOUNDED single-step trace (each step is one mork_rule_rewrite, top level)"
    )
    rule = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))"
    t = "(fib 5)"
    for k in 0:5
        println("  step=$k len=$(length(t)) term=$t")
        # take the LEFTMOST inner (fib …) of the previous expansion to show the argument growing
        r = MC.mork_rule_rewrite(rule, t)
        r === nothing && (println("  no match at step $k"); break)
        s = String(r)
        # next redex = the first nested (fib ...) occurrence, extracted by paren balance
        i = findfirst("(fib ", s)
        if i === nothing
            println("  no nested (fib …) at step $k")
            break
        end
        j = first(i)
        d = 0
        e = j
        while e <= lastindex(s)
            s[e] == '(' && (d += 1)
            s[e] == ')' && (d -= 1)
            d == 0 && break
            e = nextind(s, e)
        end
        t = s[j:e]
        k == 0 && println("  full first reduct = $s")
    end
    ROWS[] += 1

    println(
        "\n##### grounded-op reduction has NO path on L3 (MorkBridge.jl:50-58 = unify+apply only)"
    )
    for (r, d) in
        [(raw"(= (f $n) (- $n 1))", "(f 5)"), (raw"(= (f $n) $n)", "(f (- 5 1))"),
        (raw"(= (f $n) (< $n 2))", "(f 5)"), (raw"(= (f $n) (+ 1 2))", "(f 5)")]
        println("  rule=$r  data=$d  -> ", repr(MC.mork_rule_rewrite(r, d)))
    end
    println("  MORK GROUNDED_REGISTRY keys = ", sort(collect(keys(MC.GROUNDED_REGISTRY))))
    ROWS[] += 1

    println(
        "\n##### L2/L1 nesting wall — a redex UNDER a constructor is invisible to whole-atom matching"
    )
    cs = MC.new_core_space()
    MC.space_add_all_sexpr!(cs.inner, "(add (S (S Z)) (S Z))")
    for e in ["(exec 0 (I (add Z \$y)) (O (+ \$y) (- (add Z \$y))))",
        "(exec 0 (I (add (S \$x) \$y)) (O (+ (S (add \$x \$y))) (- (add (S \$x) \$y))))"]
        MC.space_add_all_sexpr!(cs.inner, e)
    end
    MC.space_metta_calculus!(cs.inner, 1_000_000)
    println("  hand-lowered Peano execs, ALL GATES BYPASSED, 1e6 calculus steps. dump:")
    for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
        isempty(strip(l)) || println("    ", strip(l))
    end
    ROWS[] += 1
end

function phase_peano()
    IN.interpret_max_steps!(0)
    println("\n##### TIMING — peano add(n,2). L3 vs L4U vs L4T. oracle = exact S-tower.")
    stop = Set{String}()
    for n in [4, 8, 16, 32, 64, 128, 256]
        g = peano_goal(n, 2)
        o = Set([peano_oracle(n, 2)])
        for (lane, th) in [("L3", () -> run_L3(PEANO_IL, g)),
            ("L4U", () -> run_L4(PEANO_EQ, g; tabled=false)),
            ("L4T", () -> run_L4(PEANO_EQ, g; tabled=true))]
            lane in stop && continue
            r = timed_cell(; lane=lane, wl="peano", n=n, oracle=o, thunk=th)
            r.halt === :none || push!(stop, lane)
        end
    end
end

function phase_append()
    IN.interpret_max_steps!(0)
    println("\n##### TIMING — append(list of n, [0]). L3 vs L4U vs L4T.")
    stop = Set{String}()
    for n in [4, 8, 16, 32, 64, 128, 256]
        g = app_goal(n)
        o = Set([app_oracle(n)])
        for (lane, th) in [("L3", () -> run_L3(APP_IL, g)),
            ("L4U", () -> run_L4(APP_EQ, g; tabled=false)),
            ("L4T", () -> run_L4(APP_EQ, g; tabled=true))]
            lane in stop && continue
            r = timed_cell(; lane=lane, wl="append", n=n, oracle=o, thunk=th)
            r.halt === :none || push!(stop, lane)
        end
    end
end

function phase_fib()
    IN.interpret_max_steps!(0)
    println(
        "\n##### TIMING — fib. L4U (untabled) vs L4T (auto_table!, COLD table per rep)."
    )
    for n in [10, 12, 14, 16, 18, 20, 22]
        o = Set([FIB_TABLE[n]])
        r = timed_cell(; lane="L4U", wl="fib", n=n, oracle=o,
            thunk=() -> run_L4(FIB_EQ, "(fib $n)"; tabled=false))
        r.halt === :none || break                          # budget breach / wrong => stop growing n
    end
    for n in [10, 12, 14, 16, 18, 20, 22, 24, 26]
        o = Set([FIB_TABLE[n]])
        timed_cell(; lane="L4T", wl="fib", n=n, oracle=o,
            thunk=() -> run_L4(FIB_EQ, "(fib $n)"; tabled=true))
    end
    println(
        "\n##### WARM-TABLE ARTEFACT (NOT a lane): same space, table already populated."
    )
    IN.untable_all!()
    IN._table_reset!()
    sp = l4_space(FIB_EQ)
    ti = IN.auto_table!(sp)
    println("  auto_table! -> tabled=$(ti.tabled) skipped=$(ti.skipped)")
    for rep in 1:4
        tm = Base.@timed IN.load_metta!(sp, "!(fib 24)")
        println(
            "  warm-hit rep=$rep t=$(round(tm.time, digits = 6)) bytes=$(tm.bytes) ans=$(tm.value)"
        )
    end
    ROWS[] += 1
end

function phase_l1ref()
    println(
        "\n##### TIMING — L1 floor reference on the ONLY recursive-free shape it serves: chain p->q->r"
    )
    timed_cell(; lane="L1", wl="chain", n=1, oracle=Set(["(r a)"]),
        thunk=() -> run_L1(CHAIN_EQ, "(p a)")[1])
    timed_cell(; lane="L3", wl="chain", n=1, oracle=Set(["(r a)"]),
        thunk=() -> run_L3(CHAIN_IL, "(p a)"))
    timed_cell(; lane="L4U", wl="chain", n=1, oracle=Set(["(r a)"]),
        thunk=() -> run_L4(CHAIN_EQ, "(p a)"; tabled=false))
end

function bench_main()
    println("RUNID=$RUNID START phase=$PHASE reps=$REPS budget=$(CELL_BUDGET_S)s")
    flush(stdout)
    if PHASE == "correctness"
        phase_correctness()
    elseif PHASE == "gates"
        phase_gates()
    elseif PHASE == "l3steps"
        phase_l3steps()
    elseif PHASE == "peano"
        phase_peano()
    elseif PHASE == "append"
        phase_append()
    elseif PHASE == "fib"
        phase_fib()
    elseif PHASE == "l1ref"
        phase_l1ref()
    else
        error("unknown BENCH_PHASE=$PHASE")
    end
    println("\nROWS=$(ROWS[])")
    println("RUNID=$RUNID END phase=$PHASE")
    flush(stdout)
end

Base.invokelatest(bench_main)
