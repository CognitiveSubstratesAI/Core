# MM2 dual-lane router (src/standard/MM2Router.jl) — CeTTa-adopted, PRIMUS-native.
# Partition a program into !/exec/data lanes; route exec+data to the native MORK CoreSpace;
# reject top-level ! in the pure-program lane (CeTTa's MM2-file-loader discipline).
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "MM2 dual-lane router" begin
    facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"
    rule  = raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
    prog  = facts * "\n" * rule

    @testset "partition into exec / data / bang lanes" begin
        p = mm2_partition(prog)
        @test isempty(p.bangs)
        @test length(p.exec) == 1 && mm2_is_exec_rule(p.exec[1])
        @test length(p.data) == 3 && all(!mm2_is_exec_rule, p.data)
        @test mm2_is_exec_rule(rule) && !mm2_is_exec_rule("(edge 0 1)")
    end

    @testset "MM2 lane runs exec on the native MORK CoreSpace" begin
        cs = MC.new_core_space()
        @test mm2_run!(cs, prog) == (n_exec = 1, n_data = 3, n_bang = 0)
        dump = MC.space_dump_all_sexpr(cs.inner)
        @test occursin("trans 0 2", dump) && occursin("trans 1 3", dump)
    end

    @testset "bisimulation: router MM2 lane ≡ interpreter (match)" begin
        cs = MC.new_core_space(); mm2_run!(cs, prog)
        R_mm2 = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                             if occursin("trans", l)]))
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, raw"!(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_interp == ["(trans 0 2)", "(trans 1 3)"]
        @test R_mm2 == R_interp
    end

    @testset "pure-program lane rejects top-level ! (CeTTa discipline)" begin
        @test_throws ErrorException mm2_run!(MC.new_core_space(), raw"!(match &self (foo $x) $x)")
        r = mm2_run!(MC.new_core_space(), facts * "\n" * raw"!(foo)"; allow_bang = true)
        @test r.n_bang == 1
    end

    # ── piece 2: the match→exec bridge ──
    @testset "match→exec lowering (§10.3)" begin
        @test mm2_lower_match(raw"(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))") ==
              raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
        @test mm2_lower_match(raw"(match &self (p $x) (found $x))") ==
              raw"(exec 0 (, (p $x)) (, (found $x)))"
    end

    @testset "mm2_match! ≡ interpreter (bisimulation)" begin
        cs = MC.new_core_space(); MC.space_add_all_sexpr!(cs.inner, facts)
        R_mm2 = mm2_match!(cs, raw"(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        @test R_mm2 == ["(trans 0 2)", "(trans 1 3)"]
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, raw"!(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_mm2 == R_interp
    end

    # ── piece 3: the (=)→exec rule bridge (general rewrite rules, relational subset) ──
    @testset "(= LHS RHS) → exec lowering + bisimulation" begin
        @test mm2_lower_equals(raw"(= (ancestor $x $y) (parent $x $y))") ==
              raw"(exec 0 (, (ancestor $x $y)) (, (parent $x $y)))"
        @test mm2_lower_equals(raw"(= (, (p $x) (q $x)) (r $x))") ==
              raw"(exec 0 (, (p $x) (q $x)) (, (r $x)))"          # conjunctive LHS passes through
        @test_throws ErrorException mm2_lower_equals(raw"(match &self (p $x) $x)")  # not a (= …) form

        # a (= …) rewrite rule fires through space_metta_calculus! and bisimulates the interpreter
        afacts = "(ancestor a b)\n(ancestor b c)"
        arule  = raw"(= (ancestor $x $y) (parent $x $y))"
        cs = MC.new_core_space()
        MC.space_add_all_sexpr!(cs.inner, afacts)
        MC.space_add_all_sexpr!(cs.inner, mm2_lower_equals(arule))
        MC.space_metta_calculus!(cs.inner, 1_000_000)
        R_mork = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                              if occursin("parent", l)]))
        @test R_mork == ["(parent a b)", "(parent b c)"]

        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, afacts)
        res = SM.load_metta!(isp, raw"!(match &self (ancestor $x $y) (parent $x $y))")
        R_interp = sort(unique(filter(s -> occursin("parent", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_mork == R_interp                              # MORK (=) lane ≡ interpreter oracle
    end

    @testset "(= …) reduction-mode lowering (delete-redex) vs relational (keep-redex)" begin
        # reduction: (= L R) → (exec 0 (I L) (O (+ R) (- L))) — consume the redex, add the reduct
        @test mm2_lower_equals(raw"(= (myf $x) (wrap $x))"; mode = :reduction) ==
              raw"(exec 0 (I (myf $x)) (O (+ (wrap $x)) (- (myf $x))))"
        @test mm2_lower_equals(raw"(= (myf $x) (wrap $x))"; mode = :relational) ==
              raw"(exec 0 (, (myf $x)) (, (wrap $x)))"          # default unchanged (forward-closure)
        @test_throws ErrorException mm2_lower_equals(raw"(= (myf $x) (wrap $x))"; mode = :bogus)

        # end-to-end: reduction DELETES the redex, relational KEEPS it (both add the reduct)
        prog = "(= (myf \$x) (wrap \$x))\n(myf a)\n"
        dmp(cs) = [strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n') if !isempty(strip(l))]
        csR = MC.new_core_space(); MC.mc_run(csR, "", prog; eq_mode = :reduction); dR = dmp(csR)
        @test ("(wrap a)" in dR) && !("(myf a)" in dR)         # reduct added, redex CONSUMED
        csK = MC.new_core_space(); MC.mc_run(csK, "", prog; eq_mode = :relational); dK = dmp(csK)
        @test ("(wrap a)" in dK) && ("(myf a)" in dK)          # reduct added, redex KEPT (default)
    end

    # ── piece 3b: string-literal-safe splitters (mm2_expr_args / mm2_split_forms) ──
    @testset "splitters treat \"…\" as opaque (no split on interior spaces/parens)" begin
        # mm2_expr_args: a top-level string with spaces stays ONE arg (was mis-split at the space)
        @test mm2_expr_args(raw"""(= (f x) "hello world")""") == ["=", "(f x)", "\"hello world\""]
        @test mm2_expr_args(raw"""(f "a b c" y)""")           == ["f", "\"a b c\"", "y"]
        # parens INSIDE a string must not corrupt paren-depth
        @test mm2_expr_args(raw"""(concat "(" ")")""")         == ["concat", "\"(\"", "\")\""]
        # escaped quote inside a string does not close it early (normal string: \\\" ⇒ a real \" pair)
        @test mm2_expr_args("(f \"a\\\"b\" y)")                == ["f", "\"a\\\"b\"", "y"]
        # mm2_split_forms: a '(' inside a string literal must not break the form boundary
        @test [f for (b, f) in mm2_split_forms("(f \"a (b\" y)\n(g z)")] == ["(f \"a (b\" y)", "(g z)"]
        # end-to-end: a bare top-level string RHS lowers as a single reduct (relational + reduction)
        @test mm2_lower_equals(raw"""(= (name $x) "John Doe")""") ==
              raw"""(exec 0 (, (name $x)) (, "John Doe"))"""
        @test mm2_lower_equals(raw"""(= (name $x) "John Doe")"""; mode = :reduction) ==
              raw"""(exec 0 (I (name $x)) (O (+ "John Doe") (- (name $x))))"""
    end

    # ── piece 3c: (= (f …) ARITH) arith body → pure-sink reduction (Phase-2, R7 lane-1; int + float) ──
    @testset "arith (=) body → MM2 pure-sink (i64 + f64); bisimulates the interpreter" begin
        SM = MeTTaCore.Interpreter
        # classifier: + - * % (int) and / + float literals (float) are arith; reduction/relational/control aren't
        @test mm2_is_arith_body(raw"(= (f $x) (+ $x 3))")
        @test mm2_is_arith_body(raw"(= (f $x) (+ (* $x 2) 1))")          # nested tree
        @test mm2_is_arith_body(raw"(= (g $x $y) (- (* $x $y) 1))")      # arity-2 + nested
        @test mm2_is_arith_body(raw"(= (f $x) (/ $x 2))")               # / ⇒ i64 mode (conformant 2026-08-06)
        @test mm2_is_arith_body(raw"(= (g $x) (+ $x 1.5))")            # float literal ⇒ FLOAT mode
        # 🔴 BOUNDARY MOVED 2026-08-06. This asserted REJECTION while `/` forced f64 and `%` was int-only,
        # so a mixed tree could not be typed. `/` on integers is now i64 division (NumericSeam.seam_div;
        # hyperon arithmetics.rs:154-155), so both share a mode and the tree IS typeable — a widened
        # boundary, not a regression.
        @test mm2_is_arith_body(raw"(= (f $x) (+ (/ $x 2) (% $y 3)))")   # both i64 now → accepted
        @test !mm2_is_arith_body(raw"(= (id $x) $x)")                   # bare-var RHS = reduction, not arith
        @test !mm2_is_arith_body(raw"(= (ancestor $x $y) (parent $x $y))")  # relational, not arith
        @test !mm2_is_arith_body(raw"(= (f $x) (+ $x a))")             # non-numeric leaf `a`
        @test !mm2_is_arith_body(raw"(foo $x)")                         # not a (= …) form

        # lowering: leaves→<t>_from_string, root→<t>_to_string, redex deleted via (- LHS)
        @test mm2_lower_equals_arith(raw"(= (f $x) (+ $x 3))") ==       # INT: i64 ops
              raw"(exec 0 (I (f $x)) (O (pure $__r $__r (i64_to_string (sum_i64 (i64_from_string $x) (i64_from_string 3)))) (- (f $x))))"
        @test mm2_lower_equals_arith(raw"(= (f $x) (/ $x 2))") ==       # INT: i64 ops (div_i64)
              raw"(exec 0 (I (f $x)) (O (pure $__r $__r (i64_to_string (div_i64 (i64_from_string $x) (i64_from_string 2)))) (- (f $x))))"

        # bisimulation: the MORK pure-sink reduct == the interpreter's normal form (Int64 / Float64), redex DELETED
        bisim(rule, call) = begin
            cs = MC.new_core_space()
            MC.space_add_all_sexpr!(cs.inner, call)
            MC.space_add_all_sexpr!(cs.inner, mm2_lower_equals_arith(rule))
            MC.space_metta_calculus!(cs.inner, 1_000_000)
            dump = [strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n') if !isempty(strip(l))]
            isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, rule)
            res = SM.load_metta!(isp, "!" * call)
            interp = [string(x) for r in res for x in (r isa AbstractVector ? r : [r])]
            (dump, interp)
        end
        for (rule, call, val) in [
                (raw"(= (f $x) (+ $x 3))",       "(f 5)",   "8"),      # INT
                (raw"(= (f $x) (- $x 3))",       "(f 5)",   "2"),
                (raw"(= (f $x) (* $x 3))",       "(f 5)",   "15"),
                (raw"(= (f $x) (% $x 3))",       "(f 10)",  "1"),
                (raw"(= (f $x) (+ (* $x 2) 1))", "(f 5)",   "11"),
                (raw"(= (g $x $y) (+ $x $y))",   "(g 3 4)", "7"),
                (raw"(= (f $x) (/ $x 2))",       "(f 10)",  "5"),      # Int÷Int = INTEGER division (conformant 2026-08-06)
                (raw"(= (f $x) (/ $x 3))",       "(f 10)",  "3"),      # truncating: hyperon Number::Integer(a/b)
                (raw"(= (g $x) (+ $x 1.5))",     "(g 2)",   "3.5"),    # float literal; int arg promoted
                (raw"(= (h $x) (* $x 2.0))",     "(h 3)",   "6.0"),
                (raw"(= (k $x) (/ (+ $x 1) 2))", "(k 9)",   "5")]      # nested, stays i64
            dump, interp = bisim(rule, call)
            @test interp == [val]                          # interpreter-oracle sanity
            @test val in dump                              # MM2 pure-sink computed the same value
            @test !(strip(call) in dump)                   # redex DELETED (reduction, not accumulation)
        end
    end

    # ── piece 3d: unified (=)→MM2 reduction dispatch + interpreter-oracle bisim harness ──
    @testset "mm2_lower_eq dispatch + mm2_eq_bisim interpreter-oracle harness" begin
        # dispatch: arithmetic body → arith pure-sink lowering; else → reduction form
        @test mm2_lower_eq(raw"(= (f $x) (+ $x 3))") == mm2_lower_equals_arith(raw"(= (f $x) (+ $x 3))")
        @test mm2_lower_eq(raw"(= (f $x) (/ $x 2))") == mm2_lower_equals_arith(raw"(= (f $x) (/ $x 2))")  # i64 div
        @test mm2_lower_eq(raw"(= (id $x) $x)") == mm2_lower_equals(raw"(= (id $x) $x)"; mode = :reduction)

        # the harness: MORK reduct set-equals the interpreter normal form across the reduction/arith subset
        for (rule, query) in [
                (raw"(= (id $x) $x)",            "(id a)"),        # symbolic identity
                (raw"(= (dup $x) (pair $x $x))", "(dup a)"),       # shared-var template duplication
                (raw"(= (f $x) (+ $x 3))",       "(f 5)"),         # int arith
                (raw"(= (f $x) (/ $x 2))",       "(f 10)"),        # integer division
                (raw"(= (k $x) (/ (+ $x 1) 2))", "(k 9)")]         # nested i64
            r = mm2_eq_bisim(rule, query)
            @test r.ok                                             # MORK reduct ≡ interpreter normal form
            @test r.reduct == r.interp
        end
        # the harness CATCHES divergence: a rule that does not apply to the query → ok=false (redex kept, no reduct)
        d = mm2_eq_bisim(raw"(= (id $x) $x)", "(other 5)")
        @test !d.ok && isempty(d.reduct) && d.interp == ["(other 5)"]
    end

    # ── piece 4: grounded-op guard + auto-routing of (= …) rules in mm2_partition ──
    @testset "grounded-op guard classifies relational vs grounded rules" begin
        @test mm2_is_relational(raw"(= (ancestor $x $y) (parent $x $y))")        # plain relations
        @test mm2_is_relational(raw"(= (, (p $x) (q $x)) (r $x))")               # conjunctive, relational
        @test !mm2_is_relational(raw"(= (fib $n) (+ (fib (- $n 1)) (fib (- $n 2))))")  # + ⇒ grounded
        @test !mm2_is_relational(raw"(= (dbl $x) (* $x 2))")                     # * ⇒ grounded
        @test !mm2_is_relational(raw"(= (q $x) (match &self (p $x) $x))")        # match ⇒ special
        @test !mm2_is_relational(raw"(= (c $x) (chain $x))")                     # chain ⇒ MINIMAL_OPS
        @test !mm2_is_relational(raw"(foo $x)")                                  # not a (= …) form
    end

    # ── REGRESSION: the gate was FAIL-OPEN on NESTED operator positions ────────────────────────
    # Every assertion above has a FLAT body, which is exactly why the hole survived. `mm2_collect_heads!`
    # pushed `args[1]` verbatim — opaque even when compound — and never descended into it, so a grounded
    # op sitting in a nested OPERATOR slot was invisible to a classifier whose docstring promises "EVERY
    # operator-position head". Measured consequence, all defaults, no opt-in flag:
    #     (= (f $x) (let* (($y (+ $x 1))) $y))
    #       heads = ["f","let*","($y (+ $x 1))"]   ← `+` NEVER SEEN, `($y …)` opaque
    #       ⇒ relational=true ⇒ gate (1) passes ⇒ ZAM SERVES the bang
    #       interpreter !(f 5) = 6   but   mc_run = "(let* (($ (+ 5 1))) _1)"   ← SILENT WRONG ANSWER
    # `evaluated = vcat(zam.served, _mc_fallback_eval(…))` (DualTrack.jl:156-157), so a ZAM-served bang
    # never reaches the interpreter to be corrected. Blast radius when found: of 899 `(=)` rules across
    # 75 production `.metta` files, 345 were admitted; after the fix 290 are — so 55 were being admitted
    # on a false classification. (Not zero, which is the datum that says PATCH the gate rather than
    # delete the lane.)
    @testset "grounded-op guard: NESTED operator positions (fail-open regression)" begin
        # the exact reproducer — a grounded op two levels down, inside an operator slot
        @test !mm2_is_relational(raw"(= (f $x) (let* (($y (+ $x 1))) $y))")
        # the head list must now actually CONTAIN the op it previously missed
        let hs = String[]
            MC.mm2_collect_heads!(hs, raw"(let* (($y (+ $x 1))) $y)")   # not exported — qualify
            @test "+" in hs                       # was absent ⇒ the classifier could not see it
        end
        # a COMPOUND in operator position is never a plain relation symbol, on its own
        @test !mm2_is_relational(raw"(= (f $x) ((g $x) 1))")

        # the four special forms that are in NEITHER TOKEN_REGISTRY NOR MINIMAL_OPS — enumerated by
        # execution, not by reading. Before the fix each was treated as an ordinary relation symbol.
        @test !mm2_is_relational(raw"(= (f $x) (if $x a b))")
        @test !mm2_is_relational(raw"(= (f $x) (let $y $x $y))")
        @test !mm2_is_relational(raw"(= (f $x) (let* (($y $x)) $y))")
        @test !mm2_is_relational(raw"(= (f $x) (quote $x))")

        # NO OVER-REJECTION: genuinely relational rules, including a nested CONSTRUCTOR (not an op)
        # in the RHS, must still be admitted — otherwise the fix would silently disable the lane.
        @test mm2_is_relational(raw"(= (p $x) (q $x))")
        @test mm2_is_relational(raw"(= (edge $x $y) (path $x $y))")
        @test mm2_is_relational(raw"(= (add (S $x) $y) (S (add $x $y)))")

        # END-TO-END: mc_run must now agree with the interpreter on the reproducer (defaults only).
        let cs = MeTTaCore.new_core_space()
            r = MeTTaCore.mc_run(cs, "", raw"(= (f $x) (let* (($y (+ $x 1))) $y))" * "\n!(f 5)")
            @test isempty(r.results.zam_served)                  # the ZAM must DEFER, not serve
            @test r.results.evaluated == [("(f 5)", ["6"])]      # …and the answer is the interpreter's
        end
    end

    @testset "mm2_partition auto-routes relational (= …), leaves grounded in data" begin
        # relational rule auto-lowered into exec; fact stays data
        p = mm2_partition("(ancestor a b)\n" * raw"(= (ancestor $x $y) (parent $x $y))")
        @test length(p.exec) == 1 && occursin("exec 0", p.exec[1])
        @test p.data == ["(ancestor a b)"]
        # arith-body rule: NOW auto-lowered to a pure-sink reduction exec (Phase-2 wired, arith_exec
        # default ON — interpreter-bisim-proven lowering); the kill switch restores the old routing
        pg = mm2_partition(raw"(= (fib $n) (+ $n 1))")
        @test length(pg.exec) == 1 && occursin("(pure ", pg.exec[1]) && isempty(pg.data)
        pg0 = mm2_partition(raw"(= (fib $n) (+ $n 1))"; arith_exec = false)
        @test isempty(pg0.exec) && pg0.data == [raw"(= (fib $n) (+ $n 1))"]
        # non-arith grounded rule (if/<) still stays in the data lane (interpreter territory)
        pif = mm2_partition(raw"(= (f $n) (if (< $n 2) $n 0))")
        @test isempty(pif.exec) && length(pif.data) == 1
        # end-to-end: a program with a relational (= …) rule now fires through the MORK lane unaided
        cs = MC.new_core_space()
        mm2_run!(cs, "(ancestor a b)\n(ancestor b c)\n" * raw"(= (ancestor $x $y) (parent $x $y))")
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]
    end

    @testset "arith (=) auto-wire: pure-sink exec E2E + interpreter bisim (piece 4b)" begin
        # E2E on the MM2 lane: the wired arith rule REDUCES a matching data atom at the substrate
        cs = MC.new_core_space()
        mm2_run!(cs, "(inc 41)\n" * raw"(= (inc $x) (+ $x 1))")
        d = [strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n') if !isempty(strip(l))]
        @test "42" in d && !("(inc 41)" in d)      # value written, redex consumed (reduction semantics)
        # bisim locks: the wired lowering ≡ the interpreter oracle (int + float promotion)
        @test mm2_eq_bisim(raw"(= (inc $x) (+ $x 1))", "(inc 41)").ok
        @test mm2_eq_bisim(raw"(= (half $x) (/ $x 4))", "(half 10)").ok   # f64 path: 2.5
    end

    @testset "auto-router default = :reduction (interpreter-faithful); :relational is opt-in" begin
        prog = "(ancestor a b)\n" * raw"(= (ancestor $x $y) (parent $x $y))"
        derived(cs, head) = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                                         if occursin(head, l)]))
        # DEFAULT (:reduction): parent derived AND the ancestor redex CONSUMED — matches the interpreter's
        # !(ancestor a b) → (parent a b) reduce-to-normal-form (MeTTa `(=)` is a reduction relation, not Datalog).
        csR = MC.new_core_space(); mm2_run!(csR, prog)
        @test derived(csR, "parent") == ["(parent a b)"]
        @test derived(csR, "ancestor") == String[]                 # redex deleted (reduce-to-normal-form)
        # OPT-IN (:relational): forward-REWRITING closure — parent added, ancestor KEPT (bisimulates !(match …)).
        csK = MC.new_core_space(); mm2_run!(csK, prog; eq_mode = :relational)
        @test derived(csK, "parent") == ["(parent a b)"]
        @test derived(csK, "ancestor") == ["(ancestor a b)"]       # source retained (keep-LHS)
        # mc_run's direct lane inherits the same reduction default
        csM = MC.new_core_space(); MC.mc_run(csM, "", prog)
        @test derived(csM, "ancestor") == String[] && derived(csM, "parent") == ["(parent a b)"]
    end

    # ── piece 5: typed Atom → MM2 sexpr (the live-eval handoff converter) ──
    @testset "typed_atom_to_expr round-trips to mm2_lower_equals" begin
        SM = MeTTaCore.Interpreter
        for s in [raw"(= (ancestor $x $y) (parent $x $y))",
                  raw"(= (, (p $x) (q $x)) (r $x))",
                  raw"(= (sym a) (sym b))",
                  raw"(= (dbl $x) (twice $x $x))"]
            atom = SM.parse_program(s)[1][2]                  # the parsed (= …) Atom
            e = typed_atom_to_expr(atom)
            @test mm2_lower_equals(e) == mm2_lower_equals(s)  # serialize→lower == lower(source)
        end
        # end-to-end: a parsed Atom rule, serialized, fires through the MORK lane and bisimulates
        atom = SM.parse_program(raw"(= (ancestor $x $y) (parent $x $y))")[1][2]
        cs = MC.new_core_space()
        MC.space_add_all_sexpr!(cs.inner, "(ancestor a b)\n(ancestor b c)")
        MC.space_add_all_sexpr!(cs.inner, mm2_lower_equals(typed_atom_to_expr(atom)))
        MC.space_metta_calculus!(cs.inner, 1_000_000)
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]
    end

    # ── piece 6: live-eval handoff — typed-Atom guard + MORK mirror lane (mirror, bisim-safe) ──
    @testset "mm2_is_relational(Atom) + mm2_lane_from_atoms bisimulates interpreter" begin
        SM = MeTTaCore.Interpreter
        @test mm2_is_relational(SM.parse_program(raw"(= (ancestor $x $y) (parent $x $y))")[1][2])
        @test !mm2_is_relational(SM.parse_program(raw"(= (fib $n) (+ $n 1))")[1][2])   # grounded
        @test !mm2_is_relational(SM.parse_program("(ancestor a b)")[1][2])             # a fact, not a rule

        prog  = "(ancestor a b)\n(ancestor b c)\n" * raw"(= (ancestor $x $y) (parent $x $y))"
        atoms = [p[2] for p in SM.parse_program(prog)]
        cs = mm2_lane_from_atoms(atoms)                       # build the MORK mirror from typed atoms
        MC.space_metta_calculus!(cs.inner, 1_000_000)
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]

        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, "(ancestor a b)\n(ancestor b c)")
        res = SM.load_metta!(isp, raw"!(match &self (ancestor $x $y) (parent $x $y))")
        R_interp = sort(unique(filter(s -> occursin("parent", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R == R_interp                                  # MORK mirror lane ≡ interpreter oracle
    end

    # ── piece 7: P2 route gate — broad single-step bisimulation + the chain boundary + lane_from_space ──
    @testset "P2 route gate: broad bisimulation + forward-closure boundary" begin
        SM = MeTTaCore.Interpreter
        mork_derive(facts, rule, head) = begin
            atoms = [p[2] for p in SM.parse_program(facts * "\n" * rule)]
            cs = mm2_lane_from_atoms(atoms); MC.space_metta_calculus!(cs.inner, 1_000_000)
            sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n') if occursin(head, l)]))
        end
        interp_match(facts, lhs, rhs, head) = begin
            isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
            res = SM.load_metta!(isp, "!(match &self $lhs $rhs)")
            sort(unique(filter(s -> occursin(head, s),
                [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        end
        # SINGLE-STEP shapes — MORK mirror saturate ≡ interpreter !(match)
        for (facts, lhs, rhs, head) in [
                ("(ancestor a b)\n(ancestor b c)", raw"(ancestor $x $y)", raw"(parent $x $y)", "parent"),
                ("(rel p q)\n(rel q r)",           raw"(rel $x $y)",      raw"(link $x $y)",   "link"),
                ("(parent a b)\n(parent b c)",     raw"(, (parent $x $y) (parent $y $z))",
                                                   raw"(grandparent $x $z)", "grandparent")]
            @test mork_derive(facts, "(= $lhs $rhs)", head) == interp_match(facts, lhs, rhs, head)
        end
        # BOUNDARY (documented): a multi-rule chain → MORK forward CLOSURE {b,c}, by design (Datalog),
        # NOT the interpreter's (=) reduction normal-form (c). This bounds what ROUTE may soundly do.
        chain = mork_derive("(a 1)", raw"(= (a $x) (b $x))" * "\n" * raw"(= (b $x) (c $x))", "")
        @test ("(b 1)" in chain) && ("(c 1)" in chain)

        # mm2_lane_from_space — mirror a LIVE Space's own atoms (excludes stdlib)
        isp = SM.Space(); SM.load_core_stdlib!(isp)
        SM.load_metta!(isp, "(ancestor a b)\n(ancestor b c)\n" * raw"(= (ancestor $x $y) (parent $x $y))")
        cs = mm2_lane_from_space(isp); MC.space_metta_calculus!(cs.inner, 1_000_000)
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]
    end

    # ── piece 8: mm2_lane_saturate! — recursive Datalog fixpoint (transitive closure) ──
    @testset "mm2_lane_saturate! computes the full transitive closure (recursion driver)" begin
        SM = MeTTaCore.Interpreter
        prog = "(edge a b)\n(edge b c)\n(edge c d)\n" *
               raw"(= (edge $x $y) (reach $x $y))" * "\n" *
               raw"(= (, (edge $x $y) (reach $y $z)) (reach $x $z))"
        atoms = [p[2] for p in SM.parse_program(prog)]
        reach(cs) = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                                 if occursin("reach", l)]))
        # single-pass MISSES the 3-hop (exec consumed after one fire — MM2 spec)
        cs1 = mm2_lane_from_atoms(atoms); MC.space_metta_calculus!(cs1.inner, 1_000_000)
        @test !("(reach a d)" in reach(cs1))
        # the fixpoint driver reaches the full closure (re-fire until stable)
        R = sort(string.(reach(mm2_lane_saturate!(atoms))))
        @test R == sort(["(reach a b)", "(reach b c)", "(reach c d)",
                         "(reach a c)", "(reach b d)", "(reach a d)"])
    end

    # ── piece 8b: mm2_lane_saturate_seminaive! — Zippy finite-difference fixpoint ≡ naive driver ──
    @testset "mm2_lane_saturate_seminaive! computes the SAME closure as the naive driver" begin
        SM = MeTTaCore.Interpreter
        prog = "(edge a b)\n(edge b c)\n(edge c d)\n" *
               raw"(= (edge $x $y) (reach $x $y))" * "\n" *
               raw"(= (, (edge $x $y) (reach $y $z)) (reach $x $z))"
        atoms = [p[2] for p in SM.parse_program(prog)]
        reach(cs) = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                                 if occursin("reach", l)]))
        expected = sort(["(reach a b)", "(reach b c)", "(reach c d)",
                         "(reach a c)", "(reach b d)", "(reach a d)"])
        @test reach(mm2_lane_saturate_seminaive!(atoms)) == expected            # full closure, incl 3-hop
        # ≡ the naive driver, fact-for-fact
        @test reach(mm2_lane_saturate_seminaive!(atoms)) == reach(mm2_lane_saturate!(atoms))
        # no (d …) delta-tag artifacts leak into the final space
        @test !any(l -> startswith(strip(l), "(d "),
                   split(MC.space_dump_all_sexpr(mm2_lane_saturate_seminaive!(atoms).inner), '\n'))
        # derived-relation analysis + variant generation (the semi-naive transform)
        @test MeTTaCore._mm2_derived_relations(
            ["(exec 0 (, (edge \$x \$y) (reach \$y \$z)) (, (reach \$x \$z)))"]) == Set(["reach"])
        vs = MeTTaCore._mm2_seminaive_variants(
            "(exec 0 (, (edge \$x \$y) (reach \$y \$z)) (, (reach \$x \$z)))", Set(["reach"]))
        @test vs == ["(exec 0 (, (edge \$x \$y) (d (reach \$y \$z))) (, (reach \$x \$z)))"]  # only derived premise tagged
        # non-recursive rule (no derived premise) → no variant → falls back to naive seed pass
        @test isempty(MeTTaCore._mm2_seminaive_variants(
            "(exec 0 (, (edge \$x \$y)) (, (reach \$x \$y)))", Set(["reach"])))
    end

    # ── piece 9: MORK byte-Expr limit guard (arity 63 / 64 vars — wiki Data-in-MORK) ──
    @testset "mm2_is_relational rejects rules exceeding MORK byte-Expr limits" begin
        SM = MeTTaCore.Interpreter
        @test mm2_is_relational(SM.parse_program(raw"(= (ancestor $x $y) (parent $x $y))")[1][2])  # within limits
        over_arity = "(= (big " * join(["a$i" for i in 1:70], " ") * ") (ok))"      # 71-child LHS > 63
        @test !mm2_is_relational(SM.parse_program(over_arity)[1][2])
        over_vars = "(= (f " * join(["\$v$i" for i in 1:70], " ") * ") (g))"        # 70 distinct vars > 64
        @test !mm2_is_relational(SM.parse_program(over_vars)[1][2])
    end

    # ── piece 10: mc_closure! — opt-in substrate route, Datalog closure materialized into a live Space ──
    @testset "mc_closure! materializes the transitive closure for the interpreter to query" begin
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp)
        SM.load_metta!(isp, "(edge a b)\n(edge b c)\n(edge c d)\n" *
            raw"(= (edge $x $y) (reach $x $y))" * "\n" *
            raw"(= (, (edge $x $y) (reach $y $z)) (reach $x $z))")
        @test mc_closure!(isp) == 6                              # 6 derived reach atoms materialized
        res = SM.load_metta!(isp, raw"!(match &self (reach $x $y) (reach $x $y))")
        reach = sort(unique(filter(s -> startswith(s, "(reach"),
            [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test length(reach) == 6                                # interpreter now queries the full closure
        @test "(reach a d)" in reach                            # incl. the 3-hop only the fixpoint finds
    end

    # ── piece 11: our MORK is MM2-idiom-complete (canonical idioms from MM2_Structuring_Code tutorial) ──
    @testset "MORK supports the canonical MM2 idioms (O-sink / priority / chaining / native recursion)" begin
        run1(prog) = begin
            cs = MC.new_core_space(); MC.space_add_all_sexpr!(cs.inner, prog)
            n = MC.space_metta_calculus!(cs.inner, 100000)
            (sort([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n') if !isempty(strip(l))]), n)
        end
        # O-sink REMOVAL — (exec 0 (, $x) (O (- b))) over {a,b} ⇒ b removed (non-monotonic)
        R, _ = run1(raw"(exec 0 (, $x) (O (- b)))" * "\na\nb")
        @test R == ["a"]
        # PRIORITIES — two no-op execs both consumed
        R, n = run1("(exec 0 (,) (,))\n(exec 1 (,) (,))")
        @test isempty(R) && n == 2
        # EXEC CHAINING (sequence) — nested execs emit 0,1,2,3 in order. The bootstrap exec needs a REAL
        # trigger atom (`start`): per the MM2 calculus (upstream `metta_calculus` removes the exec BEFORE
        # `interpret` matches its source, and matches are value-presence-gated — `path_exists`), an exec whose
        # source `(, $x)` has no atom to bind after self-removal does NOT fire. (Matching the removed exec
        # itself was the pre-`16981af` dangling-node bug that made Control_08 non-terminate.)
        R, _ = run1(raw"(exec 0 (, start) (, 0 (exec 0 (, 0) (, 1 (exec 0 (, 1) (, 2 (exec 0 (, 2) (, 3))))))))" * "\nstart")
        @test all(x -> x in R, ["0", "1", "2", "3"])             # full cascade fires (trigger `start` remains)
        # NATIVE RECURSION + HALTING — self-re-adding LOOP decrements (S(S(S Z)))→Z and halts (the MM2-native
        # fixpoint idiom; proves the host re-add loop in mm2_lane_saturate! is a shortcut, not a necessity)
        loop = raw"""
        (counter (S (S (S Z))))
        (exec (LOOP 9)
           (, (exec (LOOP 9) $p $t) )
           (O (+ (exec (LOOP 0) (, (exec (LOOP $n) $_p $_t) (counter Z)) (O (- (exec (LOOP $n) $_p $_t)))))
              (+ (exec (LOOP 1) (, (counter (S $x))) (O (+ (counter $x)) (- (counter (S $x))))))
              (+ (exec (LOOP 9) $p $t))))
        """
        R, n = run1(loop)
        @test ("(counter Z)" in R) && (n < 100000)            # terminated (didn't hit the step cap)
    end

    # ── piece 12: (mork-closure) grounded op — invoke the substrate route from MeTTa SOURCE ──
    @testset "(mork-closure) grounded op runs the substrate route from MeTTa" begin
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp)
        SM.load_metta!(isp, "(edge a b)\n(edge b c)\n(edge c d)\n" *
            raw"(= (edge $x $y) (reach $x $y))" * "\n" *
            raw"(= (, (edge $x $y) (reach $y $z)) (reach $x $z))")
        SM.load_metta!(isp, "!(mork-closure)")               # ← invoke the substrate route FROM MeTTa text
        res = SM.load_metta!(isp, raw"!(match &self (reach $x $y) (reach $x $y))")
        reach = sort(unique(filter(s -> startswith(s, "(reach"),
            [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test length(reach) == 6 && ("(reach a d)" in reach)  # full closure, queryable by the interpreter
    end

    @testset "mm2_route! full dispatch (data + exec + !match + deferred)" begin
        cs = MC.new_core_space()
        prog2 = facts * "\n" * rule * "\n" *
                raw"!(match &self (trans $a $b) (reached $a $b))" * "\n" * raw"!(+ 1 2)"
        r = mm2_route!(cs, prog2)
        @test r.n_data == 3 && r.n_exec == 1
        @test length(r.matched) == 1                       # the !(match …) routed to the MM2 lane
        @test r.matched[1][2] == ["(reached 0 2)", "(reached 1 3)"]
        @test r.deferred == [raw"(+ 1 2)"]                 # non-match ! → interpreter lane (deferred)
    end

    @testset "expr_to_atom — byte-level de Bruijn round-trip (co-reference reconstruction)" begin
        M = MeTTaCore.StandardMeTTa
        # (= (f $x) $x): both $x are ONE Var; typed→bytes→typed must return them co-referential.
        vx = M.Var("x")
        a  = M.Expression(M.Atom[M.Sym("="), M.Expression(M.Atom[M.Sym("f"), vx]), vx])
        e  = MC.sexpr_to_expr(typed_atom_to_expr(a))
        a2 = expr_to_atom(e)
        @test a2.children[2].children[2] === a2.children[3]          # co-reference RECONSTRUCTED
        # alpha-variants collapse to identical bytes (storage dedup); distinct vars do not.
        @test MC.sexpr_to_expr(raw"(= (f $x) $x)").buf == MC.sexpr_to_expr(raw"(= (f $y) $y)").buf
        @test MC.sexpr_to_expr(raw"(f $x $y)").buf != MC.sexpr_to_expr(raw"(f $x $x)").buf
        # DISTINCT vars, SAME base name (id 0 vs 7, as rename_fresh produces) must NOT collapse.
        d  = M.Expression(M.Atom[M.Sym("f"), M.Var("x", UInt64(0)), M.Var("x", UInt64(7))])
        dr = expr_to_atom(MC.sexpr_to_expr(typed_atom_to_expr(d)))
        @test dr.children[2] !== dr.children[3]
        # complementary direction (fix must NOT over-correct): the SAME renamed var (id≠0) twice MUST co-refer.
        v7 = M.Var("x", UInt64(7))
        cr = expr_to_atom(MC.sexpr_to_expr(typed_atom_to_expr(M.Expression(M.Atom[M.Sym("f"), v7, v7]))))
        @test cr.children[2] === cr.children[3]
        # symbols route through parse_atom: numbers rebuild as Grounded (not Sym).
        a3 = expr_to_atom(MC.sexpr_to_expr(raw"(f 42 $x)"))
        @test a3.children[2] isa M.Grounded && a3.children[2].value == 42
        @test a3.children[1] isa M.Sym && a3.children[3] isa M.Var
        # atom → bytes → atom → bytes is a fixpoint (write/read consistency).
        @test MC.sexpr_to_expr(typed_atom_to_expr(expr_to_atom(e))).buf == e.buf
        # THIRD direction: a synthetic var must NOT capture a source var of the same spelling (`$_0`).
        rv = expr_to_atom(MC.sexpr_to_expr(raw"(f $x)")).children[2]   # reconstructed ⇒ synthetic var
        @test rv isa M.Var && rv.id != 0                              # synthetic ⇒ id≠0 by construction
        @test rv != M.Var("_0", UInt64(0))                            # ≠ a source var written $_0 (id 0)
    end
end
