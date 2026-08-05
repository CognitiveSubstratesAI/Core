# Core has TWO grounded-op registries, and nothing kept them in agreement until this file.
#
#   MORK.GROUNDED_REGISTRY      (MORK/src/kernel/Sources.jl:289)  Dict{String,Function}
#       (args::Vector{String}) -> Union{String, Vector{String}, Nothing}
#       populated by `register_core_primitives!` (Core/src/primitives/Primitives.jl), consumed by
#       `GroundedSource` in MORK's query engine — i.e. the COMPILER/substrate lane.
#
#   Interpreter.TOKEN_REGISTRY  (Core/src/standard/Interpreter.jl:2375)  Dict{String,Atom}
#       (xs::Vector{Atom}) -> ExecResult
#       consumed by the interpreter's eval loop — i.e. the FALLBACK lane.
#
# Different calling conventions are the DESIGN, not a defect. Two lanes computing DIFFERENT ANSWERS
# for the same expression is the defect, and it was real (measured 2026-07-29): the MORK side parsed
# every argument as Float64, so
#     (* 123456789 987654321) -> 121932631112635264   exact 121932631112635269   off by 5
#     (+ 9007199254740993 1)  -> 9007199254740992     exact 9007199254740994     off by 2
#     (+ 1.5 2.5)             -> 4                    interpreter 4.0   <- a DIFFERENT ATOM
# The interpreter is the reference here: it is the lane gated by the 234-directive hyperon
# conformance matrix and the LeaTTa proved oracle.
using MeTTaCore, Test
const MCg = MeTTaCore
const INg = MeTTaCore.Interpreter
const MKg = MeTTaCore.MORK

@testset "grounded registries agree" begin
    MCg.register_core_primitives!()
    G = MKg.GROUNDED_REGISTRY

    "run an op through the MORK grounded registry"
    gcall(op, args) = G[op](String[string(a) for a in args])

    "run the same op through the interpreter, as real MeTTa evaluation"
    function icall(op, args)
        sp = INg.Space(); INg.load_core_stdlib!(sp)
        q = "!(" * op * " " * join(string.(args), " ") * ")"
        [string(x) for x in INg.metta_run(INg.parse_program(q)[1][2], sp)]
    end

    @testset "INTEGER arithmetic is EXACT (was done in Float64 ⇒ wrong past 2^53)" begin
        @test gcall("*", [123456789, 987654321])      == "121932631112635269"
        @test gcall("+", [9007199254740993, 1])       == "9007199254740994"
        @test gcall("+", [9007199254740992, 1])       == "9007199254740993"
        # …and the same defect hit COMPARISON: two distinct Int64s above 2^53 coerced to one Float64
        @test gcall("<", [9007199254740993, 9007199254740994]) == "True"
        @test gcall("==", [9007199254740993, 9007199254740994]) == "False"
    end

    @testset "FLOAT results keep their type — `4` and `4.0` are different ATOMS" begin
        @test gcall("+", [1.5, 2.5]) == "4.0"      # was "4"
        @test gcall("/", [10, 2])    == "5.0"      # was "5"
        @test gcall("+", [1, 2])     == "3"        # Int⊕Int stays Int
        @test MCg.from_sexpr("4")   isa Int64      # …which is why the distinction is observable
        @test MCg.from_sexpr("4.0") isa Float64
    end

    @testset "both lanes agree, op by op" begin
        cases = [("+", [1, 2]), ("+", [1.5, 2.5]), ("-", [5, 3]), ("*", [3, 4]),
                 ("/", [10, 3]), ("/", [10, 2]), ("%", [7, 3]),
                 ("<", [1, 2]), (">", [2, 1]), ("<=", [2, 2]), (">=", [1, 2]), ("==", [1, 1]),
                 ("*", [123456789, 987654321])]
        for (op, args) in cases
            mork = gcall(op, args)
            interp = icall(op, args)
            @test length(interp) == 1
            @test mork == interp[1]
        end
    end

    @testset "'not applicable' is signalled consistently AT THE REGISTRY BOUNDARY" begin
        # ⚠️ CORRECTED 2026-07-29. An earlier version of this comment claimed MORK's `nothing` and the
        # interpreter's `ExecNoReduce` "both mean leave it unreduced", i.e. were equivalent. They agree
        # at the REGISTRY boundary (both = "no result"), which is what the assertions below pin — but
        # their CONSUMERS diverge, so do not read this as semantic equivalence:
        #   ExecNoReduce -> the interpreter leaves the term unreduced; it is still in the answer.
        #   nothing      -> `GroundedSource` yields 0 paths, and `isempty(result_paths) && break`
        #                   (MORK/src/kernel/Space.jl:556) SILENTLY DROPS THE WHOLE JOIN MATCH —
        #                   no Error atom, no warning, the row just disappears.
        # Same signal, different blast radius. That is a real gap in the shim, tracked separately.
        @test gcall("+", [1])       === nothing        # wrong arity
        @test gcall("+", ["a", "b"]) === nothing        # non-numeric
        @test gcall("<", ["a", 1])  === nothing
    end

    @testset "*-math delegates to the hyperon-faithful implementation" begin
        # `CoreMathOps.jl` (Interpreter.jl:2520) implements this surface faithfully to
        # hyperon-experimental's lib/src/metta/runner/stdlib/math.rs and states its rules. The MORK
        # registry used to RE-IMPLEMENT all sixteen and diverged on 9 of 14 probed cases; it now
        # delegates. These assert the RULES, not just agreement, so a future re-implementation that
        # happens to agree on one case still fails.
        #
        # NOTE the division of labour, which is not duplication:
        #   CoreMathOps.jl   = hyperon stdlib grounded atoms  (this surface)
        #   NumpyOps.jl = the numpy-equivalent adapter  (norm/dotProduct/softmax/… ) —
        #                       a DIFFERENT surface, TOKEN_REGISTRY only, no MORK counterpart.

        # ALWAYS Float — even when the result is integral
        @test gcall("sqrt-math", [4])  == "2.0"        # was "2"
        @test gcall("sin-math", [0])   == "0.0"        # was "0"

        # PRESERVE type — Int stays Int, Float stays Float
        @test gcall("abs-math", [-5])     == "5"
        @test gcall("abs-math", [-5.5])   == "5.5"
        @test gcall("floor-math", [2.7])  == "2.0"     # was "2"
        @test gcall("ceil-math", [2.1])   == "3.0"     # was "3"
        @test gcall("trunc-math", [2.9])  == "2.0"     # was "2"

        # domain errors become NaN "like Rust f64" — they must NOT throw out of MeTTa
        @test gcall("sqrt-math", [-4]) == "NaN"        # was THREW DomainError
        @test gcall("asin-math", [2])  == "NaN"        # was THREW DomainError

        # symbols, not booleans
        @test gcall("isnan-math", [1]) == "False"
        @test gcall("isinf-math", [1]) == "False"

        # hyperon's log-math takes TWO arguments (base, value). The old copy took ONE and answered
        # `0` for (log-math 1); delegation makes it decline instead.
        @test gcall("log-math", [1]) === nothing

        # and every shared *-math op agrees with the interpreter on a normal input
        for (op, args) in [("sqrt-math", [4]), ("abs-math", [-5]), ("abs-math", [-5.5]),
                           ("floor-math", [2.7]), ("ceil-math", [2.1]), ("trunc-math", [2.9]),
                           ("round-math", [2.5]), ("sin-math", [0]), ("cos-math", [0]),
                           ("pow-math", [2, 3]), ("isnan-math", [1]), ("isinf-math", [1])]
            @test gcall(op, args) == icall(op, args)[1]
        end
    end

    @testset "arity is STRICTLY BINARY — extra args must not be silently ignored" begin
        # Was `length(args) < 2`, which admitted 2 OR MORE and then read only args[1..2]:
        #     (+ 1 2 3)  -> "3"     argument 3 silently dropped
        # The interpreter is strict (`length(xs) == 2 || ExecNoReduce`), so it left the term
        # unreduced. Now both refuse.
        for (op, args) in [("+", [1,2,3]), ("-", [10,1,1]), ("*", [2,3,4]), ("/", [8,2,2]),
                           ("%", [7,3,1]), ("<", [1,2,3]), (">", [3,2,1]), ("<=", [1,2,3]),
                           (">=", [3,2,1]), ("==", [1,1,9])]
            @test gcall(op, args) === nothing          # declines instead of truncating
        end
        # …and the binary cases still work
        @test gcall("+", [1,2]) == "3"
        @test gcall("<", [1,2]) == "True"
        # under-arity was already declined; keep it pinned
        @test gcall("+", [1]) === nothing
        @test gcall("+", Int[]) === nothing
    end

    @testset "mutable-state ops are ABSENT from the MORK lane, deliberately" begin
        # A String cannot be a LeaTTa `HostHandle`: `Registry.live : Nat -> Option Atom` requires an
        # identity that can be re-read, so a string transform can never observe a mutation, and an
        # unknown handle failed OPEN (it echoed its argument). Measured before removal:
        #     new-state 42 -> "(State 42)" ; change-state! -> "(State 99)" ; get-state -> "42" (stale)
        #     get-state "no-such-handle"   -> "no-such-handle"
        # LeaTTa proves the opposite: `passesHandle_missing_handle : passesHandle … = false`.
        for n in ["new-state", "get-state", "change-state!"]
            @test !haskey(G, n)                        # NOT registered ⇒ falls through to a trie source
            @test !MKg.is_grounded(n)
        end
        # Removing beats declining: a registered name returning `nothing` yields 0 paths and
        # `isempty(result_paths) && break` (MORK Space.jl:556) drops the whole join row silently.

        # The working implementation is the interpreter's, over a genuinely mutable StateCell.
        @test haskey(INg.TOKEN_REGISTRY, "new-state")
        @test haskey(INg.TOKEN_REGISTRY, "get-state")
        @test haskey(INg.TOKEN_REGISTRY, "change-state!")
        # and mm2_is_relational keeps these heads OFF the MORK lane, so nothing regressed
        @test MCg.mm2_is_relational(raw"(= (f $x) (get-state $x))") == false
    end

    @testset "_g2atom follows metta_grammar.ebnf, ALL productions — not just ATOM's four names" begin
        # docs/specs/metta_grammar.ebnf is the declared parser-of-record. The productions that bind
        # here, and which each one caught:
        #   ATOM      ::= SYMBOL | VARIABLE | GROUNDED | EXPRESSION
        #   GROUNDED  ::= STRING | WORD        <- a quoted STRING is GROUNDED, NOT Symbol. `_g2atom`
        #                                         had no STRING case, so `"hello"` became a Sym whose
        #                                         NAME included the quote characters.
        #   VARIABLE  ::= '$', (CHAR | '"'), {CHAR | '"'}
        #   WORD      ::= (CHAR | '#'), {CHAR | '"' | '#'}   <- '#' may LEAD, '"' is legal in the BODY
        #   CHAR      ::= any char except WHITESPACE and ( '"' | '#' | '(' | ')' | ';' )
        # Note GROUNDED and SYMBOL are SYNTACTICALLY IDENTICAL for the WORD case — the distinction is
        # semantic (numeric literal / known grounded name), not something the grammar can decide. That
        # is why the numeric probe below expects Grounded while the bare word expects Symbol.
        A = MCg.StandardMeTTa

        @test MCg._g2atom("42")      isa A.Grounded      # GROUNDED via numeric WORD
        @test MCg._g2atom("3.5")     isa A.Grounded
        @test MCg._g2atom("\"hi\"")  isa A.Grounded      # GROUNDED via STRING  (was Sym)
        @test MCg._g2atom("\"hi\"").value == "hi"        # …and unquoted, as parse_atom does
        @test MCg._g2atom("foo")     isa A.Sym           # SYMBOL
        @test MCg._g2atom("#tag")    isa A.Sym           # WORD may LEAD with '#'
        @test MCg._g2atom("fo\"o")   isa A.Sym           # '"' legal in a WORD body
        @test MCg._g2atom("\$x")     isa A.Var           # VARIABLE
        @test MCg._g2atom("__var_x") isa A.Var           # VARIABLE, Core's stored spelling
        @test MCg._g2atom("(A B)")   isa A.Expression    # EXPRESSION, via expr_to_atom

        # and the four kinds must be DISTINGUISHED, not merely constructed — this is the collapse
        # (SYMBOL == VARIABLE as one Julia Symbol) that SExprConvertible has and `__var_` patches.
        @test A.metatype(MCg._g2atom("foo"))     != A.metatype(MCg._g2atom("\$x"))
        @test A.metatype(MCg._g2atom("42"))      != A.metatype(MCg._g2atom("foo"))
        @test A.metatype(MCg._g2atom("(A B)"))   != A.metatype(MCg._g2atom("foo"))
        @test A.metatype(MCg._g2atom("\"hi\""))  == A.metatype(MCg._g2atom("42"))   # both GROUNDED
    end

    @testset "⚠️ KNOWN DIVERGENCE, pinned not fixed: (% x 0)" begin
        # MORK declines rather than crashing or inventing NaN (it used to return NaN, because
        # integer rem was being done in floats).
        @test gcall("%", [7, 0]) === nothing
        @test gcall("%", [7.0, 0.0]) == "NaN"          # float rem is genuinely NaN

        # The INTERPRETER throws a raw Julia DivideError — a HOST exception escaping into MeTTa
        # evaluation. That is wrong (MeTTa should see an Error atom, per "Error is poison"), but
        # what it should return instead needs the hyperon oracle, so it is pinned, not changed.
        @test_throws DivideError icall("%", [7, 0])
    end
end
