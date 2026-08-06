"""
NumericSeam — the ONE owner of the numeric boundary decisions.

## Why this module exists

Hyperon Whitepaper 2026 v5 §3.4 says a typed intermediate form exists to reduce ambiguity about
three things: **evaluation order**, **Space selection**, and **type conversion**. On 2026-08-05/06
each of those produced a defect here, independently:

  Space selection   `&self` resolved to the OLD Vector{Atom} store while `load_core_lib!` had
                    written the MORK trie — 30 constants read as "absent", all present.
  type conversion   `(/ 7 2)` → 3.5 where hyperon returns `Number::Integer(3)` and LeaTTa PROVES
                    `Ground.int (a / b)`; an out-of-range literal silently became a Float64.
  evaluation order  the interpreter's demand-driven innermost reduction vs MM2's order-agnostic
                    saturation (the merge design's open R1).

The cause is structural, not carelessness: **`+ - * / %` are implemented TWICE** —
`Interpreter.jl` `_num_binop` and `Primitives.jl` `_register_arithmetic!` — in different files, and
`MM2Router.jl`'s `_MM2_ARITH_I64`/`_MM2_ARITH_F64` decides a third time for the compiled lane. Three
sites, one semantics, no owner. They agree today only because someone hand-tuned the compiled lane
to bisimulate the interpreter (`MM2Router.jl:303`, "chosen to bisimulate the interpreter's own
promotion") — **including the interpreter's divergence from the reference**. So the bisim gate is
green while both lanes are wrong together, because its oracle is us.

This module is the missing owner. It is the same fix as `LibPolicy.lib_policy`: the ECAN constant
kept getting rewritten because nothing could be *asked*, and banners did not stop it — a reachable
single source of truth did.

## Decisions, not representations

Every function returns a DECISION. It never builds an atom, throws a MeTTa error, or knows what a
`Grounded` is — because its three callers need three different renderings (an interpreter error
atom, an MM2 sink value, a parser signal). Representation stays at the lane; only the *choice*
lives here. That is what makes one owner possible across files that cannot otherwise share types.

## Scope today

TYPE CONVERSION is implemented — it is the one that was measured. Evaluation order and Space
selection get named entry points below with no implementation, so they have a home when they are
tackled rather than being decided a fourth time in a fourth file.

## Conformance basis (verified, not assumed)

  hyperon-experimental 0.2.10  `lib/src/metta/runner/stdlib/arithmetics.rs:154-155`
      `(Number::Integer(_), Number::Integer(0)) => Err(ExecError::from("DivisionByZero"))`
      then `Ok(vec![Atom::gnd(Number::Integer(a / b))])`   ← Rust `/` on i64 = truncating
  LeaTTa (Lean, kernel-checked)  `MettaHyperonFull/Minimal/Stdlib.lean:86-101`
      `divOp | [int a, int b] => if b == 0 then Error … DivisionByZero
                                 else ReduceResult.ok [Atom.gnd (Ground.int (a / b))]`
      docstring: "Integer division by zero raises a DivisionByZero error (Hyperon's checked_div);
      float division follows IEEE (x/0.0 = ±inf)."
  CeTTa  same — integer result, promotes to bignum only on INT64_MIN/-1.
  MEASURED on upstream's own prebuilt `target/release/metta-repl`:  `!(/ 7 2)` → `[3]`.

⚠️ i64 WRAPAROUND IS NOT IN SCOPE AND IS NOT A BUG. hyperon is `Number{Integer(i64),Float(f64)}`
with plain Rust operators and ships `overflow-checks = false`; its own binary returns
`1864711849423024129` for `(* 99999999999 99999999999)` — byte-identical to ours. Making overflow
loud would be a DIVERGENCE. Bignum promotion (CeTTa's route) is an open owner decision recorded in
`docs/NUMERIC_SEAM_DIVERGENCES_2026-08-05.md`; it is deliberately not taken here.
"""
module NumericSeam


"""
    SeamError

A boundary decision that has no numeric answer. The lane renders it: the interpreter as an
`(Error … DivisionByZero)` atom, the MM2 sink as its own failure, the parser as a refusal to fall
through. `kind` is the reference's own name for the condition.
"""
struct SeamError
    kind::Symbol            # :division_by_zero | :integer_out_of_range
end

"""
    seam_div(a, b) -> Number | SeamError

MeTTa `/`. **Int ÷ Int is INTEGER division** (truncating), matching hyperon's
`Number::Integer(a / b)` and LeaTTa's proved `Ground.int (a / b)`. A zero integer divisor is
`DivisionByZero`, not `Inf`.

Float division is untouched IEEE — `(/ 7.0 0.0)` is `Inf`, exactly as LeaTTa's docstring states.
That half was already correct and a fix to the integer path must not over-reach; it is pinned in
`test/test_numeric_seam.jl`.
"""
function seam_div(a::Number, b::Number)
    if a isa Integer && b isa Integer
        b == 0 && return SeamError(:division_by_zero)
        return div(a, b)                 # truncating, as Rust `/` on i64
    end
    a / b                                # IEEE, including ±Inf and NaN
end

"""
    seam_mod(a, b) -> Number | SeamError

MeTTa `%`. A zero divisor is `DivisionByZero` — never a raw host exception.

Core previously let Julia's `rem(::Int, 0)` `DivideError` escape the evaluator, which breaks MeTTa's
partial semantics: a bad argument must reduce to an error or stay inert so nondeterministic
evaluation continues on other branches. `Primitives.jl:44-46` already declined rather than throwing
on the MORK lane and left a note that the resolution "needs the hyperon oracle to say what `(% 7 0)`
should produce". It does: `DivisionByZero`.
"""
function seam_mod(a::Number, b::Number)
    if a isa Integer && b isa Integer
        b == 0 && return SeamError(:division_by_zero)
        return rem(a, b)
    end
    # FLOAT `%` by zero is genuinely NaN — IEEE, exactly parallel to float `/` by zero being Inf.
    # LeaTTa's divOp errors ONLY on the Int/Int branch ("float division follows IEEE"). An earlier
    # draft of this function errored here too and broke `gcall("%", [7.0, 0.0]) == "NaN"`; the
    # grounded-registry differential caught it.
    rem(a, b)
end

"""
    seam_parse_integer(token) -> Int | SeamError | nothing

Parse an integer literal.

  `Int`      — parsed and fits
  `SeamError(:integer_out_of_range)` — it IS an integer literal but does not fit Int64. The caller
               must NOT fall through to a float parse.
  `nothing`  — not an integer literal at all (e.g. `"3.5"`, `"foo"`); falling through is correct.

The middle case is the fix. `Parser.jl` did `tryparse(Int, token)` and on failure fell through to
`tryparse(Float64, token)`, so `9223372036854775808` silently became `9.223372036854776e18` with its
precision gone. hyperon registers the integer literal as a FALLIBLE token precisely so this can fail
(`arithmetics.rs:163-164`), erroring "Could not parse integer: … number too large to fit in target
type". Independent of the bignum decision: reinterpreting an integer as a float is wrong whether we
wrap or promote.
"""
function seam_parse_integer(token::AbstractString)
    v = tryparse(Int, token)
    v === nothing || return v
    # Looks like an integer (optional sign, all digits) but did not fit.
    s = strip(token)
    isempty(s) && return nothing
    body = (s[1] == '-' || s[1] == '+') ? s[2:end] : s
    (!isempty(body) && all(isdigit, body)) && return SeamError(:integer_out_of_range)
    nothing
end

# ── the other two §3.4 ambiguities — named so they land HERE, not in a fourth file ──────────────
#
# EVALUATION ORDER (open; merge-design R1). Core `(=)` is demand-driven INNERMOST reduction; MM2
#   exec is forward-firing and order-agnostic, so saturation over-derives relative to the
#   interpreter. Reproducing innermost order needs driver-style residualization or a priority/guard
#   encoding. When that is decided, the decision belongs here — not in DualTrack's lane dispatch.
#
# SPACE SELECTION (partly closed). `&self` resolves to the OLD interpreter Vector{Atom} store;
#   `load_core_lib!` writes the MORK trie. An empty result from the wrong store is byte-identical to
#   a missing atom, which is how 30 present constants read as absent. `LibPolicy` fixed the policy
#   read (`core_rules` on the CoreSpace); the general rule — which store a given form addresses —
#   is still implicit and belongs here.

export SeamError, seam_div, seam_mod, seam_parse_integer

end # module NumericSeam
