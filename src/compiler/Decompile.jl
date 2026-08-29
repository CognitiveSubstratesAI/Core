# Decompile.jl — MeTTa-IL → surface MeTTa. The inverse of `EmitIL.jl`.
#
# ── WHY THIS EXISTS, AND WHAT IT IS *NOT* FOR ────────────────────────────────────────────────────
# It was first proposed as a HOMOICONICITY fix — "compiled rules stop being MeTTa data, so `match`
# cannot see them". MEASURED 2026-08-29, that premise is mostly FALSE and the measurement is kept
# here so the next session starts past it:
#
#     stored form of a compiled clause    (= (f $x) (function (return (g $x))))   head INTACT
#     !(match &self (= (f $x) $b) $b)     [(g $x)]        ← identical to the SOURCE form's answer
#     !(match &self (= (f $x) (g $y)) M)  []              ← the ONLY thing that breaks
#
# The head is never lost, and `(function (return X))` evaluates transparently to `X`, so every
# consumer that EVALUATES a matched body already gets the source answer. Only a consumer that matches
# the body STRUCTURALLY sees the wrapper. That is a real gap, but a narrow one, and it is not the
# reason to build this.
#
# THE REASON TO BUILD IT IS AS A COMPILER ORACLE: `decompile ∘ compile ≡ id` is a property test over
# the whole corpus, and it observes a defect class no answer-comparison can — a lowering that changes
# the MEANING of a clause while still producing the right answer on the corpus's inputs. `EmitIL.jl`
# has three such defects recorded in its own comments (the `eval`/`metta` confusion "survived a
# coverage ratchet, a corpus differential AND a fuzz differential"), each found by something other
# than the corpus. A structural inverse is that something.
#
# ── THE DISCIPLINE: DECLINE, NEVER GUESS ─────────────────────────────────────────────────────────
# A partial decompiler that returns a BARE TERM launders its own incompleteness — the caller cannot
# tell a faithful inverse from a plausible reconstruction. So every function here returns a
# `DecompileResult` carrying either an atom or a REASON, and an unrecognised form is a decline with
# the form named. This mirrors `Emit.jl`'s `decline_reason`, deliberately: the two stages should fail
# the same way.
#
# ⚠️ `unify` WAS DECLINED AS "AMBIGUOUS" AND THAT WAS THE WRONG ANSWER TO A REAL AMBIGUITY.
# `EmitIL` lowers THREE surface forms into it — `let` (`_instr(::GUnify)`), `if` (`_instr(::GBranch)`,
# against the literal `True`), and `case` (the same True/False chain). MEASURED: `(if C A B)` and
# `(case C ((True A) (False B)))` compile to BYTE-IDENTICAL IL, so the distinction really is destroyed
# and no decompiler can recover it. But SWI-Prolog faces the same thing and does NOT decline:
# `pl-comp.c:6895` makes an un-decompilable instruction a `sysError` — TOTALITY is required — and its
# tests assert a HAND-WRITTEN expected form, not the source (`decomp8`: `s7(X) :- X = f(A), q(A)`
# comes back as `s7(f(A)) :- q(A)`). `clause/2` returns the clause AS COMPILED.
#
# So this file does the same: it returns the CANONICAL form. `case` over booleans comes back as `if`;
# `let*` as nested `let`. Soundness is checked by a FIXPOINT rather than an allowlist —
# `compile(decompile(compile(P))) == compile(P)` — which is what `tools/decompile_roundtrip.jl`
# classifies on. Coverage over the corpus is 208 EXACT + 3 CANONICAL + 0 MISMATCH + 0 DECLINED = 211.
#
# WHAT WOULD STILL DECLINE: a producer this file has no case for (`collapse-bind`/GFindall), and a
# `unify` whose fail arm is not `(return Empty)`. Those are shapes never yet emitted, not guesses.
#
# NO `Any` — standing project rule, tests included.

module CompilerDecompile

using ..StandardMeTTa: Atom, Sym, Var, Expression

export DecompileResult, decompile_clause, decompile_body, declined

"""
    DecompileResult

`atom === nothing` ⇔ DECLINED, and `reason` then names the form that could not be inverted. A
successful result carries an empty reason. Never both.
"""
struct DecompileResult
    atom::Union{Atom, Nothing}
    reason::String
end

"True when this result is a decline. Reads better than `r.atom === nothing` at call sites."
declined(r::DecompileResult)::Bool = r.atom === nothing

_ok(a::Atom)::DecompileResult = DecompileResult(a, "")
_no(why::AbstractString)::DecompileResult = DecompileResult(nothing, String(why))

"""Is `a` the symbol `s`?

MEASURED 2026-08-29 against `Eval.TOKEN_REGISTRY`: every keyword this file dispatches on — `=`,
`function`, `return`, `chain`, `metta`, `eval`, `unify`, `collapse-bind`, `Empty`, `%Undefined%`,
`&self` — is UNREGISTERED, so it stays a `Sym` through `parse_program`. That matters because the
compile lane serializes IL to TEXT and re-parses it (`test_il_roundtrip.jl`), so a decompiler that
only worked on freshly-emitted atoms would quietly stop matching on the way back in. It does not.
"""
_is(a::Atom, s::String)::Bool = a isa Sym && (a::Sym).name === Symbol(s)

"""Is `a` the symbol `s` OR a grounded op of that name?

⚠️ NEEDED EXACTLY WHERE `_is` IS NOT, and the difference is not cosmetic. `foldl-atom` and
`superpose` ARE in `TOKEN_REGISTRY`, so `EmitIL` builds `Sym("foldl-atom")` while the parser turns
the same text into `Grounded{SpaceOp}`. A `Sym`-only guard therefore fires on emitted IL and SILENTLY
NOT on re-parsed IL — which is the half that reaches a consumer. Found by this file's own test on
first run; the guard it protects (GFindall's collapse fold) is precisely one that must never miss.
A grounded op renders as its name, so the string form covers both."""
_named(a::Atom, s::String)::Bool = a isa Sym ? (a::Sym).name === Symbol(s) : string(a) == s

# ── A-normal INLINING ────────────────────────────────────────────────────────────────────────────
# `ANormal` names every intermediate (`$__t1`) and `EmitIL` binds it with `chain`. Going back to
# surface means UNDOING that naming: substitute the producer into the continuation. The environment is
# therefore var-name → producing atom, and it is threaded, not global — a `chain` binder scopes over
# its continuation only.
#
# `Var.name` is a `String` while `Sym.name` is a `Symbol` (a real asymmetry in `Atoms.jl`; keyed
# wrongly this silently never substitutes and every clause decompiles to a term full of `$__t1`).
const Env = Dict{String, Atom}

function _subst(a::Atom, env::Env)::Atom
    if a isa Var
        v = get(env, (a::Var).name, nothing)
        return v === nothing ? a : v
    elseif a isa Expression
        return Expression(Atom[_subst(c, env) for c in (a::Expression).children])
    end
    a
end

"Is `a` exactly `(return Empty)` — `_RET_EMPTY`, the fail arm every `unify` lowering uses?"
function _is_ret_empty(a::Atom)::Bool
    a isa Expression || return false
    c = (a::Expression).children
    length(c) == 2 && _is(c[1], "return") && _is(c[2], "Empty")
end

"""`(unify CV True THEN ELSE)` → `(if CV then else)`, or `nothing` if this is not that shape.

`nothing` (not a decline) means "not a GBranch", so the caller reports accurately instead of blaming
a shape it never saw. The else arm is itself
`(chain (function (unify CV False E (return Empty))) \$o (return \$o))` — the SAME condition variable
against `False` — which is what makes the two arms recognisable as ONE `if` rather than two `unify`s.
"""
function _decompile_if(u::Atom, env::Env)::Union{DecompileResult, Nothing}
    u isa Expression || return nothing
    uc = (u::Expression).children
    (length(uc) == 5 && _is(uc[1], "unify") && _is(uc[3], "True")) || return nothing
    t = decompile_body(uc[4], env)
    declined(t) && return t
    els = uc[5]
    ev = if _is_ret_empty(els)
        _ok(Sym("Empty"))
    else
        els isa Expression || return nothing
        ec = (els::Expression).children
        (length(ec) == 4 && _is(ec[1], "chain")) || return nothing
        f = ec[2]
        f isa Expression || return nothing
        fc = (f::Expression).children
        (length(fc) == 2 && _is(fc[1], "function")) || return nothing
        iu = fc[2]
        iu isa Expression || return nothing
        ic = (iu::Expression).children
        (length(ic) == 5 && _is(ic[1], "unify") && _is(ic[3], "False")) || return nothing
        decompile_body(ic[4], env)
    end
    declined(ev) && return ev
    _ok(Expression(Atom[Sym("if"), _subst(uc[2], env), t.atom::Atom, ev.atom::Atom]))
end

"""
    decompile_body(a, env) -> DecompileResult

MeTTa-IL body → surface term. Handles the two forms whose inverse is UNAMBIGUOUS:

  * `(return X)`                                  → `X`
  * `(chain (metta E %Undefined% &self) \$t C)`    → `C` with `\$t := E`

Everything else declines by name. The `%Undefined%`/`&self` arguments are matched exactly rather than
ignored: `EmitIL._instr(::GCall)` documents both as load-bearing (the no-expectation meta-type and
the context space), so a `chain` over a `metta` with different arguments is NOT this lowering and must
not be inverted as if it were.
"""
function decompile_body(a::Atom, env::Env=Env())::DecompileResult
    a isa Expression || return _ok(_subst(a, env))
    ch = (a::Expression).children
    n = length(ch)

    # (return X) — the clause tail. `_seq`'s `tail` argument.
    if n == 2 && _is(ch[1], "return")
        return _ok(_subst(ch[2], env))
    end

    # (chain <producer> $t <cont>) — only a `metta` producer is invertible here.
    if n == 4 && _is(ch[1], "chain")
        p = ch[2]
        if p isa Expression
            pc = (p::Expression).children
            if length(pc) == 4 && _is(pc[1], "metta") && _is(pc[3], "%Undefined%") && _is(pc[4], "&self")
                v = ch[3]
                v isa Var || return _no("chain binder is not a variable: " * string(ch[3]))
                env2 = copy(env)
                env2[(v::Var).name] = _subst(pc[2], env)
                return decompile_body(ch[4], env2)
            end
            # `(chain (function (unify …)) …)` is `_instr(::GBranch)` — an `if`. Named, not guessed.
            if length(pc) == 2 && _is(pc[1], "function")
                r = _decompile_if(pc[2], env)
                r === nothing && return _no("chain over `(function …)` that is not a GBranch `if`")
                rr = r::DecompileResult
                declined(rr) && return rr
                v = ch[3]
                v isa Var || return _no("chain binder is not a variable: " * string(ch[3]))
                env2 = copy(env)
                env2[(v::Var).name] = rr.atom::Atom
                return decompile_body(ch[4], env2)
            end
            # `(chain (eval X) $t C)` — `_instr(::GResidual)` lowers X VERBATIM (`nd = _il_atom(n)`),
            # so the inverse is exact: X is the source term, unchanged. This is the same substitution
            # as the `metta` case, differing only in the producer.
            #
            # ⚠️ `eval` HAS A SECOND EMITTER. `_instr(::GFindall)` (EmitIL.jl:555) builds
            # `(chain (eval (foldl-atom …_collapse-add-next-atom-from-collapse-bind-result…)) $o C)`
            # as the INNER chain of `(chain (collapse-bind …) …)`. Today that outer `collapse-bind`
            # declines before this line is reached — but if it is ever inverted, an unguarded rule
            # here would silently return the FOLD in place of the source `collapse`. Refused by shape
            # rather than left to that ordering.
            if length(pc) == 2 && _is(pc[1], "eval")
                inner = pc[2]
                if inner isa Expression
                    ic = (inner::Expression).children
                    !isempty(ic) && _named(ic[1], "foldl-atom") &&
                        return _no("`(eval (foldl-atom …))` — GFindall's collapse fold, not a residual")
                end
                v = ch[3]
                v isa Var || return _no("chain binder is not a variable: " * string(ch[3]))
                env2 = copy(env)
                env2[(v::Var).name] = _subst(inner, env)
                return decompile_body(ch[4], env2)
            end
            return _no("chain over an uninvertible producer: " * string(pc[1]))
        end
        return _no("chain over a non-expression producer")
    end

    # `unify` — THREE surface forms lower here. See the header; declined deliberately.
    if n == 5 && _is(ch[1], "unify")
        _is_ret_empty(ch[5]) || return _no("`unify` with a non-`(return Empty)` fail arm")
        lhs, rhs, thn = ch[2], ch[3], ch[4]
        # THE ASSIGNMENT IDIOM, not a `let`: `(unify $o V (return $o) (return Empty))` is how a join
        # point binds its value (`_instr(::GBranch)` closes each arm into one). Distinguished by the
        # then-arm being EXACTLY `(return lhs)`; a `let` does further work with the binding.
        if thn isa Expression
            tc = (thn::Expression).children
            if length(tc) == 2 && _is(tc[1], "return") && lhs isa Var && tc[2] isa Var &&
               (tc[2]::Var).name == (lhs::Var).name
                return _ok(_subst(rhs, env))
            end
        end
        b = decompile_body(thn, env)
        declined(b) && return b
        return _ok(Expression(Atom[Sym("let"), _subst(lhs, env), _subst(rhs, env), b.atom::Atom]))
    end

    _no("unrecognised IL form: " * string(a))
end

"""
    decompile_clause(a) -> DecompileResult

A whole emitted clause `(= <head> (function <body>))` → `(= <head> <surface-body>)`.

The HEAD is passed through untouched — `_emit_with_head` never rewrites it, which is precisely why
`match` on a compiled rule's head works at all. Only the body was lowered, so only the body is
inverted.

A clause whose body is not `(function …)` is declined rather than returned unchanged: that shape is
a SOURCE rule, and silently echoing it would make the round-trip oracle pass on inputs it never
actually inverted.
"""
function decompile_clause(a::Atom)::DecompileResult
    a isa Expression || return _no("not an expression")
    ch = (a::Expression).children
    (length(ch) == 3 && _is(ch[1], "=")) || return _no("not a `(= head body)` clause")
    fb = ch[3]
    fb isa Expression || return _no("body is not `(function …)` — not a compiled clause")
    fc = (fb::Expression).children
    (length(fc) == 2 && _is(fc[1], "function")) ||
        return _no("body is not `(function …)` — not a compiled clause")
    r = decompile_body(fc[2], Env())
    declined(r) && return r
    _ok(Expression(Atom[Sym("="), ch[2], r.atom::Atom]))
end

end # module CompilerDecompile
