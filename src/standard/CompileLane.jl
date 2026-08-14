# CompileLane.jl — COMPILER-PRIMARY execution: MeTTa → MeTTa-IL → evaluate the IL.
#
# ─── WHY THIS FILE EXISTS ────────────────────────────────────────────────────────────────────────
# `EmitIL.jl` gave the compiler the arrow Figure 2 has (MeTTa → MeTTa-IL) and lowers 687 of the
# 1000-clause corpus. It had NO PRODUCTION CONSUMER — only tests. That is exactly the failure
# recorded on 2026-08-07, when ~1962 LOC of emitter ended up unused because it targeted a stage with
# no incoming arrow; here the incoming arrow was right and the OUTGOING one was missing. An emitter
# nothing calls is measured coverage of nothing.
#
# This is that consumer, and it implements the standing directive literally — stated 4×:
# **THE COMPILER IS PRIMARY; THE INTERPRETER IS A FALLBACK ONLY.** Every definition is compiled to
# minimal MeTTa; only the ones the compiler DECLINES fall back to their source form. The interpreter
# is not a parallel lane here — it is the IL's evaluator, which is precisely what it is, because
# `Eval.jl` implements all nine `MINIMAL_OPS`.
#
# ─── THE ONE CORRECTNESS CONSTRAINT ──────────────────────────────────────────────────────────────
# A definition contributes EITHER its IL form OR its source form — NEVER both. MeTTa dispatch is
# `query($space, (= $atom $X))` (Invariant 6) and every match yields a result, so loading both would
# not "prefer the compiled one": it would double every answer. This is the whole reason compilation
# is decided per-definition rather than per-program.
#
# ─── INVARIANT 1 IS INHERITED, NOT REIMPLEMENTED ─────────────────────────────────────────────────
# Definitions and queries interleave, and a query must see only the rules that TEXTUALLY PRECEDE it.
# That is `split_program_regions` (`SexprForms.jl`, 2026-08-08), which this lane drives directly —
# the same partition `mc_run` uses. Compiling per region rather than per program is what keeps the
# compiled lane from reproducing the flattening defect the partition was built to fix.
#
# Design + diagrams: `docs/architecture/COMPILER_IL_STAGE.md`.

# ── the may-mutate predicate, LANE-NEUTRAL and shared ────────────────────────────────────────────
# Lifted here from `DualTrack.jl` so the surviving lane owns it and the deprecated one consumes it,
# rather than two copies of a fail-safe predicate drifting apart. It REUSES `Eval._pure_heads`, a
# WHITELIST fixpoint (`Eval.jl:1040` — an op that is neither a pure primitive nor a defined head is
# classified impure, so an unknown name fails SAFE). A denylist of mutator names fails OPEN, which is
# how JeTTa's memo gate went unsound: 6 dead entries, both space mutators misspelled.
#
# Skipped unless the program has two ADJACENT bangs — the only shape where a mutating query can reach
# a later query with no definition between them. MEASURED cost when it does run: ~1.3 ms of an 8.9 ms
# call (~14%, noisy). Not free; bought for soundness.
function purity_may_mutate(program::AbstractString)
    forms = mm2_split_forms(program)
    any(i -> forms[i][1] && forms[i + 1][1], 1:length(forms) - 1) || return (_::AbstractString) -> false
    sp = Eval.Space(); Eval.load_core_stdlib!(sp)
    for (bang, f) in forms
        bang || Eval.load_metta!(sp, f)
    end
    pure = Eval._pure_heads(Eval._rules_of(Eval.all_atoms(sp)))
    (f::AbstractString) -> !(Base.Symbol(mm2_head(f)) in pure)
end

"""
    _resolve_tokens(a, sp) -> Atom

Apply the SPACE-DEPENDENT half of `parse_atom` (`Eval.jl:2602-2610`) to an emitted atom.

The emitter is space-blind, so it cannot do the two lookups the parser does on every bare word:

    haskey(sp.tokens, tok)       -->  tokens[tok]         `bind!` tokens — e.g. `&kb`
    haskey(TOKEN_REGISTRY, tok)  -->  TOKEN_REGISTRY[tok]  grounded operators

🔴 THIS IS WHY THE FIRST TWO ATTEMPTS AT THE SWITCH FAILED, and the second failure is the informative
one. `f24d636` made the LEAF builders parse-equivalent (`IRGrounded` -> `Grounded(value)`,
`IRPredefined` -> registry) and the same five scripts broke by the same margins — because
parse-equivalence is NOT A PROPERTY OF AN ATOM ALONE. It is relative to a SPACE. `_name_spaces` turns
`&kb` back into a symbol so the wire text has a word to print; the text path then re-resolves that word
through `sp.tokens`, and the atom path had no way to.

So the resolution runs HERE, in the one component that holds the space, mirroring `parse_atom`'s order
exactly — deliberately including symbols that collide with operator names, because parsing the text
would resolve those too, and the text path is the baseline this must not deviate from."""
function _resolve_tokens(a::StandardMeTTa.Atom, sp)::StandardMeTTa.Atom
    if a isa StandardMeTTa.Expression
        ch = (a::StandardMeTTa.Expression).children
        return StandardMeTTa.Expression(StandardMeTTa.Atom[_resolve_tokens(c, sp) for c in ch])
    elseif a isa StandardMeTTa.Sym
        n = String((a::StandardMeTTa.Sym).name)
        haskey(sp.tokens, n) && return sp.tokens[n]
        haskey(Eval.TOKEN_REGISTRY, n) && return Eval.TOKEN_REGISTRY[n]
    end
    a
end

const ILForm = @NamedTuple{atoms::Vector{StandardMeTTa.Atom}, clauses::Vector{String},
                           wire::Union{Nothing, String}}

"""
    compile_definition(sp, form) -> Union{ILForm, Nothing}

Compile ONE top-level form to minimal-MeTTa IL — returned as BOTH the atoms the lane loads and
the clause text that goes on the wire — or `nothing` if it is not a compilable
definition (a bare fact, an unparseable form) or the compiler declines it.

Deliberately per-form: see the correctness constraint above. A form that yields no `(=)` definition —
a ground fact like `(edge a b)` — is NOT a compiler failure and must not be counted as a decline; it
is simply data, and it returns `nothing` so the caller loads it verbatim.
"""

function compile_definition(sp, form::AbstractString)::Union{ILForm, Nothing}
    atoms = try
        toks = Eval.tokenize(form); i = Ref(1)
        out = StandardMeTTa.Atom[]
        while i[] <= length(toks)
            toks[i[]] == "!" && (i[] += 1)
            i[] > length(toks) && break
            push!(out, Eval.parse_from(toks, i, sp.tokens))
        end
        out
    catch
        return nothing
    end
    # RESTORE THE NAME FIRST, then check. A named space is round-trippable once it carries its word
    # again, so this must run BEFORE the guard or the guard declines clauses that are now fine.
    atoms = _name_spaces(atoms, sp)
    # A value that cannot survive the IL TEXT round-trip makes the emitted clause quietly mean
    # something else — see `_unroundtrippable`. Checked on the PARSED atoms, before any lowering,
    # because the corruption is in serialization and every later stage inherits it.
    # 🔴 NOT A DECLINE ANY MORE — SPLIT 2026-08-12. This guard was written when the lane round-tripped
    # through TEXT: a definition whose clause text could not be re-parsed faithfully had to be refused,
    # or the lane would load a corrupted atom. Since `2105f9d` the lane loads the emitter's ATOMS
    # directly and takes no such hop, so refusing here costs coverage for a reason that no longer
    # applies. The check still matters for the OTHER consumer — `clauses` is the wire form, and Fig-2
    # makes it the distributed artifact — so its verdict is now REPORTED on the ILForm instead of
    # silently dropping the definition.
    wire_verdict = _unroundtrippable(atoms, sp)
    prog = try CompilerFrontend.lower_program(atoms) catch; return nothing end
    isempty(prog.definitions) && return nothing        # a fact, not a definition — not a decline
    cls = try CompilerANormal.translate_program(prog) catch; return nothing end
    isempty(cls) && return nothing
    r = try CompilerEmitIL.emit_il_program(cls) catch; return nothing end
    # ALL-OR-NOTHING per form. A form can lower to several clauses; if any is declined, loading the
    # compiled subset plus the whole source form would double the surviving answers (Invariant 6).
    (r.emitted == length(cls) && isempty(r.declined)) || return nothing
    # 🟢 RETURNS BOTH VIEWS, and the lane now takes the ATOMS. Consuming them was tried on 2026-08-11
    # and REVERTED: it broke five corpus scripts (b2_backchain +5 errors, c3_pln_stv +5,
    # c1_grounded_basic +4, d2_higherfunc +3, e1_kb_write +2), because `EmitIL`'s builders were then
    # TEXT-EQUIVALENT — `&self` was `Sym("&self")` and a literal was `Sym("\"abc\"")`, proven against
    # `render`. The text path PARSED that back into a `Grounded{Space}` and a grounded string; skipping
    # the parse added the Syms literally.
    #
    # ⚠️ THE LESSON IS ABOUT THE PROPERTY, NOT THE PATCH. `test_emit_il.jl` proved atom ⇒ TEXT
    # (`il_text(_il_atom(a)) == _render_il(a)`). What bypassing the parser needs is atom ⇒ ATOM. Both
    # are called "equivalence"; only the second licenses the switch, and the first passed throughout.
    #
    # `f24d636` made the builders PARSE-EQUIVALENT (`IRGrounded` → `Grounded(value)`, `IRPredefined` →
    # `TOKEN_REGISTRY`), so the atoms are now what parsing produces — and for a Space, `parse("&self")
    # === sp`, so it is the SAME OBJECT rather than an equal one. `clauses` stays available and is
    # still the artifact that gets written out; nothing downstream of the wire changes.
    (atoms = r.atoms, clauses = r.clauses, wire = wire_verdict)
end

"""
    compile_mm2(sp, form) -> Union{@NamedTuple{rules::Vector{String}, emitted::Int}, Nothing}

Compile ONE definition to **MM2 exec atoms** — `compile_definition`'s sibling for the `:mork` backend.

Identical front half (parse -> `_name_spaces` -> `lower_program` -> `translate_program`); the only
difference is the emitter: `CompilerEmit.emit_program` instead of `CompilerEmitIL.emit_il_program`.
That pairing is the design, not a fork: per `docs/architecture/COMPILER_IL_STAGE.md` the two are
SIBLING emitters over the same A-normal clauses, and `test_emit_il.jl` runs both on the same `cls`
asserting `il.emitted >= mm2.emitted`.

ALL-OR-NOTHING per form, for the same Invariant-6 reason `compile_definition` is: loading a compiled
subset alongside the source form would DOUBLE the surviving answers.

⚠️ `Emit.jl` emits only all-`GCall`/`GUnify` clauses (2 of 6 goal types; `EmitIL` covers 5), so this
declines strictly more often than `compile_definition`. Measured scope, not a defect.
"""
function compile_mm2(sp, form::AbstractString)
    atoms = try
        toks = Eval.tokenize(form); i = Ref(1)
        out = StandardMeTTa.Atom[]
        while i[] <= length(toks)
            toks[i[]] == "!" && (i[] += 1)
            i[] > length(toks) && break
            push!(out, Eval.parse_from(toks, i, sp.tokens))
        end
        out
    catch
        return nothing
    end
    atoms = _name_spaces(atoms, sp)
    prog = try CompilerFrontend.lower_program(atoms) catch; return nothing end
    isempty(prog.definitions) && return nothing        # a fact, not a definition — not a decline
    cls = try CompilerANormal.translate_program(prog) catch; return nothing end
    isempty(cls) && return nothing
    r = try CompilerEmit.emit_program(cls) catch; return nothing end
    (r.emitted == length(cls) && isempty(r.declined)) || return nothing
    (rules = String[String(x) for x in r.rules], emitted = r.emitted)
end

"""
    compile_run(program; fallback=true) -> (; answers, compiled, fell_back, space)

Run `program` COMPILER-FIRST: each definition is lowered to minimal MeTTa and loaded as IL; declined
definitions load as source. Queries are answered against the accumulated space, region by region, so
Invariant 1 holds.

`answers` is `Vector{Tuple{String,Vector{String}}}` — (query, results) in program order.
`fallback=false` makes declines an ERROR instead of loading source: use it in tests to prove the
compiled path alone produced an answer, since a fallback that silently rescues the result is how a
compiler comes to look complete.
"""
function compile_run(program::AbstractString; fallback::Bool = true,
                     max_steps::Int = 512_000, backend::Symbol = :eval)
    # ── METER IT (the cost account) ──────────────────────────────────────────────────────────────
    # `gslt_mettail_summary_spec.md` §8, the C monad: "Every interaction is gated on consuming a
    # token… the token stack drains in step with the reductions actually performed." A GSLT gives
    # causality; C gives BOUNDED causality.
    #
    # MEASURED 2026-08-09, and this is why the bound is here rather than in a backlog: emitted IL
    # with a mis-lowered branch ran 21 MINUTES at 98% CPU inside `Eval.subst` and had to be killed
    # blind, with no output identifying even which script was looping. Core already had the
    # apparatus — `interpret_max_steps!` (Eval.jl:1652) — but it defaults to 0 = UNLIMITED and this
    # lane used neither it nor `metta_max_steps!`. Compiling a program is exactly when a fuel bound
    # is cheap and a runaway is expensive: the compiler can emit a non-terminating term from a
    # terminating source, which is what happened.
    #
    # `_INTERPRET_MAX` is PROCESS-GLOBAL, so it is snapshot/restored — the same discipline
    # `_mc_fallback_eval` uses for `_TABLED_HEADS`. Exhaustion is SURFACED in `exhausted`, not
    # swallowed: turning a budget overrun into a silent empty answer would be the drop this pipeline
    # is built to avoid. (Upstream flags budget-exhaustion SEMANTICS — false/block/fault — as an
    # open question; recording the overrun and continuing is the choice made here.)
    prev_max = Eval._INTERPRET_MAX[]
    Eval.interpret_max_steps!(max_steps)
    try
        _compile_run_inner(program, fallback, backend)
    finally
        Eval._INTERPRET_MAX[] = prev_max
    end
end

"""Rewrite each `Grounded{Space}` back to the TOKEN that named it — the wire format carries the name.

🔴 THE NAME IS LOST AT PARSE TIME, NOT AT RENDER TIME, and that is why the fix belongs here.
`parse_from` resolves `&kb` through `sp.tokens` into a `Grounded{Space}` (`Eval.jl:2525`), and from
that point the token is gone — a Space knows its contents, never what it was called. `render` then
has nothing to print but `Base.show`, which prints EVERY space as `&self` (`Eval.jl:549`).

The grammar decides the shape of the fix. `metta_language_spec.md:36` gives `GROUNDED ::= STRING |
WORD`: a grounded atom's textual form is a WORD. A named space HAS a word — `&kb` — and it re-parses
correctly, because the clause is loaded back into the same space whose token table defined it.
MEASURED: `!(bind! &kb (new-space))` then `!(add-atom &kb …)` then `!(match &kb …)` round-trips at
top level today; only the DEFINITION path lost it, because only that path goes through `render`.

So this restores the word before lowering, and everything downstream is unchanged: the `Sym` renders
as `&kb`, re-parsing turns it back into the same `Grounded{Space}`, and the emitted clause means what
its source meant. A PRE-PASS rather than a render-time lookup because `render` has no access to a
space's token table and threading one through every emitter signature would be a large change to
carry a name that the parser already knew.

⚠️ AN ANONYMOUS SPACE IS STILL UNNAMEABLE — `(new-space)` used inline, never bound to a token, has no
word to emit. Those still fall to `_unroundtrippable` and are declined, which is correct: a value with
no textual form cannot be in a DISTRIBUTED artifact, and the IL is the distributed artifact."""
function _name_spaces(atoms::Vector{StandardMeTTa.Atom}, sp)::Vector{StandardMeTTa.Atom}
    # token → space, reversed once per form.
    #
    # ⚠️ `sp` ITSELF IS EXCLUDED, for two reasons, and the first version of this did neither.
    #   CORRECTNESS: `&self` is ALWAYS bound (`Eval.jl:2579`), and rewriting it to `Sym("&self")`
    #   changes what every LATER stage sees — `Frontend.lower` tests `h isa Grounded{Eval.SpaceOp}`
    #   and `EmitIL._lowerable_match` inspects head kinds. Turning the common case from a Grounded
    #   into a Sym silently re-decides those guards. `&self` also needs no help: it round-trips by
    #   construction.
    #   COST: because `&self` is always present, `names` was never empty, so EVERY form deep-copied
    #   its whole atom tree. MEASURED — `test_compile_lane_fuzz.jl` (40 generated programs through
    #   `compile_run`) went to 288 s wall and pushed the suite past its 10-minute budget.
    # With `sp` excluded, a program that names no other space hits the early return below and pays
    # nothing at all, which is almost every program.
    names = IdDict{Eval.Space, String}()      # NO `Any` — standing rule, code and tests alike
    for (tok, a) in sp.tokens
        a isa StandardMeTTa.Grounded || continue
        v = (a::StandardMeTTa.Grounded).value
        (v isa Eval.Space && v !== sp) || continue
        get!(names, v, tok)                      # first token wins; deterministic per table order
    end
    isempty(names) && return atoms

    rewrite(a::StandardMeTTa.Atom)::StandardMeTTa.Atom = begin
        if a isa StandardMeTTa.Expression
            StandardMeTTa.Expression(StandardMeTTa.Atom[rewrite(c)
                                                        for c in (a::StandardMeTTa.Expression).children])
        elseif a isa StandardMeTTa.Grounded && (a::StandardMeTTa.Grounded).value isa Eval.Space
            nm = get(names, (a::StandardMeTTa.Grounded).value, nothing)
            nm === nothing ? a : StandardMeTTa.Sym(nm)
        else
            a
        end
    end
    StandardMeTTa.Atom[rewrite(a) for a in atoms]
end

"""The Grounded values that DO NOT SURVIVE the IL text round-trip, and why each one dies.

🔴 THE COMPILE LANE ROUND-TRIPS IL THROUGH TEXT. `compile_definition` returns `Vector{String}`, and
`_compile_run_inner` re-loads each with `Eval.load_metta!`. So a clause is only faithful if every
value in it satisfies `parse(show(v)) ≡ v`. Several do not, and their `show` methods are correct as
DISPLAY — the defect is that display became a serialization format.

MEASURED 2026-08-11, by execution, over every `Grounded`-carried type:

  `Space`     `Eval.jl:549` prints EVERY space as `&self`, whatever its identity. On re-parse,
              `&self` resolves through `space.tokens["&self"]` (`Eval.jl:2579`) to the space being
              compiled INTO. So a definition that writes to a named space silently redirects.
              WITNESSED — four lines, and the compiler produced it (`compiled=1 fell_back=0`):
                  !(bind! &kb (new-space))
                  (= (put \$x) (add-atom &kb (Green \$x)))
                  !(put Fritz)
                  !(match &kb (Green \$y) \$y)
              interpreter `Fritz`, compiled lane NOTHING. This is `e1_kb_write.metta`'s 2 divergent
              queries; its error text reads `(add-atom &self …)` for source that says `&kb`.

  `StateCell` prints as `(State (A B))` and re-parses as a plain `Expression` — TYPE LOST, measured.
              Worse than `Space` in kind: a state cell is MUTABLE IDENTITY, so no textual form could
              be faithful. Nothing to fix in its `show`; such a clause must not be compiled.

  `Bindings`  has NO `show` method at all, so it falls to `Grounded`'s `print(io, a.value)` and out
              comes Julia struct syntax, which is not MeTTa and does not re-parse.

  `WFSBottom` prints `undefined`, which re-parses as the SYMBOL `undefined`.

⚠️ `&self` ITSELF IS FINE AND MUST STAY COMPILABLE. It round-trips by construction: the text `&self`
re-parses to the space being loaded into, which is exactly what the source meant. That is why this
guard takes `sp` and compares IDENTITY rather than rejecting `Grounded{Space}` wholesale — rejecting
the type would give back working coverage to close a bug that only non-`&self` spaces have.

This DECLINES rather than repairs. A declined definition falls back to the interpreter and answers
correctly, so the guard is sound in the direction that matters. The real fix is to stop serializing
IL through text — emit `Atom`s and load them directly — and that is a larger change than this file.
Recorded so the decline is a known position rather than a mystery."""
function _unroundtrippable(atoms::Vector{StandardMeTTa.Atom}, sp)::Union{Nothing, String}
    why = nothing
    walk(a::StandardMeTTa.Atom) = begin
        why === nothing || return nothing
        if a isa StandardMeTTa.Expression
            for c in (a::StandardMeTTa.Expression).children; walk(c); end
        elseif a isa StandardMeTTa.Grounded
            v = (a::StandardMeTTa.Grounded).value
            if v isa Eval.Space
                v === sp || (why = "a named space other than &self (prints as `&self`, re-parses to &self)")
            elseif v isa Eval.StateCell
                why = "a state cell (prints as `(State …)`, re-parses as an Expression — type lost)"
            elseif v isa Eval.WFSBottom
                why = "WFSBottom (prints as `undefined`, re-parses as the symbol `undefined`)"
            elseif v isa Bool
                # ADDED 2026-08-12. `il_text` writes `true`/`false` and `Eval.parse_atom` has no boolean
                # case, so a grounded Bool comes back a SYMBOL. MeTTa's own convention is that booleans
                # are the symbols True/False, which round-trip fine — a Grounded{Bool} can only have
                # arrived from a grounded op returning a Julia Bool. This slot previously listed `Bool`
                # among the ALLOWED types, which was wrong for the wire; found by the randomized
                # property in `test/compiler/test_il_wire_roundtrip.jl`. Now that the verdict annotates
                # rather than declines, saying so costs no coverage.
                why = "a grounded Bool (prints as `true`/`false`, re-parses as a symbol — MeTTa booleans are the symbols True/False)"
            elseif !(v isa Eval.Operation || v isa Eval.SpaceOp ||
                     v isa Number || v isa AbstractString)
                why = "a grounded $(typeof(v)) with no faithful textual form"
            end
        end
        nothing
    end
    for a in atoms; walk(a); end
    why
end

"""Whether the program INSPECTS ITS OWN RULES — in which case nothing may be compiled.

🔴 COMPILING A DEFINITION CHANGES WHAT `&self` CONTAINS, and a program that looks at `&self` can see
that. MEASURED 2026-08-10 on the conformance corpus, `b3_direct.metta`:

    source    (= (croaks Fritz) T)
    compiled  (= (croaks Fritz) (function (return T)))
    directive !(assertEqualToResult (match &self (= (\$p Fritz) T) \$p) (croaks eat_flies))

The directive asks the space for rules whose right-hand side is `T`. Against source rules it finds
`croaks` and `eat_flies`; against emitted IL it finds NOTHING, because the right-hand side is now
`(function (return T))`. The compiled lane answered `AssertionFailed` where the interpreter answered
`()` — a WRONG ANSWER, from a lane that had compiled all six definitions and fallen back on none.

⚠️ `EmitIL._lowerable_match` DOES NOT COVER THIS, and the distinction is the point. That guard refuses
to LOWER a `match` whose pattern could bind a rule — it protects matches inside a DEFINITION. This is
a `!` DIRECTIVE, which is never compiled at all, so no per-clause guard can ever see it. The hazard is
at PROGRAM level: the question is not "may this match be compiled" but "may this program's
definitions be compiled AT ALL, given something in it reads the rules".

The answer is no, and it cannot be narrowed to the definitions the query happens to name: a pattern
like `(= (\$p Fritz) T)` binds its head, so which rules it can see is not decidable from the pattern.
Compile nothing, and say so in `introspects`.

Scope: rule-shaped (`=`) and type-shaped (`:`) patterns, plus a bare-variable pattern which matches
everything including rules — the same three shapes `_lowerable_match` rejects, applied to the whole
program instead of one goal."""
function _program_introspects_rules(program::AbstractString)::Bool
    # PARSED, NOT STRING-SCANNED. A `match` is almost never the top-level form — in the corpus it is
    # wrapped, e.g. `!(assertEqualToResult (match &self (= ($p Fritz) T) $p) …)`. Reading the outer
    # form's arguments finds `(match …)` and never reaches its pattern, so the first version of this
    # guard missed the very case it was written for.
    sp = Eval.Space()
    for (bang, f) in mm2_split_forms(program)
        bang || continue
        a = try
            toks = Eval.tokenize(String(f)); i = Ref(1)
            Eval.parse_from(toks, i, sp.tokens)
        catch
            continue
        end
        _reads_rules(a) && return true
    end
    false
end

"Walk an atom for a `(match <space> <pattern> …)` whose pattern can bind a rule or a type."
function _reads_rules(a)::Bool
    a isa StandardMeTTa.Expression || return false
    ch = (a::StandardMeTTa.Expression).children
    if length(ch) >= 3
        h = ch[1]
        hname = h isa StandardMeTTa.Sym ? String((h::StandardMeTTa.Sym).name) :
                h isa StandardMeTTa.Grounded && hasfield(typeof((h::StandardMeTTa.Grounded).value), :name) ?
                    String(getfield((h::StandardMeTTa.Grounded).value, :name)) : ""
        if hname == "match"
            pat = ch[3]
            # a bare VARIABLE pattern matches everything, rules included
            pat isa StandardMeTTa.Var && return true
            if pat isa StandardMeTTa.Expression && !isempty((pat::StandardMeTTa.Expression).children)
                ph = (pat::StandardMeTTa.Expression).children[1]
                if ph isa StandardMeTTa.Sym
                    n = (ph::StandardMeTTa.Sym).name
                    (n === :(=) || n === :(:)) && return true
                end
                # a VARIABLE head can become `=` at runtime
                ph isa StandardMeTTa.Var && return true
            end
        end
    end
    any(_reads_rules, ch)
end

# ── BACKEND `:mork` — ARROW 6 ────────────────────────────────────────────────────────────────────
# Fig-2's caption: "MeTTa-IL … leverages MORK Atomspace". `:eval` runs the IL on `Eval.Space()`
# (arrow 5); this runs the compiled MM2 on a MORK-backed `CoreSpace`.
#
# A BACKEND PARAMETER, NOT A SECOND RUNNER. Both share region splitting, per-form compilation and
# decline accounting; only the emitter and the execution target differ. `Emit.jl`'s own header states
# the cost of the alternative: "When the same decision is spelled out at N call sites it drifts — the
# source functor was hand-typed at four sites in this tree and three were wrong."
#
# 🔴 INGESTION IS `space_add_all_sexpr!`, NOT `core_add!`/`load_metta!`. `core_add!` routes through
# `parse_metta`/`to_sexpr`, which does NOT preserve MORK PATTERN VARIABLES: the execs then load, are
# SELECTED AND CONSUMED, never match, and the run returns the redex with no answer — a SILENT wrong
# result. Every earlier arrow-6 probe failed on exactly this; the `(~>)` lane has always ingested
# correctly (`MeTTaIL.jl:153`).
#
# 🔴 A FRESH SPACE PER QUERY IS REQUIRED, NOT TIDINESS. MORK consumes an exec when it is SELECTED,
# matched or not (`MORK.wiki/Minimal-MeTTa-2-(MM2).md:19`; upstream `space.rs:1704` `btm.remove`
# precedes `:1707` `interpret`). A second query against the same space would find NO RULES — they
# were consumed answering the first — and would silently return nothing.
#
# ⚠️ Root-prefix only: `core_calculus!` raises on a prefixed CoreSpace pending
# `space_metta_calculus_in_prefix!` upstream.
function _compile_run_mork(program::AbstractString, steps::Int)
    sp = Eval.Space(); Eval.load_core_stdlib!(sp)
    rules = String[]; declined = String[]; queries = String[]; ncompiled = 0
    for r in split_program_regions(program, purity_may_mutate(program))
        for d in r.defs
            m = compile_mm2(sp, d)
            m === nothing ? push!(declined, String(d)) :
                            (append!(rules, m.rules); ncompiled += 1)
        end
        append!(queries, String[String(q) for q in r.queries])
    end
    # ── READBACK: the PROVEN one, taken from `mm2_zam_answers` (MM2Router.jl) rather than re-derived.
    # My first version of this returned `core_atoms(cs)` WHOLESALE and had no redex guard, so it would
    # report the rules themselves as answers whenever they were not fully consumed, and report an
    # UNREDUCED query as a result. Both defects are absent from the original, which had been on file
    # since 2026-08-07. Three things it does that the naive version does not:
    #   1. dump via `space_dump_all_sexpr` and FILTER OUT the `exec` atoms — they are machinery, never
    #      answers, and any that were not selected are still sitting in the space;
    #   2. SORT, so the answer set is deterministic (MORK's traversal order is not a contract);
    #   3. 🔴 if the REDEX IS STILL PRESENT, or nothing came back at all, NOTHING FIRED — report it as
    #      a fallback rather than as an answer. Without this a non-reduction is indistinguishable from
    #      a successful one, which is the silent-wrong-answer shape this lane exists to avoid.
    answers = Tuple{String, Vector{String}}[]; unreduced = String[]; total = 0
    for q in queries
        cs = new_core_space()
        for rule in rules
            space_add_all_sexpr!(cs.inner, rule)
        end
        space_add_all_sexpr!(cs.inner, q)
        total += core_calculus!(cs, steps)
        dump = String[String(strip(l)) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                      if !isempty(strip(l))]
        reduct = sort(String[x for x in dump
                             if !(startswith(x, "(") && mm2_head(x) == "exec")])
        if strip(q) in reduct || isempty(reduct)
            push!(unreduced, q)                 # redex persisted / nothing produced ⇒ did NOT reduce
            push!(answers, (q, String[]))
        else
            push!(answers, (q, reduct))
        end
    end
    (; answers, compiled = ncompiled, fell_back = length(declined), exhausted = String[],
       introspects = false, space = nothing, declined, unreduced, steps_run = total)
end

function _compile_run_inner(program::AbstractString, fallback::Bool, backend::Symbol)
    backend === :mork && return _compile_run_mork(program, 1_000_000)
    backend === :eval || error("compile_run: unknown backend `:$backend` — expected :eval or :mork")
    sp = Eval.Space(); Eval.load_core_stdlib!(sp)
    # A program that reads its own rules must run on SOURCE rules — see `_program_introspects_rules`.
    introspects = _program_introspects_rules(program)
    answers = Tuple{String, Vector{String}}[]
    exhausted = String[]
    ncompiled = 0
    nfallback = 0
    for r in split_program_regions(program, purity_may_mutate(program))
        for d in r.defs
            il = introspects ? nothing : compile_definition(sp, d)
            if il === nothing
                fallback || error("compile_run: declined and fallback=false — $(first(d, 80))")
                Eval.load_metta!(sp, d)
                nfallback += 1
            else
                # ATOMS, not text. `load_metta!` on a non-directive form is exactly
                # `add_atom!(space, parse(form))` (Eval.jl:2649), so this is the same operation with
                # the round-trip removed — and the round-trip is where `Space`, `StateCell` and
                # grounded strings were being corrupted.
                for a in il.atoms
                    Eval.add_atom!(sp, _resolve_tokens(a, sp))
                end
                ncompiled += 1
            end
        end
        for q in r.queries
            res = try
                Eval.load_metta!(sp, "!" * q)
            catch e
                # The step limit throws. Record WHICH query exhausted the budget and keep going —
                # a bounded run that reports its overruns beats an unbounded one that hangs, and
                # beats a bounded one that quietly returns nothing.
                if e isa ErrorException && occursin("step limit", e.msg)
                    push!(exhausted, String(q))
                    push!(answers, (String(q), String[]))
                    continue
                end
                rethrow()
            end
            push!(answers, (String(q),
                  String[string(x) for y in res for x in (y isa AbstractVector ? y : [y])]))
        end
    end
    (; answers, compiled = ncompiled, fell_back = nfallback, exhausted, introspects, space = sp)
end
