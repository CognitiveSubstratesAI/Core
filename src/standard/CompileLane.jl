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
    compile_definition(sp, form) -> Union{Vector{String}, Nothing}

Compile ONE top-level form to minimal-MeTTa clauses, or `nothing` if it is not a compilable
definition (a bare fact, an unparseable form) or the compiler declines it.

Deliberately per-form: see the correctness constraint above. A form that yields no `(=)` definition —
a ground fact like `(edge a b)` — is NOT a compiler failure and must not be counted as a decline; it
is simply data, and it returns `nothing` so the caller loads it verbatim.
"""
function compile_definition(sp, form::AbstractString)::Union{Vector{String}, Nothing}
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
    prog = try CompilerFrontend.lower_program(atoms) catch; return nothing end
    isempty(prog.definitions) && return nothing        # a fact, not a definition — not a decline
    cls = try CompilerANormal.translate_program(prog) catch; return nothing end
    isempty(cls) && return nothing
    r = try CompilerEmitIL.emit_il_program(cls) catch; return nothing end
    # ALL-OR-NOTHING per form. A form can lower to several clauses; if any is declined, loading the
    # compiled subset plus the whole source form would double the surviving answers (Invariant 6).
    (r.emitted == length(cls) && isempty(r.declined)) || return nothing
    r.clauses
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
function compile_run(program::AbstractString; fallback::Bool = true)
    sp = Eval.Space(); Eval.load_core_stdlib!(sp)
    answers = Tuple{String, Vector{String}}[]
    ncompiled = 0
    nfallback = 0
    for r in split_program_regions(program, purity_may_mutate(program))
        for d in r.defs
            il = compile_definition(sp, d)
            if il === nothing
                fallback || error("compile_run: declined and fallback=false — $(first(d, 80))")
                Eval.load_metta!(sp, d)
                nfallback += 1
            else
                for c in il
                    Eval.load_metta!(sp, c)
                end
                ncompiled += 1
            end
        end
        for q in r.queries
            res = Eval.load_metta!(sp, "!" * q)
            push!(answers, (String(q),
                  String[string(x) for y in res for x in (y isa AbstractVector ? y : [y])]))
        end
    end
    (; answers, compiled = ncompiled, fell_back = nfallback, space = sp)
end
