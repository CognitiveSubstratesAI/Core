# test_eval_one_step.jl — `(eval X)` MAKES ONE STEP, so X's arguments are not reduced for you.
#
# ─── THE RULE COMES FROM THE LANGUAGE, NOT FROM A CORPUS ─────────────────────────────────────────
# `docs/specs/metta grammar/metta.txt:96`, the minimal-MeTTa instruction glossary:
#
#     (eval <atom to evaluate>) - makes ONE STEP of the evaluation
#
# hyperon's corelib says it verbatim ("Evaluates input atom, makes one step of the evaluation"). One
# step means a GROUNDED primitive under `eval` receives its arguments AS GIVEN — so an emitted
# `(eval (== $x (car-atom $l)))` compares `$x` against the unreduced expression. Hoisting nested
# calls into their own `chain` is precisely what A-normalization exists to do.
#
# This is checkable at EMISSION, on every clause, with no corpus and no execution. It would have
# failed the day the emitter was written; instead the class surfaced a day later through one corpus
# script, and only because that script happened to exercise it.
#
# ─── WHY THE PREDICATE IS NARROW, AND HOW IT GOT THAT WAY ────────────────────────────────────────
# 🔴 THE FIRST TWO VERSIONS OF THIS CHECK WERE WRONG, AND AN EXTERNAL CORPUS IS WHAT SHOWED IT.
# Measured against CeTTa's 292 .metta files (a corpus nobody here wrote):
#
#     any nested call under `eval`          277 hits — flags `(Nil)`, a DATA CONSTRUCTOR, and
#                                                      `match`, whose arguments are TEMPLATES
#     + call-vs-data knowledge               33 hits — needs the whole-program defined-head set,
#                                                      i.e. THE SAME knowledge the compiler lacks
#     + grounded-head-only                    7 hits — the version below
#
# The last narrowing came from a CeTTa case that CONTRADICTED the rule as I first stated it:
# `(eval (member2 $x (cdr-atom $list)))` returns `True`. A USER-DEFINED head is safe, because the
# interpreter's own call evaluation reduces its arguments. Only a grounded primitive does not.
#
# Had the broad form been wired in as a compiler decline — which was the plan — it would have
# declined ~55 CORRECT clauses of our own `lib/` to fix 33. Our 26-script corpus would not have
# caught that. 292 files written by other people did. That is the reason this file scans an external
# corpus at all, rather than only our own.
using MeTTaCore
using Test

const _E1_F = MeTTaCore.CompilerFrontend
const _E1_A = MeTTaCore.CompilerANormal
const _E1_E = MeTTaCore.CompilerEmitIL
const _E1_V = MeTTaCore.Eval
const _E1_S = MeTTaCore.StandardMeTTa

const _E1_CETTA = "/home/shivaji1012/JuliaAGI/dev-zone/CeTTa"
const _E1_OURS  = normpath(joinpath(dirname(pathof(MeTTaCore)), ".."))

"Heads whose ARGUMENTS are patterns/templates/spaces — never things to reduce first."
const _E1_TEMPLATE = Set(["match","evalc","unify","superpose","collapse","quote","add-atom",
                          "remove-atom","new-space","get-type","case","if","if-equal","if-error"])

"""Minimal-MeTTa instructions that COMPUTE A VALUE, and so are reducible in argument position.

⚠️ THESE ARE NOT IN `TOKEN_REGISTRY` — measured: `==`/`+`/`*`/`>=`/`and` are registered, `car-atom`
and `cdr-atom` are NOT, because the dispatcher handles instructions by head name rather than through
the token table (`Eval.interpret_stack`). Taking the registry as "everything that reduces" therefore
silently dropped `(eval (== \$x (car-atom \$list)))` — the one shape verified by execution in the
first testset below. An absence in one registry is not an absence in the language.

Control instructions (`chain`/`function`/`return`/`unify`) are deliberately NOT here: they do not
appear in argument position as values to be pre-reduced."""
const _E1_REDUCING_INSTR = Set(["car-atom","cdr-atom","cons-atom","decons-atom",
                                "size-atom","index-atom","eval","collapse-bind"])

# ⚠️ BOTH READERS MUST SKIP STRING LITERALS. Measured: without this, `(eval (== $token "("))` — the
# paren INSIDE the string — desynchronises the depth counter and the "form" reported runs off into
# the rest of the clause. The scan then counts and prints garbage. MeTTa's own grammar puts `(` and
# `)` inside `STRING` (`metta_language_spec.md:39`), so a reader that ignores strings is wrong by the
# grammar, not merely fragile.

"The balanced parenthesised group of `s` beginning at byte index `i`, ignoring string literals."
function _e1_balanced(s::AbstractString, i::Int)
    depth = 0; j = i; instr = false
    while j <= lastindex(s)
        c = s[j]
        if c == '"'
            instr = !instr
        elseif !instr
            c == '(' && (depth += 1)
            c == ')' && (depth -= 1; depth == 0 && break)
        end
        j = nextind(s, j)
    end
    s[i:min(j, lastindex(s))]
end

"Top-level parenthesised groups inside `s`, ignoring string literals."
function _e1_subforms(s::AbstractString)
    out = String[]; depth = 0; start = 0; instr = false
    for (k, ch) in enumerate(s)
        if ch == '"'
            instr = !instr
        elseif !instr
            if ch == '('
                depth += 1; depth == 1 && (start = k)
            elseif ch == ')'
                depth -= 1; depth == 0 && start > 0 && push!(out, s[start:k])
            end
        end
    end
    out
end

function _e1_head(f::AbstractString)
    inner = strip(f[nextind(f, 1):prevind(f, lastindex(f))])
    m = match(r"^\(?([^\s()]+)", inner)
    m === nothing ? "" : m.captures[1]
end

"""Violating `(eval …)` forms in one emitted clause.

A violation is an `(eval X)` where X is headed by a GROUNDED primitive and some parenthesised
argument of X is headed by something that REDUCES (a grounded primitive, or a head defined anywhere
in the corpus being scanned)."""
function _e1_violations(clause::AbstractString, reducible::Set{String}, grounded::Set{String})
    bad = String[]
    for m in eachmatch(r"\(eval ", clause)
        form  = _e1_balanced(clause, m.offset)
        inner = strip(form[6:max(6, prevind(form, lastindex(form)))])
        startswith(inner, "(") || continue          # (eval $v) / (eval sym) — already atomic
        h0 = _e1_head(inner)
        (h0 in _E1_TEMPLATE || !(h0 in grounded)) && continue
        for a in _e1_subforms(inner[nextind(inner, 1):prevind(inner, lastindex(inner))])
            h = _e1_head(a)
            (isempty(h) || startswith(h, "\$") || !(h in reducible)) && continue
            push!(bad, form); break
        end
    end
    bad
end

"""Scan `dirs` under `root`. Deciding call-vs-data needs the set of defined heads, and the SCOPE of
that set changes the answer — so the scope is a decision, not a detail.

PER FILE: a head counts as reducible in a clause only if THAT FILE defines it (or it is a grounded
primitive). MEASURED both ways 2026-08-11 over our corpus: per-file 33, corpus-wide union 184. The
union is not more thorough, it is WRONG — one file defining `(= (Nil) …)` makes every other file's
`(Nil)` data constructor look like a call, and `(eval (== \$pressure (Nil)))` in `chemistry.metta`
gets flagged for a definition it never sees.

Per-file UNDER-reports: a genuine cross-file call through `import!` is missed. That is the deliberate
direction for a ratchet — a gate with false positives blocks real work and gets switched off, which
is worse than a gate that catches less. The same choice PLeaTTa's `compiler-mismatch-witnesses.tsv`
states for its normalization: fail closed by erasing a divergence rather than manufacturing one."""
function _e1_scan(root::AbstractString, dirs, cap::Int)
    sp = _E1_V.Space(); _E1_V.load_core_stdlib!(sp)
    grounded = Set{String}(String(k) for k in keys(_E1_V.TOKEN_REGISTRY))
    files = String[]
    for d in dirs
        p = joinpath(root, d); isdir(p) || continue
        for (rt, _, fs) in walkdir(p), f in fs
            endswith(f, ".metta") && push!(files, joinpath(rt, f))
        end
    end
    sort!(files); length(files) > cap && (files = files[1:cap])

    nfile = 0; nclause = 0; hits = Tuple{String, String}[]
    for f in files
        src = try read(f, String) catch; continue end
        atoms = try
            toks = _E1_V.tokenize(src); i = Ref(1); out = _E1_S.Atom[]
            while i[] <= length(toks)
                toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
                push!(out, _E1_V.parse_from(toks, i, sp.tokens))
            end
            out
        catch; continue end
        prog = try _E1_F.lower_program(atoms) catch; continue end
        isempty(prog.definitions) && continue
        # PER FILE, per the scope decision above: this file's own heads, plus grounded primitives.
        reducible = union(grounded, _E1_REDUCING_INSTR)
        for d in prog.definitions; push!(reducible, String(d.name)); end
        cls = try _E1_A.translate_program(prog) catch; continue end
        r = try _E1_E.emit_il_program(cls) catch; continue end
        nfile += 1
        for c in r.clauses
            nclause += 1
            for b in _e1_violations(c, reducible, grounded); push!(hits, (basename(f), b)); end
        end
    end
    (files = nfile, clauses = nclause, hits = hits)
end

@testset "`eval` makes ONE STEP — no grounded primitive may get an unreduced call as an argument" begin

    # ── THE DEFECT IS REAL, shown in two lines with NO compiler involved. ────────────────────────
    # ANTI-VACUITY, and the important half of this file: a count-only ratchet would pass while the
    # class was imaginary. This asserts the language behaviour the counts are counting.
    @testset "the behaviour itself: one-step eval gives a SILENTLY WRONG boolean" begin
        function answers(q)
            prev = _E1_V._INTERPRET_MAX[]; _E1_V.interpret_max_steps!(4_000)
            try
                sp = _E1_V.Space(); _E1_V.load_core_stdlib!(sp)
                rs = _E1_V.load_metta!(sp, "!" * q)
                sort(String[string(x) for y in rs for x in (y isa AbstractVector ? y : [y])])
            finally
                _E1_V._INTERPRET_MAX[] = prev
            end
        end
        # Source semantics: `car-atom` reduces, then `==` compares b with b.
        @test answers("(== b (car-atom (b c)))") == ["True"]
        # ONE STEP: `==` compares `b` against the UNREDUCED `(car-atom (b c))`. Not an error, not
        # NotReducible — a plausible, silently wrong `False`. This is what the scan below counts.
        @test answers("(eval (== b (car-atom (b c))))") == ["False"]

        # …and a USER-DEFINED head is NOT affected, which is why the predicate is narrow. Measured
        # on CeTTa; reproduced here so the narrowing cannot be quietly widened later.
        defs = "(= (m2 \$x \$l) (if (== \$l ()) False " *
               "(if (== \$x (car-atom \$l)) True (m2 \$x (cdr-atom \$l)))))\n"
        prev = _E1_V._INTERPRET_MAX[]; _E1_V.interpret_max_steps!(4_000)
        try
            sp = _E1_V.Space(); _E1_V.load_core_stdlib!(sp); _E1_V.load_metta!(sp, defs)
            rs = _E1_V.load_metta!(sp, "!(eval (m2 b (a b c)))")
            @test "True" in String[string(x) for y in rs
                                   for x in (y isa AbstractVector ? y : [y])]
        finally
            _E1_V._INTERPRET_MAX[] = prev
        end
    end

    # ── OUR OWN corpus — the ratchet. ────────────────────────────────────────────────────────────
    @testset "our corpus: the count may not rise" begin
        r = _e1_scan(_E1_OURS, ["stdlib", "src/standard", "lib"], 500)
        for (f, b) in first(r.hits, 6)
            @info "eval-one-step violation (ours)" file=f form=first(b, 100)
        end
        println("     ours: files=$(r.files) clauses=$(r.clauses) violations=$(length(r.hits))")
        # MEASURED 2026-08-11: 21, nearly all `(eval (== (car-atom $x) SYM))` — the exact shape the
        # first testset proves returns a silently wrong `False`. They pass the health gate only
        # because it runs the INTERPRETER, and pass the coverage ratchet only because the ratchet
        # COUNTS emitted clauses and never executes them. Neither gate could have seen this.
        # A DROP MUST BE RECORDED DELIBERATELY, same discipline as the corpus differential.
        @test length(r.hits) <= 21
        @test r.clauses > 500                     # anti-vacuity: the scan actually emitted
    end

    # ── AN EXTERNAL corpus — the part that falsified the first two versions of this check. ───────
    #
    # OPT-IN, because it is a CALIBRATION tool rather than a per-run gate, and because it costs the
    # suite time it does not have. MEASURED: the full suite already sat at ~9-10 min
    # (`test_compile_lane_fuzz.jl` alone is ~255 s in-suite, the coverage ratchet ~150 s), and adding
    # this scan of 98 external files pushed it past its budget. Its VALUE is in what it does when you
    # change the predicate — it is what proved the first three versions wrong — and that is an act you
    # perform deliberately, not something every suite run needs to repeat.
    #
    #     CORE_TEST_CETTA=1 tools/run_tests.sh test/compiler/test_eval_one_step.jl
    #
    # The our-corpus ratchet above is NOT opt-in: that one guards against regression and runs always.
    @testset "CeTTa corpus: the count may not rise" begin
        if get(ENV, "CORE_TEST_CETTA", "") == ""
            @info "CeTTa scan SKIPPED (opt-in) — set CORE_TEST_CETTA=1 to run it" expected_violations=3
            @test_skip false
        elseif !isdir(_E1_CETTA)
            # LOUD, never silent. A skipped external gate that reports nothing is indistinguishable
            # from a passing one, which is the failure mode this whole file exists to avoid.
            @warn "CeTTa corpus ABSENT — this half of the gate did NOT run" path=_E1_CETTA
            @test_skip false
        else
            r = _e1_scan(_E1_CETTA, ["lib", "examples"], 150)
            for (f, b) in first(r.hits, 6)
                @info "eval-one-step violation (CeTTa)" file=f form=first(b, 100)
            end
            println("     CeTTa: files=$(r.files) clauses=$(r.clauses) violations=$(length(r.hits))")
            # MEASURED 2026-08-11 over CeTTa lib+examples: 3. Lower than ours not because CeTTa is
            # cleaner but because per-file scoping misses its heavier cross-file structure — the
            # under-reporting is stated above and is the intended direction.
            @test length(r.hits) <= 3
            @test r.clauses > 800                 # anti-vacuity
        end
    end
end
