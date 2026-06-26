# MM2Router.jl — dual-lane program routing.
#
# Adopted from CeTTa's MM2 loader dispatch (`src/library.c` mm2-load: partition a loaded program by
# `cetta_mm2_atom_is_exec_rule` into the PROGRAM handle vs the CONTEXT handle, and reject top-level `!`
# in the pure-program lane via `cetta_mm2_atoms_have_top_level_eval`).
#
# PRIMUS-NATIVE adaptation (deliberately NOT a 1:1 port):
#   - CeTTa needs a surface→IR rewrite (`mm2_lower.c`) + a Rust-MORK FFI byte-bridge; PRIMUS-MORK is
#     native Julia and executes the MM2 *surface* directly (CompatSource/BTMSource/ACTSource/CmpSource
#     (==/!=)/GroundedSource + `,`/ACT/O/+/- sinks), so NEITHER layer is needed here.
#   - CeTTa keeps separate program/context MORK handles; PRIMUS uses ONE native CoreSpace — data and
#     exec atoms live in the same trie and `space_metta_calculus!` steps the exec rules over the data.
#
# The gap this closes: `load_metta!` splits `!`→`metta_run` vs non-`!`→`add_atom!`, but never detects
# `(exec …)` rules — they got `add_atom!`'d INERT into the interpreter space, never reaching the MORK
# engine. This router detects them and routes data+exec to the native MORK lane.

# ── top-level form splitter: paren-depth aware, `!`-prefix aware, `;`-comment aware ──
function mm2_split_forms(program::AbstractString)::Vector{Tuple{Bool, String}}
    forms = Tuple{Bool, String}[]
    s = collect(program); n = length(s); i = 1
    while i <= n
        while i <= n && (isspace(s[i]) || s[i] == ';')
            if s[i] == ';'
                while i <= n && s[i] != '\n'; i += 1; end
            else
                i += 1
            end
        end
        i > n && break
        bang = false
        if s[i] == '!'
            bang = true; i += 1
            while i <= n && isspace(s[i]); i += 1; end
        end
        i > n && break
        start = i
        if s[i] == '('
            depth = 0
            while i <= n
                s[i] == '(' && (depth += 1)
                s[i] == ')' && (depth -= 1)
                i += 1
                depth == 0 && break
            end
        else
            while i <= n && !isspace(s[i]); i += 1; end
        end
        push!(forms, (bang, String(s[start:i-1])))
    end
    forms
end

"Head symbol of a top-level form (`\"exec\"` for an exec-rule)."
function mm2_head(form::AbstractString)::String
    t = lstrip(form)
    startswith(t, "(") || return strip(t)
    inner = SubString(t, nextind(t, firstindex(t)))
    j = findfirst(c -> isspace(c) || c == '(' || c == ')', inner)
    j === nothing ? strip(inner) : strip(SubString(inner, firstindex(inner), prevind(inner, j)))
end

"True iff `form` is an `(exec …)` rule (the MM2-program lane)."
mm2_is_exec_rule(form::AbstractString)::Bool = mm2_head(form) == "exec"

# ── (=)→exec auto-routing guard (the grounded-op classifier) ──
# Collect the operator-position head of `form` and of every nested sub-expression (recursively).
function mm2_collect_heads!(heads::Vector{String}, form::AbstractString)
    t = strip(form)
    (startswith(t, "(") && endswith(t, ")")) || return heads     # leaf (var/sym/number) — no head
    args = try mm2_expr_args(t) catch; return heads end
    isempty(args) && return heads
    push!(heads, args[1])
    for k in 2:length(args); mm2_collect_heads!(heads, args[k]); end
    heads
end

"""
    mm2_is_relational(rule) -> Bool

True iff `(= LHS RHS)` is safe to auto-lower to the MORK exec lane: EVERY operator-position head in
LHS/RHS is a plain relation symbol — NONE is a grounded op or a special form. Authority = the interpreter's
`TOKEN_REGISTRY` (grounded ops: `+ - * / < == and match superpose collapse foldl-atom case …`) ∪
`MINIMAL_OPS` (eval/chain/function/unify/cons-atom/decons-atom/…). Conservative: any grounded/special head
⇒ `false` (stay in the Interpreter lane). NB the authority is the INTERPRETER registry, NOT MORK's
`GROUNDED_REGISTRY` (which holds only the 3 WILLIAM ops — arithmetic is a calculus source/sink TYPE there,
so `MORK.is_grounded("+")` is false and would misclassify `(= (fib …) (+ …))` as relational). The `,`
conjunction marker is allowed (it is the exec source list, not an operator).
"""
function mm2_is_relational(rule::AbstractString)::Bool
    a = try mm2_expr_args(rule) catch; return false end
    (length(a) == 3 && a[1] == "=") || return false
    heads = String[]
    mm2_collect_heads!(heads, a[2]); mm2_collect_heads!(heads, a[3])
    for h in heads
        h == "," && continue
        (haskey(Interpreter.TOKEN_REGISTRY, h) || Symbol(h) in Interpreter.MINIMAL_OPS) && return false
    end
    true
end

"""
    mm2_partition(program) -> (; bangs, exec, data)

Partition a MeTTa/MM2 program's top-level forms into the three lanes: `bangs` (`!`-directives →
interpreter), `exec` (`(exec …)` rules + auto-lowered RELATIONAL `(= …)` rules → MORK engine), `data`
(facts + non-relational `(= …)` rules + everything else → the space). A `(= LHS RHS)` rule that passes
`mm2_is_relational` is auto-lowered via `mm2_lower_equals` into the exec lane; one that does not (grounded
ops / special forms) stays in `data` exactly as before — so existing behavior is preserved by default and
the new routing fires only on provably-relational rules.
"""
function mm2_partition(program::AbstractString)
    forms = mm2_split_forms(program)
    bangs = String[f for (b, f) in forms if b]
    exec  = String[]
    data  = String[]
    for (b, f) in forms
        b && continue                                            # `!` forms already collected in `bangs`
        if mm2_is_exec_rule(f)
            push!(exec, f)
        elseif mm2_head(f) == "=" && mm2_is_relational(f)
            push!(exec, mm2_lower_equals(f))                     # relational (= …) → auto-lower to exec
        else
            push!(data, f)                                       # facts / non-relational (= …) → data (unchanged)
        end
    end
    (bangs = bangs, exec = exec, data = data)
end

"""
    mm2_run!(cs::CoreSpace, program; steps=1_000_000, allow_bang=false) -> (; n_exec, n_data, n_bang)

The MM2-program lane: add `data` then `exec` atoms to the native MORK CoreSpace `cs`, then step the
exec-calculus. Per CeTTa's pure-program-lane discipline, top-level `!` forms are rejected (they belong
to the interpreter lane) unless `allow_bang=true` (then they are partitioned out but not run here).
"""
function mm2_run!(cs::CoreSpace, program::AbstractString;
                  steps::Int = 1_000_000, allow_bang::Bool = false)
    p = mm2_partition(program)
    if !allow_bang && !isempty(p.bangs)
        error("mm2_run!: MM2-program lane does not accept top-level ! forms " *
              "($(length(p.bangs)) found) — route those to the interpreter lane")
    end
    isempty(p.data) || space_add_all_sexpr!(cs.inner, join(p.data, "\n"))
    isempty(p.exec) || space_add_all_sexpr!(cs.inner, join(p.exec, "\n"))
    isempty(p.exec) || space_metta_calculus!(cs.inner, steps)
    (n_exec = length(p.exec), n_data = length(p.data), n_bang = length(p.bangs))
end

# ── piece 2: the match→exec bridge (route a `!(match …)` into the MM2 lane) ──

"Top-level argument forms of a paren expr, e.g. `(match S P T)` → [\"match\",\"S\",\"P\",\"T\"]."
function mm2_expr_args(form::AbstractString)::Vector{String}
    t = strip(form)
    (startswith(t, "(") && endswith(t, ")")) || error("mm2_expr_args: not an expr: $form")
    inner = SubString(t, nextind(t, firstindex(t)), prevind(t, lastindex(t)))
    args = String[]; depth = 0; buf = IOBuffer()
    for c in inner
        if c == '('; depth += 1; print(buf, c)
        elseif c == ')'; depth -= 1; print(buf, c)
        elseif isspace(c) && depth == 0
            s = String(take!(buf)); isempty(s) || push!(args, s)
        else; print(buf, c); end
    end
    s = String(take!(buf)); isempty(s) || push!(args, s)
    args
end

"""
    mm2_lower_match(query) -> String

§10.3 lowering: `(match SPACE PAT TMPL)` → `(exec 0 (, PAT) (, TMPL))` (SPACE dropped — runs vs the
one trie; a conjunctive PAT `(, …)` passes through as the source list). The clean inert lowering;
NOT the materializing supercompiler.
"""
function mm2_lower_match(query::AbstractString)::String
    a = mm2_expr_args(query)
    (length(a) == 4 && a[1] == "match") ||
        error("mm2_lower_match: expected (match SPACE PAT TMPL), got: $query")
    pat, tmpl = a[3], a[4]
    src = startswith(lstrip(pat), "(,") ? pat : "(, $pat)"
    "(exec 0 $src (, $tmpl))"
end

"""
    mm2_lower_equals(rule) -> String

Lower a `(= LHS RHS)` rewrite rule to an exec rule: `(= LHS RHS)` → `(exec 0 (, LHS) (, RHS))` — the
SAME shape as `mm2_lower_match` (LHS becomes the exec SOURCE pattern, RHS the SINK template). This is
the `(=)→MM2` bridge for the RELATIONAL subset: forward-closure semantics (for every data atom matching
LHS, derive RHS), sound when LHS/RHS carry NO grounded ops — those (arithmetic, control) need the
interpreter lane and are rejected. A conjunctive LHS `(, …)` passes through as the source list.
"""
function mm2_lower_equals(rule::AbstractString)::String
    a = mm2_expr_args(rule)
    (length(a) == 3 && a[1] == "=") ||
        error("mm2_lower_equals: expected (= LHS RHS), got: $rule")
    lhs, rhs = a[2], a[3]
    src = startswith(lstrip(lhs), "(,") ? lhs : "(, $lhs)"
    "(exec 0 $src (, $rhs))"
end

# ── typed Atom → MM2 sexpr (the LIVE-eval handoff: load_metta!/eval hold typed Atoms, not strings) ──
const _MM2_ATOM = Interpreter.StandardMeTTa
function _typed_atom_to_expr!(io::IO, a)
    if a isa _MM2_ATOM.Sym
        print(io, a.name)
    elseif a isa _MM2_ATOM.Var
        print(io, "\$", a.name)                          # drop internal #id — MORK assigns De Bruijn on parse
    elseif a isa _MM2_ATOM.Expression
        print(io, "(")
        for (k, c) in enumerate(a.children); k > 1 && print(io, " "); _typed_atom_to_expr!(io, c); end
        print(io, ")")
    elseif a isa _MM2_ATOM.Grounded
        print(io, a.value)
    else
        print(io, a)
    end
end

"""
    typed_atom_to_expr(atom) -> String

Serialize a typed `StandardMeTTa` `Atom` to the MeTTa sexpr string MORK's parser ingests — the inverse
of parse, for the live-eval handoff (eval holds typed `Atom` objects, not source strings). Variables
emit as `\$name` with the internal `#id` dropped; MORK assigns the byte-level De Bruijn (NewVar/VarRef)
on `space_add_all_sexpr!`, and interned/repeated vars print consistently in first-occurrence order.
Round-trip gated: `mm2_lower_equals(typed_atom_to_expr(parse(rule))) == mm2_lower_equals(rule_string)`.
"""
typed_atom_to_expr(a)::String = (io = IOBuffer(); _typed_atom_to_expr!(io, a); String(take!(io)))

# is `a` a `(= LHS RHS)` rewrite-rule Atom? (vs a fact / other atom)
_mm2_is_eq_rule(a) = a isa _MM2_ATOM.Expression && length(a.children) == 3 &&
                     a.children[1] isa _MM2_ATOM.Sym && a.children[1].name == Symbol("=")

# MORK byte-Expr HARD LIMITS (upstream wiki Data-in-MORK): an Expression has ≤63 children (arity tag is
# 6-bit) and an expression has ≤64 distinct vars (De Bruijn level is 6-bit). A rule exceeding either cannot
# encode → must NOT route to MORK (stays in the interpreter). Conservative: reject on >63 children.
function _mm2_collect_limits!(a, vars)::Bool
    if a isa _MM2_ATOM.Expression
        length(a.children) > 63 && return false
        for c in a.children; _mm2_collect_limits!(c, vars) || return false; end
    elseif a isa _MM2_ATOM.Var
        push!(vars, a)
    end
    true
end
_mm2_within_mork_limits(a)::Bool =
    (vars = Set{_MM2_ATOM.Var}(); _mm2_collect_limits!(a, vars) && length(vars) <= 64)

"Typed-Atom overload of the grounded-op guard — serialize then classify; also rejects rules exceeding MORK's
byte-Expr limits (arity 63 / 64 vars), which can't encode and must stay in the interpreter."
mm2_is_relational(atom::_MM2_ATOM.Atom)::Bool =
    _mm2_within_mork_limits(atom) && mm2_is_relational(typed_atom_to_expr(atom))

"""
    mm2_lane_from_atoms(atoms) -> CoreSpace

The LIVE-eval handoff (mirror form): build a MORK CoreSpace from a list of typed `Atom`s (e.g. a live
interpreter Space's user atoms). Relational `(= …)` rules → auto-lowered to `(exec …)`; non-rule atoms
→ data; grounded/special `(= …)` rules → skipped (interpreter-only). Read-only on the source atoms — the
interpreter keeps its rules (MIRROR, not route), so this is bisimulation-safe. The caller runs
`space_metta_calculus!` to saturate. This is the substrate-lane half of P2; full ROUTE (interpreter
defers to MORK + delete) is a later bisimulation-gated step.
"""
# classify typed atoms → (data sexprs, lowered exec-rule sexprs) for the MORK lane
function _mm2_classify_atoms(atoms)
    data = String[]; execs = String[]
    for a in atoms
        s = typed_atom_to_expr(a)
        if mm2_is_relational(a)
            push!(execs, mm2_lower_equals(s))                     # relational (= …) → exec
        elseif !_mm2_is_eq_rule(a)
            push!(data, s)                                        # fact / data
        end                                                       # else grounded (= …) → skip (interp-only)
    end
    (data, execs)
end

function mm2_lane_from_atoms(atoms)::CoreSpace
    cs = new_core_space()
    data, execs = _mm2_classify_atoms(atoms)
    isempty(data)  || space_add_all_sexpr!(cs.inner, join(data, "\n"))
    isempty(execs) || space_add_all_sexpr!(cs.inner, join(execs, "\n"))
    cs
end

# ⚠ SEMANTICS BOUNDARY (the route gate): `space_metta_calculus!` on this lane computes the FORWARD CLOSURE
# (Datalog forward-chaining) of all relational rules. That EQUALS the interpreter only for SINGLE-STEP
# forward derivation (the `!(match &self LHS RHS)` shape) — verified across single-rule / different-relation /
# conjunctive-join shapes. For a multi-rule CHAIN (a→b→c) MORK derives the whole closure {b,c} whereas the
# interpreter `(=)` REDUCTION gives the normal form (c). So ROUTE is sound for forward-derivation/Datalog
# workloads (where the closure IS the wanted answer), NOT as a drop-in for general (=) reduction-to-normal-form.

"""
    mm2_lane_from_space(isp) -> CoreSpace

Convenience over `mm2_lane_from_atoms`: mirror a LIVE interpreter `Space`'s OWN atoms
(`atoms[lib_count+1:end]` — excludes the imported stdlib) into a MORK lane. The whole-Space live-eval handoff.
"""
mm2_lane_from_space(isp::Interpreter.Space)::CoreSpace =
    mm2_lane_from_atoms(@view isp.atoms[(isp.lib_count + 1):end])

"""
    mm2_lane_saturate!(atoms; max_rounds=64) -> CoreSpace

The RECURSIVE route driver: build the MORK lane from typed atoms and run the exec calculus to a FIXPOINT
(full Datalog forward-closure). Per the MM2 spec an `exec` instruction is CONSUMED when it fires ("removed
no matter what"), so a single `space_metta_calculus!` is single-pass; recursion is the spec's "repeated exec
selections". This drives that: re-add the exec rules and re-run until the atom count stabilizes — so a
recursive relational rule (e.g. transitive `reach`) reaches its full closure, which `mm2_lane_from_atoms` +
one calculus step cannot. Sound for forward-derivation/Datalog workloads (the closure is the wanted answer).
"""
function mm2_lane_saturate!(atoms; max_rounds::Int = 64)::CoreSpace
    cs = new_core_space()
    data, execs = _mm2_classify_atoms(atoms)
    isempty(data) || space_add_all_sexpr!(cs.inner, join(data, "\n"))
    isempty(execs) && return cs
    joined = join(execs, "\n"); prev = -1
    for _ in 1:max_rounds
        n = space_val_count(cs.inner)
        n == prev && break                                       # fixpoint reached
        prev = n
        space_add_all_sexpr!(cs.inner, joined)                   # re-add consumed execs
        space_metta_calculus!(cs.inner, 1_000_000)
    end
    cs
end

"""
    mm2_match!(cs::CoreSpace, query; steps=1_000_000) -> Vector{String}

Run a `(match SPACE PAT TMPL)` via the MM2 lane: lower to exec, step the calculus on `cs`'s native
trie (data must already be loaded), and collect the derived TMPL atoms. Equivalent to the interpreter's
`!(match …)` (bisimulation-gated) but on the MORK engine.
"""
function mm2_match!(cs::CoreSpace, query::AbstractString; steps::Int = 1_000_000)
    space_add_all_sexpr!(cs.inner, mm2_lower_match(query))
    space_metta_calculus!(cs.inner, steps)
    tmpl_head = mm2_head(mm2_expr_args(query)[4])
    sort(unique(String[strip(l) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                        if mm2_head(strip(l)) == tmpl_head]))
end

"""
    mm2_route!(cs::CoreSpace, program; steps=1_000_000) -> (; n_exec, n_data, matched, deferred)

Full dual-lane dispatch: data+exec → the MM2 lane (run); each `!(match …)` directive → the match→exec
bridge (`mm2_match!`, results in `matched`); other `!` forms → `deferred` (the interpreter lane — needs
the interpreter/MORK space link, not yet wired).
"""
function mm2_route!(cs::CoreSpace, program::AbstractString; steps::Int = 1_000_000)
    p = mm2_partition(program)
    isempty(p.data) || space_add_all_sexpr!(cs.inner, join(p.data, "\n"))
    isempty(p.exec) || space_add_all_sexpr!(cs.inner, join(p.exec, "\n"))
    isempty(p.exec) || space_metta_calculus!(cs.inner, steps)
    matched = Vector{Tuple{String, Vector{String}}}()
    deferred = String[]
    for b in p.bangs
        if mm2_head(b) == "match"
            push!(matched, (b, mm2_match!(cs, b; steps)))
        else
            push!(deferred, b)
        end
    end
    (n_exec = length(p.exec), n_data = length(p.data), matched = matched, deferred = deferred)
end
