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
    mm2_partition(program; eq_mode=:relational) -> (; bangs, exec, data)

Partition a MeTTa/MM2 program's top-level forms into the three lanes: `bangs` (`!`-directives →
interpreter), `exec` (`(exec …)` rules + auto-lowered grounded-free `(= …)` rules → MORK engine), `data`
(facts + non-relational `(= …)` rules + everything else → the space). A `(= LHS RHS)` rule that passes
`mm2_is_relational` is auto-lowered via `mm2_lower_equals` into the exec lane using `eq_mode`
(`:relational` forward-closure [default] or `:reduction` delete-redex function-eval); one that does not
(grounded ops / special forms) stays in `data` exactly as before — so existing behavior is preserved by
default and the new routing fires only on provably grounded-free rules.
"""
function mm2_partition(program::AbstractString; eq_mode::Symbol = :relational)
    forms = mm2_split_forms(program)
    bangs = String[f for (b, f) in forms if b]
    exec  = String[]
    data  = String[]
    for (b, f) in forms
        b && continue                                            # `!` forms already collected in `bangs`
        if mm2_is_exec_rule(f)
            push!(exec, f)
        elseif mm2_head(f) == "=" && mm2_is_relational(f)
            push!(exec, mm2_lower_equals(f; mode = eq_mode))     # grounded-free (= …) → auto-lower (relational|reduction)
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
                  steps::Int = 1_000_000, allow_bang::Bool = false, eq_mode::Symbol = :relational)
    p = mm2_partition(program; eq_mode = eq_mode)
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
    mm2_lower_equals(rule; mode=:relational) -> String

Lower a `(= LHS RHS)` rewrite rule to an exec rule. TWO modes — the caller declares which `(=)`
semantics apply (both are `(= LHS RHS)` with no grounded ops, so they are syntactically
indistinguishable; the mode is intent, not inference):

- `:relational` (default) → `(exec 0 (, LHS) (, RHS))`. FORWARD-CLOSURE (Datalog): for every data atom
  matching LHS, DERIVE RHS and **KEEP LHS**. Correct for relations, e.g. `(= (parent \$x \$y) (ancestor \$x \$y))`.
  A conjunctive LHS `(, …)` passes through as the source list. (Same shape as `mm2_lower_match`.)

- `:reduction` → `(exec 0 (I LHS) (O (+ RHS) (- LHS)))`. FUNCTION-EVAL: for every data atom matching LHS,
  ADD RHS and **REMOVE the matched LHS redex** — reduce to normal form. Correct for function defs, e.g.
  `(= (id \$x) \$x)` reduces `(id a)` → `a` (deleting `(id a)`). Mirrors MorkSupercompiler `_lower_eq_snode`
  and the interpreter's reduce-to-normal-form semantics; LHS is a single redex term.

Both are the `(=)→MM2` bridge for the RELATIONAL/grounded-free subset; grounded ops (arithmetic, control)
still need the interpreter or KBSaturation lane and are gated out upstream by `mm2_is_relational`.
"""
function mm2_lower_equals(rule::AbstractString; mode::Symbol = :relational)::String
    a = mm2_expr_args(rule)
    (length(a) == 3 && a[1] == "=") ||
        error("mm2_lower_equals: expected (= LHS RHS), got: $rule")
    lhs, rhs = a[2], a[3]
    if mode === :reduction
        return "(exec 0 (I $lhs) (O (+ $rhs) (- $lhs)))"      # delete redex + add reduct (function-eval)
    elseif mode === :relational
        src = startswith(lstrip(lhs), "(,") ? lhs : "(, $lhs)"
        return "(exec 0 $src (, $rhs))"                        # keep LHS + add RHS (forward-closure)
    else
        error("mm2_lower_equals: unknown mode $mode (expected :relational or :reduction)")
    end
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

# ⚠ SEMANTICS BOUNDARY (the route gate): `space_metta_calculus!` is the MM2 exec calculus — pattern-directed
# METAGRAPH REWRITING (match → instantiate → write; the MM2 spec: exec ≡ match + add-atom). On this lane it
# computes the FORWARD-REWRITING closure of all relational rules. That EQUALS the interpreter only for
# SINGLE-STEP forward derivation (the `!(match &self LHS RHS)` shape) — verified across single-rule /
# different-relation / conjunctive-join shapes. For a multi-rule CHAIN (a→b→c) MORK's forward rewriting derives
# the whole closure {b,c} whereas the interpreter `(=)` REDUCTION gives the normal form (c). So ROUTE is sound
# for forward-derivation workloads (where the closure IS the wanted answer), NOT a drop-in for general (=)
# reduction-to-normal-form. (NB: this is metagraph rewriting, NOT Datalog — MM2 is general nested-S-expr
# rewriting with removal/priorities; Datalog is at most a narrow special case it can express.)

"""
    mm2_lane_from_space(isp) -> CoreSpace

Convenience over `mm2_lane_from_atoms`: mirror a LIVE interpreter `Space`'s OWN atoms
(`atoms[lib_count+1:end]` — excludes the imported stdlib) into a MORK lane. The whole-Space live-eval handoff.
"""
mm2_lane_from_space(isp::Interpreter.Space)::CoreSpace =
    mm2_lane_from_atoms(@view isp.atoms[(isp.lib_count + 1):end])

"""
    mm2_lane_saturate!(atoms; max_rounds=64) -> CoreSpace

The RECURSIVE route driver: build the MORK lane from typed atoms and run the MM2 exec calculus (metagraph
rewriting) to a FIXPOINT (full forward-rewriting closure). Per the MM2 spec an `exec` instruction is CONSUMED
when it fires ("removed no matter what"), so a single `space_metta_calculus!` is single-pass; recursion is the
spec's "repeated exec selections". This drives that: re-add the exec rules and re-run until the atom count
stabilizes — so a recursive relational rule (e.g. transitive `reach`) reaches its full closure, which
`mm2_lane_from_atoms` + one calculus step cannot. Sound for forward-derivation workloads (the closure is the
wanted answer). NB: metagraph rewriting, NOT Datalog. The canonical MM2 alternative (verified working on our
MORK, see test) is the NATIVE main-loop idiom — `DEF` rules + a self-re-adding exec + a halt condition — which
runs the fixpoint INSIDE one `space_metta_calculus!`; this host re-add loop is a pragmatic shortcut for the
additive-closure case (per the MM2_Structuring_Code tutorial: Going-Wide main loop, Control_09 halting).
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

# ── semi-naive (delta-tracked) saturation — the Zippy finite-difference fixpoint ──────────────────
# Zippy README §4: the naive program re-multiplies the whole relation each round; the semi-naive one
# "computes the finite difference … keeping only summands in which at least one input is new". We express
# that at the lane level (kernel untouched): tag the previous round's delta with a `(d …)` wrapper and run
# delta-variant rules that bind one premise to the delta and the rest to the full relation.

# delta-tag a premise/fact by wrapping under head `d`: (reach $y $z) → (d (reach $y $z)).
_mm2_dtag(sexpr::AbstractString)::String = "(d $(strip(sexpr)))"

# DERIVED relations = head symbols some exec TEMPLATE emits (vs BASE relations, which are only matched).
function _mm2_derived_relations(execs)::Set{String}
    derived = Set{String}()
    for e in execs
        a = try mm2_expr_args(e) catch; continue end
        length(a) >= 4 || continue
        for t in (try mm2_expr_args(a[4]) catch; String[] end)   # template list (, T1 T2 …)
            t == "," && continue
            push!(derived, mm2_head(t))
        end
    end
    derived
end

# Semi-naive delta-variants of one exec: for EACH body premise whose head is a DERIVED relation, emit a
# variant with that premise delta-tagged (the others left full). A rule with no derived premise is
# non-recursive (returns empty) — it fires only in the naive seed round.
function _mm2_seminaive_variants(exec::AbstractString, derived::Set{String})::Vector{String}
    a = try mm2_expr_args(exec) catch; return String[] end
    length(a) >= 4 || return String[]
    loc, src, tmpl = a[2], a[3], a[4]
    body = try mm2_expr_args(src) catch; return String[] end
    prems = [p for p in body if p != ","]
    out = String[]
    for i in eachindex(prems)
        mm2_head(prems[i]) in derived || continue
        nb = copy(prems); nb[i] = _mm2_dtag(prems[i])
        push!(out, "(exec $loc (, $(join(nb, " "))) $tmpl)")
    end
    out
end

"""
    mm2_lane_saturate_seminaive!(atoms; max_rounds=256) -> CoreSpace

Semi-naive (delta-tracked) counterpart of [`mm2_lane_saturate!`] — the Zippy finite-difference fixpoint
(README §4: "keep only summands in which at least one input is new"). Produces the SAME forward-rewriting
closure (verified ≡ the naive driver), but on LINEAR-recursive workloads (reach / ancestor / PLN forward
chaining) it avoids re-joining the whole relation each round: round 0 is a naive seed pass, then each round
joins only the previous round's delta against the full relation (the delta premise wrapped `(d …)`),
promoting newly-derived facts to the next delta until the fixpoint. Measured ~4–5× faster than naive on
linear transitive closure (N≤192); for doubling-closure shapes (large deltas) the naive trie-join is
already optimal and the two converge. Opt-in — the naive `mm2_lane_saturate!` stays the default; the MORK
kernel calculus is untouched (this is pure lane-level orchestration).
"""
function mm2_lane_saturate_seminaive!(atoms; max_rounds::Int = 256)::CoreSpace
    cs = new_core_space()
    data, execs = _mm2_classify_atoms(atoms)
    isempty(data) || space_add_all_sexpr!(cs.inner, join(data, "\n"))
    isempty(execs) && return cs
    derived = _mm2_derived_relations(execs)
    variants = String[]
    for e in execs; append!(variants, _mm2_seminaive_variants(e, derived)); end
    isempty(variants) && return mm2_lane_saturate!(atoms; max_rounds = max_rounds)  # no recursion → naive
    # fact set of the space, excluding exec-rule artifacts and `(d …)` delta tags
    factset(s) = Set(x for x in (strip(l) for l in split(space_dump_all_sexpr(s), '\n'))
                     if !isempty(x) && (h = mm2_head(x); h != "exec" && h != "d"))
    before = factset(cs.inner)
    space_add_all_sexpr!(cs.inner, join(execs, "\n"))                 # round 0: naive seed pass
    space_metta_calculus!(cs.inner, 1_000_000)
    full = factset(cs.inner)
    delta = setdiff(full, before)
    vjoined = join(variants, "\n")
    for _ in 1:max_rounds
        isempty(delta) && break
        dtags = join((_mm2_dtag(f) for f in delta), "\n")
        space_add_all_sexpr!(cs.inner, dtags)                        # tag delta (O(|delta|))
        space_add_all_sexpr!(cs.inner, vjoined)                      # re-add consumed delta-variants
        space_metta_calculus!(cs.inner, 1_000_000)                   # join delta × full (accumulates)
        cur = factset(cs.inner)
        newf = setdiff(cur, full)
        union!(full, newf)
        space_remove_all_sexpr!(cs.inner, dtags)                     # untag — keep the trie clean
        delta = newf
    end
    cs
end

"""
    mc_closure!(isp; rounds=64) -> Int

OPT-IN substrate route: compute the FORWARD-REWRITING CLOSURE (MM2 exec calculus = metagraph rewriting, NOT
Datalog) of a live interpreter `Space`'s relational rules on the MORK lane (`mm2_lane_saturate!`) and
MATERIALIZE the newly-derived atoms back into `isp`. Returns the count added. The user opts into the
forward-closure (metagraph-rewriting) semantics for the relational subset; the
interpreter's `(=)` reduction semantics for everything else are untouched. So a MeTTa program can compute a
transitive closure on the substrate, then query it with the interpreter (`!(match &self …)`).
"""
function mc_closure!(isp::Interpreter.Space; rounds::Int = 64)::Int
    own = collect(@view isp.atoms[(isp.lib_count + 1):end])
    cs = mm2_lane_saturate!(own; max_rounds = rounds)
    added = 0
    for line in split(space_dump_all_sexpr(cs.inner), '\n')
        s = strip(line); isempty(s) && continue
        mm2_head(s) == "exec" && continue                        # skip MM2 exec-rule artifacts
        atom = Interpreter.parse_program(s)[1][2]
        if !any(==(atom), isp.atoms)
            Interpreter.add_atom!(isp, atom); added += 1
        end
    end
    added
end

# wire the `(mork-closure)` grounded op: its SpaceOp is defined in Interpreter (so it lives in TOKEN_REGISTRY),
# but its impl is `mc_closure!` here in the parent — populate the hook now that both are loaded.
Interpreter._MORK_CLOSURE_HOOK[] = mc_closure!

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
function mm2_route!(cs::CoreSpace, program::AbstractString; steps::Int = 1_000_000, eq_mode::Symbol = :relational)
    p = mm2_partition(program; eq_mode = eq_mode)
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
