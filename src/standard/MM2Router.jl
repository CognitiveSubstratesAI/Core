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

"""
    mm2_partition(program) -> (; bangs, exec, data)

Partition a MeTTa/MM2 program's top-level forms into the three lanes:
`bangs` (`!`-directives → interpreter), `exec` (`(exec …)` rules → MORK engine), `data` (everything
else → facts/rules in the space).
"""
function mm2_partition(program::AbstractString)
    forms = mm2_split_forms(program)
    bangs = String[f for (b, f) in forms if b]
    rest  = [f for (b, f) in forms if !b]
    exec  = String[f for f in rest if mm2_is_exec_rule(f)]
    data  = String[f for f in rest if !mm2_is_exec_rule(f)]
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
