"""
CoreSpaceLoad — load MeTTa source (and the `lib/` algorithm modules) into a `CoreSpace`, i.e. into
the **shared MORK byte trie**.

## Why this exists

Before this file, `load_metta!` had exactly ONE method, on the interpreter's `Space` — a pure-Julia
`Vector{Atom}` store. So every algorithm library (`lib/ecan`, `lib/pln`, `lib/MOSES`, `lib/metamo`,
`lib/subrep`, …) could only ever live in that store, and NONE of them reached MORK. Meanwhile
`CoreSpace` — the MORK-backed space that implements the shared-trie model (one trie, disjoint byte
prefixes) — could ingest atoms (`core_add!`) and run programs (`mc_run`) but could not load a
library at all.

The result was two spaces where the algorithms were in the one WITHOUT the sharing, persistence
and cross-package visibility. This closes that specific gap: **library atoms can now live in the
shared trie.**

## What this does NOT do

It does not move EXECUTION onto MORK. The fast lane serves a restricted subset (all rules lowered,
one clause per head, acyclic, no nested rule-head calls); PLN and MOSES are multi-clause and
recursive, so evaluating them still goes through the interpreter. This is STORAGE unification, and
claiming more of it would be wrong.

## Why it is small

Measured across all seven libraries before writing any of it:

    lib         (= rules   ! directives   import!   bind!   &self
    metamo         100          8           12        0      23
    ecan           115          8            8        0      83
    MOSES          258         32           33        0      33
    subrep          58          0            0        0      10
    pln            266          5            9        0     158
    quantale        31          0            0        0       0
    hyperseed       13          1            0        0      15

**Zero `bind!` anywhere**, so no parse-time token table is needed — `&self` is the only token, and
it is resolved structurally here. And of every `!` directive in the whole tree, exactly ONE is not
an `import!`:

    ecan: !(remove-atom &self (= (attention-evolution-step!) EvolutionStubUnloaded))

So the loader needs: recursive `import!`, a single `remove-atom`, and bulk ingest of everything
else. Anything else raises rather than being silently dropped.

MORK's s-expression reader already strips `;` comments (verified), so non-directive text is handed
through verbatim rather than being re-serialised — no fidelity is lost in a parse/print round trip.
"""

# ── top-level form splitting ─────────────────────────────────────────────────────────────────
#
# Paren-depth scan that is aware of `;` line comments and "..." strings, so a `;` inside a string
# and a `(` inside a comment cannot desynchronise the split. Returns the source text of each
# top-level form, with a leading `!` kept so directives stay identifiable.

function _cs_split_top_level(text::AbstractString)::Vector{String}
    forms = String[]
    buf = IOBuffer()
    depth = 0
    in_str = false
    in_comment = false
    started = false          # have we seen any non-space char of the current form?
    esc = false
    for ch in text
        if in_comment
            if ch == '\n'
                in_comment = false
                # a comment cannot end a form; only depth 0 + whitespace does that
                started && depth == 0 && (push!(forms, strip(String(take!(buf)))); started = false)
            end
            continue
        end
        if in_str
            write(buf, ch)
            if esc
                esc = false
            elseif ch == '\\'
                esc = true
            elseif ch == '"'
                in_str = false
            end
            continue
        end
        if ch == ';'
            in_comment = true
            continue
        end
        if ch == '"'
            in_str = true
            started = true
            write(buf, ch)
            continue
        end
        if isspace(ch)
            if started && depth == 0
                push!(forms, strip(String(take!(buf))))
                started = false
            elseif started
                write(buf, ch)
            end
            continue
        end
        started = true
        ch == '(' && (depth += 1)
        ch == ')' && (depth -= 1)
        write(buf, ch)
        # a form closing back to depth 0 ends it immediately
        if depth == 0 && ch == ')'
            push!(forms, strip(String(take!(buf))))
            started = false
        end
    end
    started && push!(forms, strip(String(take!(buf))))
    filter!(!isempty, forms)
    forms
end

# ── directive helpers ────────────────────────────────────────────────────────────────────────

"Strip a leading `!` (and any space after it); return (is_directive, body_text)."
function _cs_split_bang(form::AbstractString)
    s = strip(form)
    startswith(s, "!") ? (true, strip(s[nextind(s, 1):end])) : (false, String(s))
end

"""
    _cs_resolve_module(name) -> path or nothing

Resolve an `import!` target against `Interpreter._MODULE_PATH` — the SAME search path the
old loader uses, so `(library metamo)`, `"config.metta"` and bare `metamo` resolve identically in
both spaces. Deliberately reuses that Ref rather than duplicating the path list, so the two loaders
cannot drift apart.

⚠️ `Interpreter` is a SELF-CONTAINED submodule that deliberately "shares no types with the
MORK-backed engine". Reaching in for `_MODULE_PATH` respects that boundary — it is a
`Vector{String}` of directories, not a type — and the alternative (a second module path here) is
exactly the drift the boundary is meant to prevent.
"""
function _cs_resolve_module(name::AbstractString)
    n = strip(String(name), ['"', '\''])
    cands = endswith(n, ".metta") ? [n] : [n * ".metta", joinpath(n, n * ".metta")]
    for dir in Interpreter._MODULE_PATH[], c in cands
        p = joinpath(dir, c)
        isfile(p) && return p
    end
    isfile(n) ? n : nothing
end

"Pull the module name out of `(import! &self (library metamo))` / `(import! &self \"config.metta\")`."
function _cs_import_target(body::AbstractString)
    inner = strip(body)
    startswith(inner, "(") && (inner = inner[nextind(inner, 1):prevind(inner, lastindex(inner))])
    toks = _cs_split_top_level(inner)
    length(toks) < 3 && return nothing
    tgt = toks[3]
    if startswith(tgt, "(")
        parts = _cs_split_top_level(tgt[nextind(tgt, 1):prevind(tgt, lastindex(tgt))])
        return isempty(parts) ? nothing : parts[end]      # `(library metamo)` -> metamo
    end
    tgt
end

# ── the loader ───────────────────────────────────────────────────────────────────────────────

"""
    load_metta!(cs::CoreSpace, text; as_library=false, imported=Set{String}()) -> CoreSpace

Load MeTTa source into the **shared MORK trie** behind `cs`.

Mirrors `load_metta!(::Space, …)` for the constructs the algorithm libraries actually use:

* non-directive forms  → `core_add!` (so a prefixed space stores under its own byte region)
* `!(import! …)`       → resolved on `_MODULE_PATH` and loaded RECURSIVELY, with the module's own
                         directory pushed for the duration so its relative imports resolve —
                         same discipline as `_load_module_file!`
* `!(remove-atom …)`   → `core_remove!`
* any other directive  → **raises**. Silently skipping a directive would load a library that only
                         LOOKS complete, which is the failure mode this whole exercise exists to
                         eliminate.

`imported` guards against import cycles (the old loader uses `space.imported` for this; `CoreSpace`
has no such field, so the set is threaded explicitly).

⚠️ `as_library` is ACCEPTED BUT NOT YET HONOURED. In the interpreter's space it sets `lib_count`,
which hides library atoms from `get-atoms`. `CoreSpace` has no equivalent, and faking one would be
worse than not having it: the honest fix is a distinct byte PREFIX for library content (which is
exactly what the shared-trie model is for), and that is a deliberate design step, not a flag. Until
then `core_atoms` on a library-loaded space returns library atoms too — documented rather than
hidden.
"""
function load_metta!(cs::CoreSpace, text::AbstractString;
                     as_library::Bool = false, imported::Set{String} = Set{String}())
    as_library  # accepted for signature parity; see the docstring — deliberately not honoured yet
    pending = String[]
    flush!() = begin
        isempty(pending) || core_add!(cs, join(pending, "\n"))
        empty!(pending)
    end
    for form in _cs_split_top_level(text)
        is_dir, body = _cs_split_bang(form)
        if !is_dir
            push!(pending, body)
            continue
        end
        flush!()                                  # keep directive ordering vs surrounding atoms
        head = first(_cs_split_top_level(startswith(body, "(") ?
                     body[nextind(body, 1):prevind(body, lastindex(body))] : body), 1)
        h = isempty(head) ? "" : head[1]
        if h == "import!"
            tgt = _cs_import_target(body)
            tgt === nothing && error("load_metta!(CoreSpace): cannot parse import target in `$form`")
            path = _cs_resolve_module(tgt)
            path === nothing && error("load_metta!(CoreSpace): module `$tgt` not found on Interpreter._MODULE_PATH")
            rp = realpath(path)
            if !(rp in imported)                  # cycle / re-import guard
                push!(imported, rp)
                d = dirname(rp)
                pushed = !(d in Interpreter._MODULE_PATH[])
                pushed && push!(Interpreter._MODULE_PATH[], d)
                try
                    load_metta!(cs, read(rp, String); as_library = true, imported = imported)
                finally
                    pushed && filter!(!=(d), Interpreter._MODULE_PATH[])
                end
            end
        elseif h == "remove-atom"
            parts = _cs_split_top_level(body[nextind(body, 1):prevind(body, lastindex(body))])
            length(parts) >= 3 || error("load_metta!(CoreSpace): malformed remove-atom in `$form`")
            core_remove!(cs, parts[3])
        else
            error("load_metta!(CoreSpace): directive `$h` is not supported on a MORK-backed space " *
                  "(form: `$form`). Only import! and remove-atom appear in lib/; add explicit " *
                  "support rather than letting it be skipped.")
        end
    end
    flush!()
    cs
end

"""
    load_core_lib!(cs::CoreSpace, name) -> CoreSpace

Load one of the `lib/` algorithm modules into the shared trie, e.g. `load_core_lib!(cs, :ecan)`.
"""
function load_core_lib!(cs::CoreSpace, name::Union{Symbol, AbstractString})
    n = String(name)
    imported = Set{String}()
    path = _cs_resolve_module(n)

    # A library is EITHER a single entry module (`quantale/quantale.metta`, `ecan/ecan.metta`) OR a
    # bare directory of modules with no entry point (`subrep/`, `hyperseed/` have no `<name>.metta`).
    # Both shapes exist in lib/, so handle both rather than assuming the entry-file convention holds.
    files = if path !== nothing
        [path]
    else
        dir = nothing
        for d in Interpreter._MODULE_PATH[]
            cand = joinpath(d, n)
            isdir(cand) && (dir = cand; break)
        end
        dir === nothing && error("load_core_lib!: library `$n` is neither a module on " *
                                 "Interpreter._MODULE_PATH nor a directory on it")
        sort(filter(f -> endswith(f, ".metta"), readdir(dir; join = true)))
    end

    for f in files
        rp = realpath(f)
        rp in imported && continue
        push!(imported, rp)
        # Push the module's OWN directory for the duration, exactly as `_load_module_file!` does, so
        # its relative imports (`!(import! &self "config.metta")`) resolve self-contained. Without
        # this every multi-file library fails on its first nested import.
        d = dirname(rp)
        pushed = !(d in Interpreter._MODULE_PATH[])
        pushed && push!(Interpreter._MODULE_PATH[], d)
        try
            load_metta!(cs, read(rp, String); as_library = true, imported = imported)
        finally
            pushed && filter!(!=(d), Interpreter._MODULE_PATH[])
        end
    end
    cs
end

export load_core_lib!
