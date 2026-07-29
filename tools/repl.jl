#!/usr/bin/env julia
# tools/repl.jl — warm dev REPL + interactive MeTTa shell for MeTTaCore, on the MeTTaCore.Interpreter
# engine (the 234/234 hyperon-faithful evaluator + CoreExtensions). Replaces PRIMUS tools/metta_repl.jl.
#
# Architecture mirrors hyperon-experimental's repl/ crate (verified against upstream main.rs /
# metta_shim.rs / interactive_helper.rs / config_params.rs):
#   * a thin read -> exec -> print loop; NO `:command` surface — everything is MeTTa (load = !(import!),
#     help = !(help!)); config lives as `&Repl*` MeTTa state atoms (builtin_init below, like
#     builtin_init_metta_code()); multiline = "ask the parser" (try-parse, continue if incomplete).
#   * `Shim` is the single boundary between the loop and the evaluator (exec / print_result / parse_ok).
#
# Interactive:  julia --project=. -i tools/repl.jl   then  metta()   (enters the `> ` loop; Ctrl-D exits)
# Scripted   :  printf 'q("!(+ 1 2)")\n'                  | julia --project=. -i tools/repl.jl
#               printf 'lib!("metamo"); q("!(expNum 0.0)")\n' | julia --project=. -i tools/repl.jl
#
# Dev/test helpers (Julia API — distinct from the REPL loop, like hyperon's Rust test setup):
#   ml("!(...)")  — exec ONE MeTTa line against the persistent space (prints, hyperon exec+print_result)
#   q("!(...)")   — exec and RETURN results as Julia values (numbers/Symbols/Vectors) for tests
#   mscript(str)  — exec a multi-line MeTTa script
#   lib!("name")  — load lib/<name>/ into the persistent space (test/dev setup)
#   sm("!(...)")  — exec in a FRESH stdlib space (stateless one-shot)
#   tstd()        — StandardMeTTa testsets        t()  — full suite
#
# NOTE (Revise): function-body edits in src/ hot-reload; editing a STRUCT's fields needs a fresh session.

try; using Revise; catch; @warn "Revise unavailable — install into the global env for hot-reload"; end

using MeTTaCore
using Test

const SM = MeTTaCore.Interpreter                       # metta_run / load_metta! / Space / parse
const SA = MeTTaCore.StandardMeTTa         # Sym / Var / Expression / Bindings / match_atoms

const _ROOT   = dirname(@__DIR__)
const _STDLIB = joinpath(_ROOT, "src", "standard", "stdlib.metta")
const _LIBDIR = joinpath(_ROOT, "lib")

# Config as MeTTa state atoms — mirrors hyperon builtin_init_metta_code() (config_params.rs). A
# repl.default.metta can `change-state!` these. Read back via get-state in the loop.
const _REPL_INIT = """
!(bind! &ReplPrompt (new-state "> "))
!(bind! &ReplHistoryMaxLen (new-state 500))
"""

# ── the persistent space + Shim boundary (the only place the loop touches the evaluator) ─────────────
function _fresh_space()
    sp = SM.Space()
    SM.load_core_stdlib!(sp)             # stdlib.metta + CoreExtensions.metta (library, hidden from get-atoms)
    SM.load_metta!(sp, _REPL_INIT)       # &Repl* config atoms
    sp
end
const _SPACE = Ref(_fresh_space())

# Atom -> Julia value (readable results / test comparison). True/False -> :True/:False (test idiom).
mval(a) = a isa SM.Grounded   ? a.value :
          a isa SM.Sym        ? Symbol(a.name) :
          a isa SM.Expression ? Any[mval(c) for c in a.children] : a

# Shim.exec + print_result: run a chunk of MeTTa, print each result (hyperon exec/print_result).
function ml(src::AbstractString)
    try
        rs = SM.load_metta!(_SPACE[], src)
        isempty(rs) || foreach(r -> println("  ", r), rs)
    catch e
        println("  ERROR: ", sprint(showerror, e))
    end
    return nothing
end

# Shim.exec returning Julia values (for tests / programmatic use); never prints.
q(src::AbstractString) = Any[mval(x) for x in SM.load_metta!(_SPACE[], src)]

mscript(src::AbstractString) = (ml(src); nothing)   # load_metta! already handles many lines

# Shim.parse_ok: does `src` parse to a COMPLETE expression? (hyperon parse_line — drives multiline.)
function _parse_ok(src::AbstractString)
    try
        SM.parse_program(src); return true
    catch
        return false
    end
end

# ── dev/test setup: load a library into the persistent space (NOT a REPL command) ────────────────────
# Mirrors how the legacy test harness sets up, but on Minimal. Follows the lib's loader order if present.
function lib!(name::AbstractString)
    dir = joinpath(_LIBDIR, name)
    isdir(dir) || (println("  no library dir: ", dir); return nothing)
    SM._MODULE_PATH[] = [dir]
    loader = joinpath(dir, name * ".metta")
    files = String[]
    if isfile(loader)
        for m in eachmatch(r"import!\s+&self\s+\"([^\"]+\.metta)\"", read(loader, String))
            push!(files, m.captures[1])
        end
    end
    isempty(files) && (files = filter(f -> endswith(f, ".metta") && f != name * ".metta", readdir(dir)))
    isempty(files) && (files = filter(f -> endswith(f, ".metta"), readdir(dir)))
    n0 = length(_SPACE[].atoms); loaded = 0
    for f in files
        path = isabspath(f) ? f : joinpath(dir, f)
        try SM.load_metta!(_SPACE[], read(path, String)); loaded += 1
        catch e; println("  ✗ ", f, ": ", first(sprint(showerror, e), 140)); end
    end
    println("  lib!(\"", name, "\") -> +", length(_SPACE[].atoms) - n0, " atoms (", loaded, "/", length(files), " files)")
    return nothing
end

reset!() = (_SPACE[] = _fresh_space(); println("  space reset (stdlib + config reloaded)"); nothing)

"Exec StandardMeTTa `src` in a FRESH stdlib space (stateless); return raw result atoms."
function sm(src::AbstractString)
    sp = SM.Space(); SM.load_core_stdlib!(sp); SM.load_metta!(sp, src)
end

"Run ONLY the StandardMeTTa testsets (fast warm iteration)."
tstd() = for f in ("test_atoms","test_minimal","test_interpreter","test_stdlib","test_conformance")
    include(joinpath(_ROOT, "test", "standard", f * ".jl"))
end
"Run the full MeTTaCore test suite."
t() = include(joinpath(_ROOT, "test", "runtests.jl"))

# ── the faithful interactive loop (hyperon main.rs:147-170) ──────────────────────────────────────────
# Thin: read (multiline via _parse_ok) -> exec -> print. Prompt from &ReplPrompt. No commands. Ctrl-D
# exits back to the Julia REPL. (Line-editing/history is the deferred layer — see module docstring.)
function _prompt()
    try
        r = SM.load_metta!(_SPACE[], "!(get-state &ReplPrompt)")
        (!isempty(r) && r[1] isa SM.Grounded && r[1].value isa AbstractString) ? r[1].value : "> "
    catch; "> "; end
end

function metta()
    println("MeTTa REPL (MeTTaCore.Interpreter). Ctrl-D to exit. Loading = !(import! …), help = !(help!).")
    buf = IOBuffer()
    while true
        print(position(buf) == 0 ? _prompt() : "  ")
        line = readline(stdin; keep=false)
        # readline returns "" on EOF (eof(stdin)); distinguish real empty line from EOF
        if eof(stdin) && isempty(line)
            println(); break
        end
        print(buf, line, '\n')
        src = String(take!(copy(buf)))
        if _parse_ok(src) || isempty(strip(line))   # complete, or blank line forces submit
            strip(src) |> s -> isempty(s) || ml(s)
            take!(buf)                                # clear
        end
    end
    return nothing
end

if isinteractive()
    println("MeTTaCore REPL — Minimal engine, Revise tracking src/.  (SM / SA namespaces)")
    println("  metta()        — enter the interactive MeTTa `> ` loop (Ctrl-D exits)")
    println("  ml(\"!(...)\")  q(\"!(...)\")→values  mscript(...)  lib!(\"metamo\")  sm(\"...\")  tstd()  t()")
end
