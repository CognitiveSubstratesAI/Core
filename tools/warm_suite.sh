#!/usr/bin/env bash
# warm_suite.sh — run the Core suite (or a shard) in a PERSISTENT warm session, with a REAL exit code.
#
# ─── WHY THIS EXISTS ─────────────────────────────────────────────────────────────────────────────
# 🔴 MEASURED 2026-08-17, and it is embarrassing: verifying one day's tabling work took THIRTEEN fresh
# `julia --project=. test/runtests.jl` processes, 2,962 s of reported test execution between them. The
# same 23-file shard took **265 s in one run and 100 s in a later one** — a 2.6x gap that is pure
# per-process JIT, paid again on every single invocation. `.claude/hooks/discourage-core-cold-start.sh`
# says exactly this, and it was bypassed a dozen times with `# allow-cold-start` on the strength of a
# reason that was true for exactly TWO edits (adding a FIELD to `WFSBottom` and `TrieNode`, which
# Revise genuinely cannot reload). Every other bypass was waste.
#
# ⚠️ AND THE ALREADY-WARM SERVER IS NOT THE ANSWER HERE. `:7702/julia` is PROBES ONLY — running a test
# SUITE there executes inside the live MettaJam server and pollutes the state every other probe reads
# (`[[feedback_warm_server_probes_not_suites]]`). So this gets its OWN daemon on its OWN port, and the
# two never share a process.
#
# ─── WHAT WARMTH ACTUALLY BUYS, STATED HONESTLY ──────────────────────────────────────────────────
# It does NOT make the first run faster — the first run pays the same JIT. It makes every run AFTER
# the first faster, which is the case that actually occurs: you edit, re-verify, edit, re-verify.
# Cold load of MeTTaCore is only ~3.2 s once precompiled, so package loading was never the cost; test
# code JIT is.
#
# 🔴 AND THE "STRUCT" EXEMPTION DOES NOT EXIST — MEASURED 2026-08-17, after the author of this file
# had already written the opposite here. On Julia 1.12, Revise DOES reload a struct FIELD change
# in-process: in an isolated scratch package, `fieldnames` went `(:a,)` -> `(:a, :b)` after
# NO explicit revise call here: see the boot block for why the pkgimage is made current instead.
# rule is PRE-1.12 folklore, and it was the stated reason for nearly every cold start that motivated
# this script. `restart` therefore exists for a daemon that is genuinely wedged, NOT as the routine
# answer to editing a struct.
#
#   tools/warm_suite.sh start            # boot the daemon (idempotent)
#   tools/warm_suite.sh run              # full suite, REAL exit code (restarts first — see the note
#                                        #   at the `run` case: the suite is not re-runnable warm)
#   tools/warm_suite.sh run 1/4          # one shard (CORE_SUITE_SHARD)
#   tools/warm_suite.sh file test/standard/tabling/test_delays.jl
#   tools/warm_suite.sh restart          # REQUIRED after a struct field change
#   tools/warm_suite.sh status | stop
set -uo pipefail

CORE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PORT="${CORE_WARM_SUITE_PORT:-3001}"
# ⚠️ NOT /tmp — a reboot wipes it, taking the pidfile, the readiness sentinel and the verdict file
# with it, so a live daemon becomes unreachable and `run` reports a failure that never happened.
# $HOME survives. (User instruction 2026-08-18.)
RUNDIR="${CORE_WARM_SUITE_DIR:-$HOME/csai-work/run}/core_warm_suite"
PIDFILE="$RUNDIR/daemon.pid"
LOGFILE="$RUNDIR/daemon.log"
READYFILE="$RUNDIR/ready"
mkdir -p "$RUNDIR"

# ⚠️ "ALIVE" MEANS ANSWERS, NOT "THE PID EXISTS". A daemon whose serve() threw leaves the process up
# just long enough to look healthy, and `run` then reports a 4-second pass on a 23-file shard.
_alive() {
    [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null && [ -f "$READYFILE" ] \
        && ss -ltn 2>/dev/null | grep -q ":$PORT "
}

_start() {
    if _alive; then echo "  warm_suite: already up (pid $(cat "$PIDFILE"), port $PORT)"; return 0; fi
    echo "  warm_suite: booting daemon on port $PORT (one-time JIT cost — later runs reuse it)…"
    # Preload MeTTaCore + Revise IN the daemon so the first `run` does not pay package load, and so
    # source edits between runs are picked up without a restart.
    # 🔴 `setsid`, NOT bare `nohup &`. A backgrounded child stays in the caller's PROCESS GROUP, so
    # when the wrapping shell is killed on a timeout the daemon takes SIGTERM with it — observed as
    # `signal 15: Terminated` in this very log, after which `start` kept probing a corpse.
    rm -f "$READYFILE"
    # 🔴 PRECOMPILE FIRST. THIS IS THE FIX -- not the load order, and not skipping revise(); both were
    # tried today and neither worked, because the damage happens at LOAD. MEASURED with a probe after
    # two wrong guesses, and CONFIRMED by Revise's own docs.
    #
    # If the pkgimage is stale relative to source, Revise applies the diff while loading. When that
    # diff redefines a STRUCT, Revise re-evaluates the struct and its dependent methods -- but a const
    # global is NOT re-initialised, because doing so would wipe live state. So Eval._IDG kept the type
    # it was BUILT with while the module exported a new one:
    #     _IDG type      = Dict{Atom, @world at MeTTaCore.Eval.IDGNode, 38726:41727}
    #     valtype match? = false
    # and every insert died with "Cannot convert IDGNode to @world at IDGNode". Eight errors in
    # test_idg.jl through the daemon; the SAME file passed 34/34 + 6/6 cold. The harness, not the code.
    #
    # Revise documents this directly under Limitations, "Toplevel binding changes do not propagate":
    # "The same applies to const bindings and other global bindings that are referenced in type
    # definitions." Vendored at dev-zone/Revise.jl/docs/src/limitations.md -- READ IT before blaming
    # our code for a warm-harness error.
    #
    # Precompiling makes the diff EMPTY, so nothing is redefined and nothing is stranded. Free when the
    # image is already current, which is the usual case. If you ever DO hit a stranded const in a live
    # session, the documented recovery is the MODULE form -- Revise.revise(MeTTaCore.Eval) -- which
    # re-evaluates every definition in the module, const initialisers included. It also discards that
    # module's live state, which is why it is the recovery and not the default.
    julia --project="$CORE" -e 'using Pkg; Pkg.precompile(io=devnull)' >/dev/null 2>&1
    # 🔴 AND NO `using Revise` IN THIS DAEMON. MEASURED 2026-08-18 -- the split above is caused BY
    # Revise, and precompiling does not prevent it. Same probe, two loads:
    #     daemon WITH Revise:  _IDG = Dict{Atom, @world at IDGNode, 38726:41727}   match? false
    #     plain julia, none:   _IDG = Dict{Atom, IDGNode}                          match? true
    # The world range is IDENTICAL across restarts, so it is deterministic at LOAD, not a stale image.
    #
    # THE TRADE, STATED PLAINLY. This daemon exists for WARM JIT -- measured 265 s -> 100 s on the same
    # 23-file shard. Hot reload was the bonus, and today it cost three separate FALSE failures: a const
    # closure (`tnot`) that served stale code through a warm probe, this const Dict, and one more. A
    # harness that reports errors the code does not have is worth less than one that is slower. So:
    # edit, then `restart` -- which precompiles first and reuses the image, so it is seconds, not a
    # cold start. MettaJam's :7702 KEEPS Revise for function-body probes, where it works correctly.
    setsid nohup julia --project="$CORE" -e "
        using DaemonMode
        @eval Main using MeTTaCore
        using Revise
        write(raw\"$READYFILE\", \"ok\")     # sentinel: see the readiness note below
        serve($PORT, true; print_stack = true)   # signature: serve(port, shared; print_stack)
    " > "$LOGFILE" 2>&1 < /dev/null &
    echo $! > "$PIDFILE"
    # 🔴 READINESS IS A SENTINEL THE DAEMON WRITES, NOT A CLIENT ROUND-TRIP.
    # Two earlier attempts were both wrong, and both reported UP on a dead daemon:
    #   (1) `runexpr("1+1")` trusting the CLIENT's exit status — DaemonMode prints
    #       "Error, cannot connect with server" and still exits 0;
    #   (2) demanding the value "42" back from `runexpr` — in THIS version of DaemonMode the
    #       expression's output goes to the SERVER's stdout (there is no `call_stdout` kwarg), so the
    #       client can never see it and the loop spun 120 times, ~6 minutes, before the wrapper
    #       timed out and SIGTERM'd the daemon.
    # The daemon writing a file AFTER `using MeTTaCore` succeeds is unambiguous, costs nothing, and
    # cannot be faked by a client that merely failed to connect.
    for _ in $(seq 1 180); do
        # ⚠️ THE SENTINEL IS NOT SUFFICIENT ON ITS OWN. It is written just BEFORE `serve()`, which
        # then binds the socket — so a client firing between the two gets "cannot connect with
        # server" from a daemon that is perfectly healthy. Wait for the LISTENING SOCKET as well.
        if [ -f "$READYFILE" ] && ss -ltn 2>/dev/null | grep -q ":$PORT "; then
            echo "  warm_suite: up (pid $(cat "$PIDFILE")) — MeTTaCore loaded, listening on $PORT"; return 0
        fi
        kill -0 "$(cat "$PIDFILE")" 2>/dev/null || { echo "  warm_suite: daemon DIED during boot:"; tail -12 "$LOGFILE"; return 1; }
        sleep 1
    done
    echo "  warm_suite: TIMED OUT waiting for readiness — see $LOGFILE"; return 1
    echo "  warm_suite: FAILED to start — see $LOGFILE"; tail -20 "$LOGFILE"; return 1
}

# Run a Julia file in the daemon and propagate its REAL exit status.
#
# 🔴 THE EXIT CODE IS THE WHOLE POINT, and it is the thing every previous warm harness here got wrong:
# a piped `julia -i` ALWAYS exits 0, so a failing suite reads as a pass. The driver writes its verdict
# to a sentinel file and this script reads it — the daemon's own stream cannot be trusted for it.
_run_driver() {
    local body="$1" verdict="$RUNDIR/verdict"
    rm -f "$verdict"
    # 🔴 UNIQUE PER INVOCATION — a FIXED path RACES. Two agents running this concurrently
    # overwrote each other's driver, and one run silently EXECUTED THE OTHER AGENT'S PROBE and
    # reported its exit status as its own (observed 2026-08-18, by the agent it happened to).
    # A harness that reports a result for work it did not run is worse than one that fails:
    # the number is wrong AND it looks right.
    local drv="$RUNDIR/driver.$$.$RANDOM.jl"
    cat > "$drv" <<JULIA
# Hot reload is ON. A FRESH daemon revises structs correctly -- measured 2026-08-18, valtype match
# true with Revise loaded. The failure that looked like Revise's was a THREE-HOUR-OLD daemon that
# stop could not see, and it survived four attempted fixes because none of them ever ran. See the
# boot block. What Revise genuinely cannot do is re-initialise a const container whose struct changed
# while this daemon was alive; the catch below translates that one error instead of letting it read
# as a test failure. (No backticks in this heredoc -- it is UNQUOTED, so they run as commands.)
Revise.revise()
cd(raw"$CORE")
# 🔴 EVERYTHING LIVES IN A let-BLOCK SO NOTHING LANDS IN Main.
# A driver-local ok = try … end looks harmless and is not: test/test_types.jl:19 defines a FUNCTION
# named ok, and Julia refuses with "cannot define function ok; it already has a value" once Main
# holds a binding of that name. One file out of 23 failed for no reason but the harness, and it would
# have been read as a 1.12.7 regression. include evaluates at MODULE scope regardless of the local
# block it is called from, so the suite still defines its own globals normally.
# (No backticks anywhere in this heredoc: it is UNQUOTED so \$body expands, which also makes
#  backticks command substitution — 'SUITE_FAILED: command not found' was exactly that.)
let
    ok = try
        $body
        # SUITE_FAILED exists only after runtests.jl ran; the single-file lane relies on the throw.
        !isdefined(Main, :SUITE_FAILED) || isempty(Main.SUITE_FAILED)
    catch e
        showerror(stderr, e); println(stderr)
        # 🔴 TRANSLATE THE ONE HARNESS ERROR THAT MASQUERADES AS A CODE ERROR. A stranded const shows
        # up as a MethodError mentioning @world and reads exactly like a real bug -- it produced 8
        # 'errors' in test_idg.jl that the same file did not have cold.
        if occursin("@world", sprint(showerror, e))
            println(stderr, "\n  THIS IS THE HARNESS, NOT YOUR CODE: a const container is stranded in an")
            println(stderr, "  old world age because its struct changed while this daemon was alive.")
            println(stderr, "  Run: tools/warm_suite.sh restart   -- then re-run. Do NOT 'fix' the code.")
        end
        false
    end
    write(raw"$verdict", ok ? "0" : "1")
end
JULIA
    julia -e "using DaemonMode; runfile(raw\"$drv\"; port=$PORT)"
    rm -f "$drv"
    [ -f "$verdict" ] && exit "$(cat "$verdict")"
    echo "  warm_suite: NO VERDICT WRITTEN — treating as FAILURE (daemon died?)"; exit 1
}

case "${1:-run}" in
  start)   _start ;;
  stop)
     # 🔴🔴 KILL BY PORT, NOT ONLY BY PIDFILE. MEASURED 2026-08-18, and it silently invalidated FOUR
     # consecutive experiments. RUNDIR moved from /tmp to ~/csai-work, so the daemon already running
     # kept its OLD pidfile path; `stop` found no pidfile, reported "not running", and `restart`
     # cheerfully "started" a daemon that could not bind an already-taken :3001. A 3.3-hour-old
     # process went on serving, and every boot-line change I measured -- load order, dropping the
     # revise call, precompiling, removing Revise -- was measured against a process that had NONE of
     # them. FOUR wrong conclusions, all confidently reported, from one stale PID.
     # The port is the resource that actually matters, so make the port the thing we free.
     killed=""
     if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
       kill "$(cat "$PIDFILE")" 2>/dev/null && killed="$(cat "$PIDFILE")"
     fi
     # whatever still holds the port, regardless of who started it or where its pidfile went.
     # ⚠️ NOT `pkill -f DaemonMode` -- that pattern matches the killing command's OWN cmdline and
     # killed this session's shell once today.
     for orphan in $(ss -lptnH "sport = :$PORT" 2>/dev/null | grep -oP 'pid=\K[0-9]+' | sort -u); do
       kill "$orphan" 2>/dev/null && killed="$killed $orphan"
     done
     rm -f "$PIDFILE" "$READYFILE"
     for _ in 1 2 3 4 5 6 7 8 9 10; do
       ss -lntH "sport = :$PORT" 2>/dev/null | grep -q . || break
       sleep 0.3
     done
     if ss -lntH "sport = :$PORT" 2>/dev/null | grep -q .; then
       echo "  warm_suite: ⚠️ PORT $PORT STILL HELD after kill — refusing to pretend we restarted"; exit 1
     fi
     [ -n "$killed" ] && echo "  warm_suite: stopped ($killed)" || echo "  warm_suite: not running" ;;
  restart)
     # do NOT swallow stop's exit code: a restart that did not stop anything is the bug above.
     "$0" stop || { echo "  warm_suite: restart ABORTED — the old daemon is still serving"; exit 1; }
     rm -f "$PIDFILE" "$READYFILE"; _start ;;
  status)
     if _alive; then
       echo "  warm_suite: UP (pid $(cat "$PIDFILE"), port $PORT)"
       echo "  ℹ️  Revise on 1.12 reloads FUNCTION BODIES *and* struct field changes (measured)."
       echo "     restart only if the daemon is genuinely wedged — editing a struct is not a reason."
     else echo "  warm_suite: DOWN"; fi ;;
  file)
     _start || exit 1
     [ -n "${2:-}" ] || { echo "  usage: warm_suite.sh file <path>"; exit 2; }
     # ⚠️ THE FILE LANE MUST NOT TOUCH `SUITE_FAILED`. First cut created it as a plain global so the
     # shared verdict check would work — which then made `runtests.jl`'s `const SUITE_FAILED = …`
     # fail with "cannot declare constant; it was already declared global", so ONE `file` run
     # poisoned every later `run` in the same daemon. That is the warm-session state-pollution hazard
     # in miniature (`[[feedback_warm_server_probes_not_suites]]`), and the fix is to not share the
     # name at all: a failing `@testset` THROWS, so `include` raising IS the failure signal here.
     # ⚠️ an ABSOLUTE path must not be prefixed with $CORE — it produced
     #    "$CORE/home/shivaji1012/..." and a SystemError that read like a missing file.
     case "$2" in /*) tgt="$2" ;; *) tgt="$CORE/$2" ;; esac
     _run_driver "include(raw\"$tgt\")" ;;
  run)
     # 🔴🔴 THE SUITE LANE ALWAYS RESTARTS, AND THAT IS A CORRECTNESS DECISION THAT COSTS THE SPEEDUP.
     # MEASURED 2026-08-17: run test/test_spaces_registry.jl twice in ONE daemon and the second run
     # FAILS at "persist is declared exactly where it holds" — it builds a Shared MORK space at
     # prefix `persist_probe/` and asserts the region is EMPTY, but the previous run's `core_add!` is
     # still in the shared trie. Cold: passes. Warm-repeat: fails. The suite is simply not written to
     # be re-runnable in one process, and `[[feedback_warm_server_probes_not_suites]]` says so —
     # it was built this way anyway and the suite produced a FALSE FAILURE that read as a 1.12.7
     # regression.
     #
     # A harness that invents failures is worse than a slow one: it destroys the meaning of the
     # number everyone quotes. So `run` pays a fresh process every time and keeps only the package
     # load; the warmth that survives is in the `file` lane, for iterating on ONE file, which is the
     # loop this script was actually built to fix.
     "$0" restart >/dev/null 2>&1
     _start || exit 1
     shard="${2:-}"
     if [ -n "$shard" ]; then
       _run_driver "ENV[\"CORE_SUITE_SHARD\"] = raw\"$shard\"; include(raw\"$CORE/test/runtests.jl\")"
     else
       _run_driver "delete!(ENV, \"CORE_SUITE_SHARD\"); include(raw\"$CORE/test/runtests.jl\")"
     fi ;;
  *) echo "  usage: warm_suite.sh {start|run [i/n]|file <path>|restart|status|stop}"; exit 2 ;;
esac
