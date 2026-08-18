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
# 🔴 THE "STRUCT" RULE, RECONCILED — and both halves are measured, which is why it reads oddly.
# On Julia 1.12 Revise DOES reload a struct FIELD change in-process: in an isolated scratch package
# `fieldnames` went (:a,) -> (:a, :b) after `Revise.revise()` and the new constructor worked, same
# session (2026-08-17). "Revise can't reload structs" is pre-1.12 folklore, and it was the stated
# reason for nearly every cold start this script was built to eliminate.
# BUT (2026-08-18) redefining the struct does NOT re-initialise a `const` container typed on it —
# that would wipe live state — so the container is stranded in the old world age and every insert
# dies with "Cannot convert IDGNode to @world(IDGNode, ...)". Revise names the mechanism in an OPEN
# issue, #1116: "revise() runs in a frozen world, and on 1.12 globals are world-partitioned".
# SO: edit a struct freely; RESTART if anything holds it in a const container. The driver detects
# that specific error and says so, rather than letting it read as a test failure.
#
#   tools/warm_suite.sh start            # boot the daemon (idempotent)
#   tools/warm_suite.sh run              # full suite, REAL exit code — WARM: 147 s vs 466 s cold
#   tools/warm_suite.sh run 1/4          # one shard (CORE_SUITE_SHARD)
#   tools/warm_suite.sh run-cold         # the old always-restart behaviour; the arbiter when a
#                                        #   `run` failure looks implausible
#   tools/warm_suite.sh run-warm         # diagnostic: a second pass in the SAME process, to find
#                                        #   state a file leaks into the next one
#   tools/warm_suite.sh file test/standard/tabling/test_delays.jl
#   tools/warm_suite.sh restart          # after a struct change that a const container holds
#   tools/warm_suite.sh status | stop
set -uo pipefail

CORE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# 🔴🔴 TWO DAEMONS, AND THE SPLIT IS THE WHOLE POINT — 2026-08-18.
# `file` is for PROBES; `run` is the GATE. They must not share a process, and the day they did it
# cost 26 minutes of confusion. MEASURED, same suite, 92 files / 0 failed every time:
#     cold, fresh daemon .................. 575 s
#     warm, nothing run since ............. 161 s
#     warm, after ~15 diagnostic probes ... 26 min and still going when killed
# The probes were ordinary debugging — tabling traces, an instrumented build, a couple of one-off
# spaces — and each left tables, spaces and IDG nodes behind. While `run` restarted unconditionally it
# was immune; making it warm for the 3.5x speedup handed it every probe's residue.
# `[[feedback_warm_server_probes_not_suites]]` said this about MettaJam's :7702 and it is the same
# hazard one level down: the answer is not "remember to restart", it is SEPARATE PORTS.
PORT="${CORE_WARM_SUITE_PORT:-3001}"          # probe lane   (`file`)
SUITE_PORT="${CORE_WARM_SUITE_GATE_PORT:-3002}"  # gate lane (`run`, `run-warm`, `run-cold`)
# ⚠️ NOT /tmp — a reboot wipes it, taking the pidfile, the readiness sentinel and the verdict file
# with it, so a live daemon becomes unreachable and `run` reports a failure that never happened.
# $HOME survives. (User instruction 2026-08-18.)
RUNROOT="${CORE_WARM_SUITE_DIR:-$HOME/csai-work/run}"

# Point every path at one lane. Called by the run* verbs to switch to the gate daemon; everything
# else stays on the probe lane. Keeping the paths PORT-SUFFIXED is what stops the two lanes from
# reading each other's pidfile — the class of bug that let a 3.3 h daemon survive `stop` this morning.
_use_lane() {
    PORT="$1"
    RUNDIR="$RUNROOT/core_warm_suite_$1"
    PIDFILE="$RUNDIR/daemon.pid"
    LOGFILE="$RUNDIR/daemon.log"
    READYFILE="$RUNDIR/ready"
    mkdir -p "$RUNDIR"
}
_use_lane "$PORT"
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
    # 🔴🔴 TWO RULES ABOUT THIS BOOT, BOTH LEARNED THE EXPENSIVE WAY ON 2026-08-18.
    #
    # (1) `using Revise` COMES FIRST, BEFORE THE PACKAGE. Revise tracks what is loaded after it.
    # I reordered it the other way earlier today -- for a cause that turned out to be wrong -- and then
    # measured the "fix" against a daemon that had never actually restarted, so I never saw that the
    # reorder SILENTLY DISABLES HOT RELOAD. It surfaced only when a probe asked "is the new function
    # even defined?" and got false, while a benchmark reported perfectly stable numbers for code that
    # had not changed. A harness that does not reload is worse than none: every measurement is of the
    # previous build and looks convincing.
    # ⚠️ IF YOU TOUCH THIS ORDER, VERIFY WITH A NEW SYMBOL (isdefined), NEVER WITH A TIMING.
    # ⚠️ AND ORDER MAY NOT BE THE WHOLE STORY: Revise issue #994, still OPEN, is exactly this shape --
    # "Edits to function initially ignored, until unrelated edits happen". So treat a missing symbol as
    # a REASON TO RESTART, not as a puzzle to solve; the restart is seconds and the puzzle is not.
    #
    # (2) PRECOMPILE BEFORE BOOTING, so Revise has no struct diff to apply at load. Revise revises
    # structs on 1.12, but it cannot re-initialise a const global when its struct is redefined --
    # doing so would wipe live state -- so a daemon that outlives a struct change strands every const
    # container typed on it in the old world age:
    #     _IDG type      = Dict{Atom, @world at MeTTaCore.Eval.IDGNode, 38726:41727}
    #     valtype match? = false
    # and inserts die with "Cannot convert IDGNode to @world at IDGNode". Revise documents the binding
    # half under Limitations, "Toplevel binding changes do not propagate": "The same applies to const
    # bindings and other global bindings that are referenced in type definitions."
    # Vendored at dev-zone/Revise.jl/docs/src/limitations.md.
    # 🔑 AND THE MECHANISM IS NAMED IN AN OPEN UPSTREAM ISSUE -- Revise #1116: "revise() runs in a
    # frozen world, and on 1.12 globals are world-partitioned". That is precisely the @world type we
    # saw. Related open ones in the same family: #1107 (a removed global keeps its old value live),
    # #1104/#1105/#1106 (stale methods survive various edits). Revise's method tracking is excellent;
    # its BINDING tracking has a live bug family. Structure long-lived warm state accordingly.
    #
    # 🔑 AND THE META-LESSON, WHICH COST MORE THAN EITHER: the world-age failure I chased for an hour
    # belonged to a THREE-HOUR-OLD daemon that `stop` could not see, because RUNDIR had moved and its
    # pidfile was at the old path. Four "fixes" were measured against a process that had none of them.
    # BEFORE BELIEVING A WARM RESULT, CHECK WHICH PROCESS SERVED IT. That is why `stop` kills by PORT.
    julia --project="$CORE" -e 'using Pkg; Pkg.precompile(io=devnull)' >/dev/null 2>&1
    setsid nohup julia --project="$CORE" -e "
        using Revise, DaemonMode
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
    # 🔴🔴 ONE CLIENT AT A TIME. DaemonMode serves requests SEQUENTIALLY, so a second invocation does
    # not run in parallel -- it QUEUES, invisibly, behind whatever is already running. Measured
    # 2026-08-18: a `for f in test/.../*.jl` loop hit this script's 10-minute budget, the outer command
    # was killed, and its ALREADY-SPAWNED clients kept sitting in the queue. Everything afterwards
    # looked mysteriously slow -- three clients stacked on one daemon, the oldest 32 minutes in, all
    # serialised on a 2-core box. Nothing errored; there was simply a line I could not see.
    # Refuse instead, and say what to do. (A loop over files is the wrong shape anyway: each call
    # spawns a fresh client julia that pays its OWN JIT before it ever reaches the warm daemon.
    # Put the loop INSIDE one driver file.)
    local busy
    busy=$(pgrep -f "runfile.*port=$PORT" 2>/dev/null | grep -v "^$$\$" | head -3)
    if [ -n "$busy" ]; then
      echo "  warm_suite: ⛔ a client is ALREADY running against port $PORT (pids: $(echo $busy))."
      echo "     DaemonMode serialises — a second run would queue silently, not go faster."
      echo "     Wait for it, or: kill $(echo $busy)"
      exit 1
    fi
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
    # 🔴 STREAM IT. DaemonMode hands the client output as the run PROGRESSES for some lanes and only
    # at the END for others, and a silent 12-minute run is indistinguishable from a hung one -- I sat
    # on a 0-byte output file twice today deciding whether to kill it. `stdbuf -oL` line-buffers the
    # client so progress is visible as it happens, and the tee keeps a log to point at afterwards.
    stdbuf -oL -eL julia -e "using DaemonMode; runfile(raw\"$drv\"; port=$PORT)" 2>&1 | tee "$RUNDIR/last.log"
    rm -f "$drv"
    [ -f "$verdict" ] && exit "$(cat "$verdict")"
    echo "  warm_suite: NO VERDICT WRITTEN — treating as FAILURE (daemon died?)"; exit 1
}

case "${1:-run}" in
  start)   _start ;;
  stop-all)
     # BOTH lanes. `stop` alone leaves the other daemon holding its port and its memory — and the
     # gate daemon is the bigger one (~950 MB RSS on this 17 GB box).
     "$0" stop; "$0" stop-gate ;;
  stop-gate)
     _use_lane "$SUITE_PORT"
     "$0" stop 2>/dev/null || true
     CORE_WARM_SUITE_PORT="$SUITE_PORT" "$0" stop ;;
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
       echo "  ℹ️  Revise reloads function bodies AND struct fields on 1.12 (measured)."
       echo "     BUT a const container typed on a changed struct is stranded in the old world age"
       echo "     (Revise #1116, open) — restart if you changed a struct something holds."
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
     _use_lane "$SUITE_PORT"
     # 🟢 THE SUITE LANE IS NOW WARM BY DEFAULT — 2026-08-18. It restarted on every invocation for a
     # year of sessions, and the reason was real: the suite leaked state, so a second run in one
     # process invented failures, and a harness that invents failures is worse than a slow one.
     #
     # THE LEAKS ARE FIXED, and there were only three in 92 files. Found by running the suite twice in
     # one daemon and diffing (`run-warm`, below):
     #   · test_spaces_registry.jl and test_corespace.jl each built a Shared MORK region at a FIXED
     #     prefix and asserted it was empty. Shared regions co-reside in ONE process-global trie that
     #     nothing resets, so the region still held what that testset wrote the last time it ran
     #     ANYWHERE in the process. Both now derive a unique prefix per invocation.
     #   · test_completion_resume.jl and test_dependency_firing.jl restored `_RESUME_COMPLETION` and
     #     `_DEPS_RECORD` to the LITERAL false — the default when they were written. That default
     #     flipped to true on 2026-08-16 and the restores never followed, so every file that ran after
     #     them silently exercised the RECOMPUTATION path. All restores now go through
     #     `reset_execution_flags!()`, so a default can only move in one place.
     #
     # MEASURED back to back on the same box, 92 files / 0 failed each:
     #     run-cold   466 s wall   (298 s of testsets + restart + full JIT)
     #     run        147 s wall   (120-121 s of testsets)
     # A 3.2x speedup, ~5 minutes back on every gate. That is the difference between verifying once
     # and verifying often.
     # ⚠️ AN EARLIER DRAFT OF THIS COMMENT SAID "~20 min -> 2.5 min, 8x". That was real elapsed time
     # but not a like-for-like comparison: those runs also paid a cold precompile and shared the box
     # with other work. The honest number is the one above, and it is still the right call.
     #
     # ⚠️ IF A `run` FAILURE LOOKS IMPLAUSIBLE, RE-CHECK IT WITH `run-cold` BEFORE BELIEVING IT.
     # A newly-added test that leaks would show up here first, and it will look like a regression in
     # whatever ran after it rather than in itself.
     _start || exit 1
     shard="${2:-}"
     if [ -n "$shard" ]; then
       _run_driver "isdefined(Main, :SUITE_FAILED) && empty!(Main.SUITE_FAILED); ENV[\"CORE_SUITE_SHARD\"] = raw\"$shard\"; include(raw\"$CORE/test/runtests.jl\")"
     else
       _run_driver "isdefined(Main, :SUITE_FAILED) && empty!(Main.SUITE_FAILED); delete!(ENV, \"CORE_SUITE_SHARD\"); include(raw\"$CORE/test/runtests.jl\")"
     fi ;;
  run-cold)
     _use_lane "$SUITE_PORT"
     # The old behaviour, kept as the arbiter. Use it to confirm a suspicious `run` failure, or when
     # you have just added a test that touches shared/global state.
     "$0" restart >/dev/null 2>&1
     _start || exit 1
     shard="${2:-}"
     if [ -n "$shard" ]; then
       _run_driver "ENV[\"CORE_SUITE_SHARD\"] = raw\"$shard\"; include(raw\"$CORE/test/runtests.jl\")"
     else
       _run_driver "delete!(ENV, \"CORE_SUITE_SHARD\"); include(raw\"$CORE/test/runtests.jl\")"
     fi ;;
  run-warm)
     _use_lane "$SUITE_PORT"
     # 🔬 THE SAME SUITE, IN THE DAEMON THAT IS ALREADY UP — no restart. This is the MEASUREMENT that
     # tells us whether `run` still needs to restart: anything that fails here and passed under `run`
     # is state some file LEAKS into the next one.
     #
     # ⚠️ NOT A GATE. Use `run` for a verdict. This exists to FIND leaks so `run` can eventually stop
     # restarting, which is worth roughly nine minutes on every gate.
     # ⚠️ runtests.jl declares `const SUITE_FAILED`, so a second include in one process would fail on
     # the const redeclaration rather than on any test. The driver therefore clears it first — that is
     # the harness's own state, not the suite's, and leaving it would mask exactly what we are hunting.
     _start || exit 1
     _run_driver "isdefined(Main, :SUITE_FAILED) && empty!(Main.SUITE_FAILED); delete!(ENV, \"CORE_SUITE_SHARD\"); include(raw\"$CORE/test/runtests.jl\")" ;;
  *) echo "  usage: warm_suite.sh {start|run [i/n]|run-cold [i/n]|run-warm|file <path>|restart|status|stop}"; exit 2 ;;
esac
