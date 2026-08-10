#!/bin/bash
# run_tests.sh — run Core's suite in the MANDATED warm REPL and EXIT WITH THE RESULT.
#
# Ported from MORK/tools/run_tests.sh (2026-07-29). Core was the last of the three cold-start-hooked
# packages without one, and `.claude/hooks/discourage-core-cold-start.sh` says so in its own error
# text: "Core has no run_tests.sh yet (MORK/PathMap do) … worth porting here properly if Core probes
# keep needing trustworthy verification, not just iteration." They do. This is that port.
#
# WHY THIS EXISTS. The documented invocation
#     printf 'include("test/runtests.jl");exit()\n' | julia --project=. -i tools/repl.jl
# ALWAYS EXITS 0 — regardless of failures OR errors. `julia -i` with piped stdin is interactive, and
# interactive mode SWALLOWS exceptions: the throw is printed, the REPL continues, and the trailing
# `exit()` returns 0. Measured in MORK:
#     piped -i, error then exit()      -> 0
#     piped -i, FAILING @testset       -> 0        <-- a red suite reporting success
#     non-interactive `julia file.jl`  -> 1        <-- correct
# So the warm-REPL workflow this repo MANDATES (hook-enforced, to avoid cold-start cost) could not
# fail a build. In MORK that is exactly how its only upstream differential check sat ERRORING on
# every run unnoticed (commit c543841). An `errored` line among N passes reads as noise; an exit
# code does not.
#
# The fix keeps the warm REPL and makes the status real: guard the include, and exit with a code
# computed from whether it threw. A Julia testset throws `Some tests did not pass: …` when anything
# failed OR errored, so this catches both.
#
# `< /dev/null` IS LOAD-BEARING — not tidiness. Anything that spawns a subprocess with an explicit
# stdio handle (Aqua's test_persistent_tasks is the known case) is handed the CURRENT stdin. Piping
# the driver in leaves stdin a PipeEndpoint that printf has ALREADY CLOSED — `isopen(stdin) == false`
# — and libuv rejects a closed handle with EINVAL, showing up as a permanent phantom `1 errored`.
# So the driver goes in a FILE and stdin stays open.
#
# `-i` is kept deliberately so `isinteractive()` is true and tools/repl.jl loads exactly as it does
# in the mandated warm workflow. Keeping that path identical is the point — a runner that loads
# differently from the workflow it guards cannot catch the workflow's bugs.
#
# ABSOLUTE paths inside the driver, and the repl load INSIDE the guard: `include` in a script
# resolves relative to the SCRIPT'S directory, so a driver in /tmp doing `include("tools/repl.jl")`
# looks for /tmp/tools/repl.jl, throws at top level, and gets swallowed by `-i` — the very bug this
# file exists to close. Under `-i` nothing outside an explicit try/exit can be trusted to fail.
#
# Usage:  tools/run_tests.sh                              # whole suite
#         tools/run_tests.sh test/test_mork_native_rewrite.jl   # one file
# Exit:   0 = all green · 1 = failure/error
set -uo pipefail
cd "$(dirname "$0")/.."
TARGET="${1:-test/runtests.jl}"

ROOT="$PWD"
case "$TARGET" in /*) ABS_TARGET="$TARGET" ;; *) ABS_TARGET="$ROOT/$TARGET" ;; esac

if [ ! -f "$ABS_TARGET" ]; then
  echo "run_tests.sh: no such target: $ABS_TARGET" >&2
  exit 1
fi

DRIVER="$(mktemp "${TMPDIR:-/tmp}/core_run_tests_XXXXXX.jl")"
trap 'rm -f "$DRIVER"' EXIT
# The status variable is `__core_run_tests_ok__`, NOT `ok`. MORK's runner uses `ok`, and copying that
# verbatim broke the FULL suite here (found 2026-07-29 by running it): the driver binds `ok` at top
# level in Main, then `test/test_types.jl:19` defines a FUNCTION named `ok` and Julia refuses —
# "cannot define function ok; it already has a value". Single-file runs never hit it, so the port
# looked fine. Any name the driver binds in Main is in the same namespace as every test file's
# top-level definitions; keep it collision-proof.
cat > "$DRIVER" <<EOF
__core_run_tests_ok__ = try
    include(raw"$ROOT/tools/repl.jl")
    include(raw"$ABS_TARGET")
    true
catch e
    showerror(stderr, e); println(stderr)
    false
end
exit(__core_run_tests_ok__ ? 0 : 1)
EOF

# ── MEMORY CEILING — the test process must die BEFORE the machine does ──────────────────────────
#
# MEASURED 2026-08-10, and it cost the session: a new test evaluated `(match &self $a $a)` against a
# Space with the stdlib loaded. That returns EVERY atom in the space, the process grew past the box's
# 17 GB (a warm MettaJam server already holds ~5 GB of it), and the kernel OOM-killer chose its
# victim by score — it killed the VS Code server, not the runaway. The developer lost their session
# to a bad test in a different process.
#
# A cgroup scope fixes the blast radius: the runaway hits ITS OWN ceiling and dies with 137, and
# nothing outside the scope is a candidate. `MemorySwapMax=0` matters as much as `MemoryMax` — without
# it the process thrashes swap for minutes first, which is how the same run burned ~10 minutes before
# being killed.
#
# `--heap-size-hint` is the cooperative half: it tells Julia's GC the budget so it collects hard as it
# approaches, turning many would-be kills into a slow-but-completing run. Set BELOW the hard cap so
# the GC gets its chance first. Neither is a substitute for the other — the hint is advisory, the
# cgroup is not.
#
# Override for a genuinely large suite:  CORE_TEST_MEM_MAX=12G tools/run_tests.sh
# Escape hatch (say why):                CORE_TEST_MEM_MAX=none tools/run_tests.sh
MEM_MAX="${CORE_TEST_MEM_MAX:-8G}"
HEAP_HINT="${CORE_TEST_HEAP_HINT:-6G}"
JL=(julia --project=. --threads="${JULIA_TEST_THREADS:-4}" --heap-size-hint="$HEAP_HINT"
    -i "$DRIVER")

if [ "$MEM_MAX" = "none" ]; then
  echo "run_tests.sh: memory ceiling DISABLED (CORE_TEST_MEM_MAX=none)" >&2
  "${JL[@]}" < /dev/null
elif command -v systemd-run >/dev/null 2>&1 &&
     systemd-run --user --scope -p MemoryMax=256M --quiet true >/dev/null 2>&1; then
  # `--scope` runs it as a child of THIS shell (not a forked service), so stdin/stdout and the exit
  # code pass through unchanged — which the `< /dev/null` discipline above depends on.
  systemd-run --user --scope -p MemoryMax="$MEM_MAX" -p MemorySwapMax=0 --quiet \
      "${JL[@]}" < /dev/null
  rc=$?
  [ $rc -eq 137 ] && echo "run_tests.sh: KILLED at the ${MEM_MAX} ceiling — a test allocated without
  bound. Find it before raising CORE_TEST_MEM_MAX; the usual cause is an unbounded query (a
  space-wide \`match\` with a variable pattern) rather than a suite that legitimately needs more." >&2
  exit $rc
else
  # No usable cgroup scope. Say so LOUDLY rather than silently running uncapped — the failure mode
  # this guards against takes down the editor, not the test.
  echo "run_tests.sh: WARNING — systemd-run --user --scope unavailable; running WITHOUT a memory
  ceiling. A runaway test can OOM-kill unrelated processes on this machine." >&2
  "${JL[@]}" < /dev/null
fi
# allow-cold-start: full-suite runner; a suite run is a cold run by nature
