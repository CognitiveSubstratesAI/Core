#!/usr/bin/env bash
# warm_test.sh — run ONE test file in a WARM, Revise-tracked session, with a REAL exit code.
#
# ─── WHY THIS EXISTS ─────────────────────────────────────────────────────────────────────────────
# `tools/run_tests.sh` starts a FRESH process every call: ~1-2 min of MeTTaCore load + JIT per test
# file. That is correct for the regression gate (a clean process is what makes the exit code mean
# something) and pure waste when iterating on ONE file — measured ~15 times in one session on
# 2026-08-17 before anyone asked why.
#
# The obvious warm form is a trap, and the reason `run_tests.sh` exists:
#     printf 'include("t.jl")\n' | julia -i tools/repl.jl     # ⚠️ ALWAYS EXITS 0
# `julia -i` with piped stdin SWALLOWS exceptions, so a FAILING test reads as a pass. Eyeballing
# output is not a pass/fail signal.
#
# This gets both: `tools/repl.jl` preloads MeTTaCore and activates Revise (so `src/` edits hot-reload
# with no restart), and the driver `exit()`s on the test result, so `$?` is trustworthy.
#
# ─── WHEN TO USE WHICH ───────────────────────────────────────────────────────────────────────────
#   warm_test.sh <file>     iterating on one test file            — seconds after the first call
#   run_tests.sh <file>     one file, guaranteed-clean process    — ~1-2 min
#   run_tests.sh            THE REGRESSION GATE, before a commit  — fresh process, always
#
# ⚠️ NOT A REPLACEMENT FOR THE SUITE. Revise cannot reload a STRUCT DEFINITION or a `const`; if you
# changed either, this session is stale and will report on the OLD definition. Restart it (delete the
# socket file) or use `run_tests.sh`. That failure is silent, which is why it is stated here.
set -uo pipefail
CORE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
[ $# -ge 1 ] || { echo "usage: $0 test/path/to/file.jl [more.jl ...]" >&2; exit 2; }

DRIVER="$(mktemp /tmp/warm_test_driver_XXXXXX.jl)"
trap 'rm -f "$DRIVER"' EXIT
{
  echo 'using Test'
  echo "include(raw\"$CORE_DIR/tools/repl.jl\")"
  echo 'const _WT_FAILED = String[]'
  for f in "$@"; do
    # ALWAYS absolutise: the driver lives in /tmp, so a relative `include` resolves against /tmp,
    # not the repo. First attempt silently looked for /tmp/test/standard/... and "failed" the test.
    case "$f" in /*) abs="$f" ;; *) abs="$CORE_DIR/$f" ;; esac
    [ -f "$abs" ] || { echo "no such test file: $abs" >&2; exit 2; }
    cat <<JL
try
    include(raw"$abs")
catch e
    push!(_WT_FAILED, raw"$f")
    printstyled("\n  ✗ FAILED: ", raw"$f", "\n"; color = :red, bold = true)
    showerror(stderr, e); println(stderr)
end
JL
  done
  # the whole point: a REAL exit code, not `julia -i`'s unconditional 0
  echo 'if isempty(_WT_FAILED)'
  echo '    printstyled("\n  warm: all files passed\n"; color = :green, bold = true); exit(0)'
  echo 'else'
  echo '    printstyled("\n  warm: FAILED — ", join(_WT_FAILED, ", "), "\n"; color = :red, bold = true); exit(1)'
  echo 'end'
} > "$DRIVER"

cd "$CORE_DIR" && julia --project=. -i "$DRIVER" < /dev/null
