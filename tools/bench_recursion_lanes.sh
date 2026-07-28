#!/bin/bash
# bench_recursion_lanes.sh — driver for bench_recursion_lanes.jl.
#
# B0 harness integrity:
#   * PRIVATE warm unit + PRIVATE warm dir per run — never Core/.warm (a concurrent agent's seq
#     collides there and you silently read someone else's out.txt).
#   * The sender NEVER prints out.txt on timeout; it prints STALE and exits 2.
#   * The session is RESTARTED before every phase, so no accumulated method can shadow anything.
#   * Each phase's output must carry `RUNID=<id> START` and `RUNID=<id> END` with the RUNID this
#     script generated, and a final `ROWS=<n>`. Missing sentinel => FAILED run, even with 0 errors.
#
# Usage: tools/bench_recursion_lanes.sh [phase ...]      (default: all)
set -uo pipefail

CORE="$(cd "$(dirname "$0")/.." && pwd)"
SCRATCH="${BENCH_SCRATCH:-/tmp/claude-1000/-home-shivaji1012-code-CognitiveSubstratesAI/94260b72-21f8-4228-a1a0-cd7e95ba9f22/scratchpad}"
RUNID="${BENCH_RUNID:-$(cat /proc/sys/kernel/random/uuid | cut -c1-8)}"
WARMDIR="$SCRATCH/warm-$RUNID"
UNIT="core-warm-bench-$RUNID"
OUTDIR="$SCRATCH/bench-$RUNID"
mkdir -p "$OUTDIR"
PHASES=("$@"); [ ${#PHASES[@]} -eq 0 ] && PHASES=(correctness gates l3steps l1ref peano append fib)

restart_session() {
  systemctl --user stop "$UNIT" >/dev/null 2>&1
  systemctl --user reset-failed "$UNIT" >/dev/null 2>&1
  rm -rf "$WARMDIR"; mkdir -p "$WARMDIR"
  systemd-run --user --unit="$UNIT" --working-directory="$CORE" \
      --setenv=WARMDIR="$WARMDIR" --setenv=BENCH_RUNID="$RUNID" --setenv=BENCH_PHASE="$1" \
      $(which julia) --project="$CORE" "$SCRATCH/warm_session_p.jl" >/dev/null || return 1
  for _ in $(seq 1 180); do [ -f "$WARMDIR/ready" ] && return 0; sleep 1; done
  echo "SESSION NEVER BECAME READY"; return 1
}

send() { # $1 = snippet, $2 = timeout seconds
  local D="$WARMDIR"
  local SEQ=$(( $(cat "$D/seq" 2>/dev/null || echo 0) + 1 ))
  cp "$1" "$D/in.jl"; echo "$SEQ" > "$D/seq"
  for _ in $(seq 1 "${2:-1800}"); do
    [ "$(cat "$D/done" 2>/dev/null)" = "$SEQ" ] && break
    sleep 1
  done
  if [ "$(cat "$D/done" 2>/dev/null)" != "$SEQ" ]; then
    echo "!!! TIMEOUT seq=$SEQ — out.txt IS STALE, DISCARD"; return 2
  fi
  cat "$D/out.txt"
}

FAIL=0
for ph in "${PHASES[@]}"; do
  echo "===== PHASE $ph (RUNID=$RUNID) ====="
  restart_session "$ph" || { echo "PHASE $ph: SESSION START FAILED"; FAIL=1; continue; }
  cat > "$WARMDIR/drive.jl" <<EOF
ENV["BENCH_RUNID"] = "$RUNID"; ENV["BENCH_PHASE"] = "$ph"
include("$CORE/tools/bench_recursion_lanes.jl")
EOF
  send "$WARMDIR/drive.jl" "${BENCH_TIMEOUT:-3000}" | tee "$OUTDIR/$ph.txt"
  rc=${PIPESTATUS[0]}
  out="$OUTDIR/$ph.txt"
  if [ $rc -ne 0 ]; then echo "PHASE $ph: SENDER FAILED rc=$rc — output DISCARDED"; FAIL=1; continue; fi
  grep -q "RUNID=$RUNID START phase=$ph" "$out" || { echo "PHASE $ph: MISSING START SENTINEL"; FAIL=1; }
  grep -q "RUNID=$RUNID END phase=$ph"   "$out" || { echo "PHASE $ph: MISSING END SENTINEL";   FAIL=1; }
  grep -q "^ROWS="                        "$out" || { echo "PHASE $ph: MISSING ROWS";           FAIL=1; }
  echo "----- phase $ph: cells=$(grep -c '^CELL ' "$out") rows=$(grep '^ROWS=' "$out" | tail -1)"
done
systemctl --user stop "$UNIT" >/dev/null 2>&1
echo "RUNID=$RUNID outputs in $OUTDIR ; FAIL=$FAIL"
exit $FAIL
