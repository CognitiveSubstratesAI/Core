#!/usr/bin/env bash
# verify_corpus.sh — run every XSB wfs_tests program under the LIVE swipl and check it against the
# gold `query/5` row it ships with.
#
# 🔴 WHY VALIDATE THE ORACLE BEFORE USING IT. `[[feedback_verify_the_oracle_runs]]` and
# `[[feedback_verify_oracle_against_upstream_not_assume_canonical]]`: a corpus we have not executed is
# a corpus we are assuming. These gold rows come from XSB; we are about to hold our Julia engine to
# them, so the first question is whether the SWI engine — the one we ported from — reproduces them.
# Any row where it does not is a row we must not grade ourselves against.
#
#   test/standard/tabling/upstream/verify_corpus.sh          # all 72
#   test/standard/tabling/upstream/verify_corpus.sh p13      # one
set -uo pipefail
UP="${SWIPL_DEVEL:-$HOME/JuliaAGI/dev-zone/swipl-devel}"
SRC="$UP/tests/xsb/wfs_tests"
HERE="$(cd "$(dirname "$0")" && pwd)"
command -v swipl >/dev/null || { echo "swipl not on PATH"; exit 2; }

if [ -n "${1:-}" ]; then files="$SRC/${1%.P}.P"; else files=$(ls "$SRC"/*.P); fi
ok=0; diff=0; err=0
for f in $files; do
  # each program in its own process: these define the SAME predicate names (p/0, q/0, win/1) and
  # would collide in one image — the cross-file state hazard that bit our own runner today.
  out=$(cd "$SRC" && timeout 30 swipl -q "$HERE/verify_corpus.pl" "$f" 2>/dev/null)
  case "$out" in
    OK*)   ok=$((ok+1)) ;;
    DIFF*) diff=$((diff+1)); echo "$out" ;;
    *)     err=$((err+1)); echo "  ERR  $(basename "$f")" ;;
  esac
done
echo "  ── XSB wfs corpus vs live swipl: $ok agree · $diff differ · $err errored"
