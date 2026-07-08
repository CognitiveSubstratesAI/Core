#!/usr/bin/env bash
# LeaTTa proved-oracle — OFFLINE regeneration / verification. Needs the LeaTTa Lean binary; NEVER run in
# CI (the standing gate test_leatta_oracle.jl is pure Core + the frozen corpus/ and needs no Lean).
#
#   1. verifies LeaTTa itself still proves the corpus (270/270, "ORACLE OK");
#   2. re-vendors corpus/*.metta + EXPECTED.txt from the LeaTTa checkout into ./corpus/.
#
# After re-vendoring, re-run the Julia gate and update LEATTA_LEDGER_BASELINE if the corpus changed:
#   cd ../../.. && printf 'using MeTTaCore,Test; include("test/oracle/leatta/test_leatta_oracle.jl")\n' \
#     | julia --project=. -i tools/repl.jl
set -euo pipefail
cd "$(dirname "$0")"

LEATTA_DIR="${LEATTA_DIR:-$HOME/JuliaAGI/dev-zone/LeaTTa}"
LEATTA_BIN="$LEATTA_DIR/.lake/build/bin/LeaTTa"
SRC="$LEATTA_DIR/tests/corpus"

if [[ ! -x "$LEATTA_BIN" ]]; then
  echo "LeaTTa binary not found at $LEATTA_BIN — build it first:"
  echo "  ( cd $LEATTA_DIR && lake build LeaTTa )   # mathlib-free exe; ~15 min first time"
  exit 1
fi

echo "== LeaTTa version / provenance =="
echo "  binary: $LEATTA_BIN"
echo "  corpus: $SRC  (Hyperon unmodified corpus, MIT)"
echo

echo "== 1. LeaTTa self-proof of the corpus (expect: ORACLE OK, 270/270) =="
if [[ -x "$LEATTA_DIR/scripts/run-oracle.sh" ]]; then
  ( cd "$LEATTA_DIR" && ./scripts/run-oracle.sh )
else
  for f in "$SRC"/*.metta; do
    [[ "$(basename "$f")" == c2_spaces_kb.metta ]] && continue
    printf '  %-26s ' "$(basename "$f")"
    "$LEATTA_BIN" --oracle "$f" | tail -1
  done
fi
echo

echo "== 2. re-vendor corpus + EXPECTED.txt into ./corpus/ =="
cp -v "$SRC"/*.metta ./corpus/
cp -v "$SRC/EXPECTED.txt" ./corpus/
echo
echo "Done. Now re-run the Julia gate (see header) and reconcile LEATTA_LEDGER_BASELINE."
