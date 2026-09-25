#!/usr/bin/env bash
# gate_commit.sh — run the suite against the COMMITTED tree, not the working tree.
#
# WHY. `c558a99` was pushed BROKEN and the gate was green. Eval.jl held two unrelated changes;
# `git add src/standard/Eval.jl` staged both, so the commit carried a 6-arg `index_candidates` call
# whose matching DEFINITION was still uncommitted in Index.jl. The suite passed because it ran on the
# WORKING TREE, where both halves existed. Nothing about the commit itself was ever tested.
# `git add -p` fixes that CASE; this fixes the CLASS — what gets tested is what gets pushed.
#
# ⚠️ THE FIRST VERSION OF THIS SCRIPT PROVED NOTHING, and the shape of that failure is worth keeping.
# It put the worktree in a bare $TMPDIR and reported `c558a99-> exit 1`, which looked like a catch.
# The actual error was `Package MORK is required but does not seem to be installed`: Core's
# Project/Manifest dev-reference their siblings as `path = "../MORK"` etc, and a worktree under /tmp
# has no siblings. The POSITIVE CONTROL is what exposed it — the known-good `db57932` failed
# identically, i.e. the gate rejected everything. A gate that cannot pass a good commit has not
# caught a bad one.
#
# So the layout is built deliberately: $ROOT/Core is the checkout under test, and every sibling the
# manifest names is symlinked beside it from the REAL tree. The siblings are the working copies on
# purpose — this gates Core's commit, not theirs.
#
# Usage:  tools/gate_commit.sh [<rev>] [-- <run_tests.sh args>]
set -uo pipefail
CORE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(cd "$CORE/.." && pwd)"
REV="${1:-HEAD}"; shift || true
ROOT="$(mktemp -d "${TMPDIR:-/tmp}/core_gate_XXXXXX")"
WT="$ROOT/Core"

cleanup() { git -C "$CORE" worktree remove --force "$WT" >/dev/null 2>&1; rm -rf "$ROOT"; }
trap cleanup EXIT

echo "gate_commit: $REV -> $WT"
git -C "$CORE" worktree add --detach --quiet "$WT" "$REV" || { echo "gate_commit: worktree add failed"; exit 1; }

# Symlink every sibling the manifest dev-references, so `path = "../X"` resolves.
for rel in $(grep -oE 'path = "\.\./[A-Za-z0-9_]+"' "$CORE/Manifest.toml" 2>/dev/null | sed 's|path = "\.\./||; s|"||' | sort -u); do
    if [ -d "$PARENT/$rel" ]; then
        ln -sfn "$PARENT/$rel" "$ROOT/$rel"
    else
        echo "gate_commit: WARNING — sibling '$rel' not found at $PARENT/$rel"
    fi
done
echo "gate_commit: siblings linked: $(find "$ROOT" -maxdepth 1 -type l -printf '%f ' 2>/dev/null)"

# ⚠️ Manifest.toml IS GITIGNORED, so the worktree has none and NOTHING resolves — which is why the
# first two attempts at this gate failed identically on a good and a bad commit. The manifest is
# ENVIRONMENT STATE (pinned dependency versions), not the source under test, so it is copied in from
# the working tree rather than regenerated: regenerating could silently gate against different
# dependency versions than the ones the suite normally runs on.
if [ -f "$CORE/Manifest.toml" ]; then
    cp "$CORE/Manifest.toml" "$WT/Manifest.toml"
    echo "gate_commit: copied Manifest.toml (gitignored — env state, not source under test)"
else
    echo "gate_commit: WARNING — no Manifest.toml in $CORE; resolution may fail"
fi

untracked=$(git -C "$CORE" ls-files --others --exclude-standard | wc -l)
[ "$untracked" -gt 0 ] && echo "gate_commit: NOTE — $untracked untracked working-tree file(s) are NOT in this gate (that is the point)."

# The marker belongs to the WORKING tree; a committed-tree pass must not authorise committing
# something else. Point it at a throwaway path.
( cd "$WT" && PRIMUS_TEST_MARKER="$ROOT/.marker" bash tools/run_tests.sh "$@" )
rc=$?
echo "gate_commit: $REV -> exit $rc"
exit $rc
