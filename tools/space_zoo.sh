#!/bin/bash
# space_zoo.sh — construct one of every registered Space kind and print the capability ledger.
#
# Usage:  Core/tools/space_zoo.sh
# Exit:   0 = the zoo ran · 1 = something threw
#
# WHY A WRAPPER AND NOT `julia tools/space_zoo.jl`. Same reason run_tests.sh exists (read its header):
# the mandated warm workflow loads through tools/repl.jl, and a driver that loads DIFFERENTLY from the
# workflow it demonstrates cannot demonstrate it. This keeps the load path identical and still exits
# with a real status — an exception here means a declared capability stopped being true.
#
# ⚠️ ABSOLUTE paths in the driver: `include` in a script resolves relative to the SCRIPT'S directory,
# so a driver in /tmp doing include("tools/repl.jl") looks for /tmp/tools/repl.jl. And `< /dev/null`
# keeps stdin open for anything that spawns a subprocess with an explicit stdio handle. Both lessons
# are inherited from run_tests.sh, where each was a real bug.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"

DRIVER="$(mktemp "${TMPDIR:-/tmp}/core_space_zoo_XXXXXX.jl")"
trap 'rm -f "$DRIVER"' EXIT
cat > "$DRIVER" <<EOF
__core_space_zoo_ok__ = try
    include(raw"$ROOT/tools/repl.jl")
    include(raw"$ROOT/tools/space_zoo.jl")
    true
catch e
    showerror(stderr, e); println(stderr)
    false
end
exit(__core_space_zoo_ok__ ? 0 : 1)
EOF

julia --project="$ROOT" -i "$DRIVER" < /dev/null
