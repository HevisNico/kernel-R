#!/usr/bin/env bash
# Compile the inverter-instance gate library on the learned-coincidence modules, then each gate file given.
# Usage: lean/check.sh [Gate.lean ...]   (pinned Lean 4.35.0 on PATH)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
lc="$here/../../../../learned-coincidence"
build="${GATE_BUILD:-$(mktemp -d)}"
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
if [ ! -f "$build/InverterInstanceCheck.olean" ]; then
  for module in Target TwoLayerTarget MonotoneTarget MonotoneSupport TwoRailsTarget MonotoneOneSidedTarget InverterTarget; do
    (cd "$lc" && lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean")
  done
  (cd "$here" && lean -DwarningAsError=true -o "$build/InverterInstanceCheck.olean" InverterInstanceCheck.lean)
fi
for f in "$@"; do lean -DwarningAsError=true "$f"; done
