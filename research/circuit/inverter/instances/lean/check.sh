#!/usr/bin/env bash
# Compile the inverter-instance gate: the single-source definitions (research/circuit/lean/CircuitInverterGate.lean,
# core Lean only, taken byte-identical from proof/inverter-bridge 13aba3a), the learned-coincidence modules up to
# InverterTarget, and this package's abstract layer; then each gate file given.
# Usage: lean/check.sh [Gate.lean ...]   (pinned Lean 4.35.0 on PATH)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
lc="$here/../../../../learned-coincidence"
cl="$here/../../../lean"
gate_sha=ffb51672ce35ff52b5266dd9561250922d6807c680ed59fb1f702d589574b0ee   # CircuitInverterGate.lean at 13aba3a
echo "$gate_sha  $cl/CircuitInverterGate.lean" | sha256sum -c --quiet -
build="${GATE_BUILD:-$(mktemp -d)}"
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
if [ ! -f "$build/InverterInstanceTiming.olean" ]; then
  for module in Target TwoLayerTarget MonotoneTarget MonotoneSupport TwoRailsTarget MonotoneOneSidedTarget InverterTarget; do
    (cd "$lc" && lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean")
  done
  (cd "$cl" && lean -DwarningAsError=true -o "$build/CircuitInverterGate.olean" CircuitInverterGate.lean)
  (cd "$here" && lean -DwarningAsError=true -o "$build/InverterInstanceTiming.olean" InverterInstanceTiming.lean)
fi
for f in "$@"; do lean -DwarningAsError=true "$f"; done
