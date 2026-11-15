#!/usr/bin/env bash
# Compiles the guarded model, the port system of ../network-circuit/phase1 and the ring of ../network-circuit-ring
# with warnings as errors, then, when it exists, Predicted.lean: per port and budget, `Own` or its negation for the
# instances of campaign 2, and the writes of their zero-error runs, checked by the Lean kernel.
# Needs only the pinned Lean, no Lake package. `check.sh FILE` checks FILE instead of Predicted.lean.
set -euo pipefail

cd "$(dirname "$0")"
here=$PWD
repo=$(git rev-parse --show-toplevel)
target=${1:-Predicted.lean}
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"
mkdir "$build/SelfCertifyingLearning"
(
  cd "$repo/research/self-certifying-learning"
  for module in Budget Composition; do
    lean -o "$build/SelfCertifyingLearning/$module.olean" "SelfCertifyingLearning/$module.lean"
  done
)
(
  cd "$repo/research/network-stability"
  for module in RoutedCalendar AutonomousFeedback; do
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
  done
)
(
  cd "$repo/research/network-circuit/phase1"
  for module in CircuitNetwork DatedOrder; do
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
  done
)
(
  cd "$repo/research/network-circuit-ring"
  lean -DwarningAsError=true -o "$build/RingNetwork.olean" RingNetwork.lean
)
cd "$here"
if [[ -f "$target" ]]; then
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' "$target"; then
    exit 1
  fi
  lean -DwarningAsError=true "$target"
  echo "Predicted.lean: checked"
else
  echo "Predicted.lean: not written yet"
fi
