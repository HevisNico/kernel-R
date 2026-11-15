#!/usr/bin/env bash
# Compiles the guarded model, its instance for the circuit network, the lemma on the order of the dates and, when it
# exists, Predicted.lean: the margins of the instances of the campaign, checked by the Lean kernel.
set -euo pipefail

cd "$(dirname "$0")"
repo=$(git rev-parse --show-toplevel)
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
if [[ -f Predicted.lean ]]; then
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' Predicted.lean; then
    exit 1
  fi
  lean -DwarningAsError=true Predicted.lean
  echo "Predicted.lean: checked"
else
  echo "Predicted.lean: not written yet"
fi
