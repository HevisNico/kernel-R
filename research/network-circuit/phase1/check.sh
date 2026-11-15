#!/usr/bin/env bash
# Compiles the guarded model of ../../network-stability, its instance for the circuit network, the lemma on the
# order of the dates and the generated instances, with warnings as errors, then audits the axioms. Needs only the pinned Lean, no Lake package.
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
if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' CircuitNetwork.lean DatedOrder.lean Instances.lean; then
  exit 1
fi
for module in CircuitNetwork DatedOrder Instances; do
  lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
lean -DwarningAsError=true Audit.lean
