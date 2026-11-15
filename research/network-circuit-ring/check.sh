#!/usr/bin/env bash
# Compiles the guarded model of ../network-stability, its instance for the two-cell network and the port system of
# ../network-circuit/phase1, then the ring of this folder, with warnings as errors, and audits the axioms.
# Needs only the pinned Lean, no Lake package.
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
if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' RingNetwork.lean; then
  exit 1
fi
lean -DwarningAsError=true -o "$build/RingNetwork.olean" RingNetwork.lean
lean -DwarningAsError=true Audit.lean
