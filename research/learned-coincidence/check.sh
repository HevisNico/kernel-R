#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
for module in Target Recognition TwoLayerTarget MonotoneTarget MonotoneSupport \
  MonotoneRecognition MonotoneCharacterization TwoRailsTarget TwoRails MonotoneOneSidedTarget \
  MonotoneOneSidedRecognition MonotonePremiseTargets MonotonePremiseCompletenessTargets \
  MonotonePremiseSoundness MonotonePremiseCompleteness MonotonePremiseExamples \
  LayeredMonotoneTarget LayeredMonotoneRecognition LayeredMonotoneCharacterization \
  LayeredMonotoneExample LayeredMonotoneCheckerTargets LayeredMonotoneCheckerProofs \
  LayeredMonotoneCheckerExamples LayeredMonotoneCheckerBench; do
  lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
lean -DwarningAsError=true Audit.lean
