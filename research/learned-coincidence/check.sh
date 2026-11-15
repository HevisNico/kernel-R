#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
for module in Target Recognition TwoLayerTarget MonotoneTarget MonotoneSupport \
  MonotoneRecognition MonotoneCharacterization MonotoneOneSidedTarget \
  MonotoneOneSidedRecognition MonotonePremiseTargets MonotonePremiseCompletenessTargets \
  MonotonePremiseSoundness MonotonePremiseCompleteness MonotonePremiseExamples; do
  lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
lean -DwarningAsError=true Audit.lean
