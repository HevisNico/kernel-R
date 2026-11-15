#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
for module in Target Recognition TwoLayerTarget; do
  lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
lean -DwarningAsError=true Audit.lean
