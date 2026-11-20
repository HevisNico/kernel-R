#!/usr/bin/env bash
# Mine, NOT campaign 5's check.sh: compiles the theory with check.sh's own commands (same modules, same order,
# warnings as errors), then each Gate7_*.lean of this folder the same way. A gate file compiles only if Lean's kernel
# agrees with every verdict written in it (`decide +kernel`). No regeneration of campaign 5's cases, no axioms audit.
#   compile_gates.sh        writes COMPILED.txt beside the gate files: one line per file, "ok" or "FAILED", and seconds
set -uo pipefail
export PATH=/home/user/lean-pinned/dist/bin:$PATH
here=$(cd "$(dirname "$0")" && pwd)
theory=REPO/research/learned-coincidence
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"
(
  cd "$theory"
  for module in Target Recognition TwoLayerTarget MonotoneTarget MonotoneSupport MonotoneRecognition \
    MonotoneCharacterization MonotoneOneSidedTarget MonotoneOneSidedRecognition MonotonePremiseTargets \
    MonotonePremiseCompletenessTargets MonotonePremiseSoundness MonotonePremiseCompleteness; do
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean" || exit 1
  done
) || { echo "theory: FAILED" > "$here/COMPILED.txt"; exit 1; }
: > "$here/COMPILED.txt"
for file in "$here"/Gate7_*.lean; do
  name=$(basename "$file" .lean)
  cp "$file" "$build/$name.lean"
  start=$(date +%s)
  if (cd "$build" && lean -DwarningAsError=true -o "$build/$name.olean" "$name.lean") > "$here/$name.out" 2>&1; then
    echo "$name ok $(( $(date +%s) - start )) s" >> "$here/COMPILED.txt"
  else
    echo "$name FAILED $(( $(date +%s) - start )) s" >> "$here/COMPILED.txt"
  fi
done
echo "all done" >> "$here/COMPILED.txt"
