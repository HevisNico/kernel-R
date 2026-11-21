#!/usr/bin/env bash
# Step 2 of the layered phase: compile and audit every file of tests/run_layered.py, one gencheck_layered.sh call per
# file (timed, GENCHECK_TIMEOUT per file, default 1800 s), then the flipped controls with --expect-fail.
#   run_layered.sh DIR        (LEAN, GENCHECK_BUILD, GENCHECK_TIMEOUT as for gencheck_layered.sh)
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
d=$1
for f in "$d"/Synth_*.lean "$d"/Mut_*.lean "$d"/Control_pass.lean "$d"/Control_fail.lean; do
  bash "$here/gencheck_layered.sh" "$f" 2>&1 | grep -v '^Lean (version' | grep -v '^theory: compiled' | grep -E "compiled|theorems|passed|FAILED|error" | head -20
done
for f in "$d"/Flip_*.lean; do
  out=$(bash "$here/gencheck_layered.sh" --expect-fail "$f" 2>&1)
  if grep -q "failed to compile, as expected" <<<"$out"; then
    echo "$(basename "$f"): failed to compile, as required"
  else
    echo "$(basename "$f"): CONTROL NOT MET"; echo "$out" | tail -20
  fi
done
