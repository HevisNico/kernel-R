#!/usr/bin/env bash
# M4: compile and audit every file written by tests/run_synth.py, one gencheck.sh call per file (timed), then the
# flipped controls with --expect-fail (each must fail with a `decide` error).
#   run_m4.sh M4_DIR        (LEAN, GENCHECK_BUILD, GENCHECK_TIMEOUT as for gencheck.sh)
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
d=$1
for f in "$d"/Synth_*.lean "$d"/Mut_*.lean "$d"/Reach.lean "$d"/Control_pass.lean "$d"/Control_fail.lean; do
  bash "$here/gencheck.sh" "$f" 2>&1 | grep -v '^Lean (version' | grep -v '^theory: compiled'
done
for f in "$d"/Flip_*.lean; do
  out=$(bash "$here/gencheck.sh" --expect-fail "$f" 2>&1)
  if grep -q "failed to compile, as expected" <<<"$out" && grep -qi "decide" <<<"$out"; then
    echo "$(basename "$f"): failed to compile with a decide error, as required"
  else
    echo "$(basename "$f"): CONTROL NOT MET"; echo "$out" | tail -20
  fi
done
