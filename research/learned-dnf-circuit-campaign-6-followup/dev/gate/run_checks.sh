#!/usr/bin/env bash
# One check.sh call per gate file, as predict6.gate_each: the pinned Lean first on PATH, the pinned interpreter.
export PATH=/home/user/lean-pinned/dist/bin:$PATH
export PYTHON=/home/user/owner-prep/venv312/bin/python
here=$(cd "$(dirname "$0")" && pwd)
for name in Gate6_1x_frozen Gate6_1x_oneport Gate6_2x_frozen Gate6_2x_oneport; do
  start=$(date +%s)
  bash REPO/research/learned-dnf-circuit-campaign-5/check.sh "$here/$name.lean" > "$here/check_$name.log" 2>&1
  echo "$name exit=$? seconds=$(( $(date +%s) - start ))" >> "$here/CHECKS_DONE.txt"
done
echo "all done" >> "$here/CHECKS_DONE.txt"
