#!/usr/bin/env bash
# Campaign 5, the second pre-run, before PREDICTION.md is pushed (coordinator's review 2): the diagnostic of P2's
# interval (diag5.py, B2) and the rehearsal stages against the kit's check_budget (budget5.py, B1).
#
#   prerun2.sh OUT_DIR
#
# Runs under the pinned toolchain only: the kit's identity check (Python 3.12.3, numpy 2.3.5, ngspice 42, PDK),
# Lean 4.35.0, and numpy's OpenBLAS on its SkylakeX kernel on a CPU with avx512f. Copies this folder into a fresh
# tree beside research/learned-dnf-circuit (CALIBRATION.json, dnf.py), research/network-circuit and
# research/learned-coincidence of this commit, since campaign 4's code finds them by its own folder's parent. Then:
# compiles the theory, writes the cases (cases5.py), the gate on them (gate4.py cases), compiles both Lean files with
# warnings as errors and audits their axioms as campaign 4's check.sh does, and runs the sizing (size5.py).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
out=$1; mkdir -p "$out"; out=$(cd "$out" && pwd)
python=/home/user/owner-prep/venv312/bin/python
export PATH=/home/user/lean/bin:$PATH
grep -qw avx512f /proc/cpuinfo || { echo "prerun2.sh: refused: no avx512f" >&2; exit 1; }
export OPENBLAS_CORETYPE=SkylakeX
core=$(OPENBLAS_VERBOSE=2 "$python" -B -c 'import numpy' 2>&1 | grep -m1 -o 'Core: .*' || true)
[[ "$core" == "Core: SkylakeX" ]] || { echo "prerun2.sh: OpenBLAS reports '$core'" >&2; exit 1; }
{
  echo "commit: $(git -C "$repo" rev-parse HEAD)"
  echo "cpu: $(grep -m1 '^model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//'); OpenBLAS $core"
  echo "lean: $(lean --version)"
  "$python" -B "$repo/research/sky130-supervisor-closure/launchkit/launch.py" identity --ngspice /usr/bin/ngspice --pdk /home/user/campaign/pdk | tr -d '\n '; echo
} > "$out/ENVIRONMENT.txt"
work=$(mktemp -d); build=$work/build; mkdir -p "$build" "$work/research"
trap 'rm -rf "$work"' EXIT
for d in learned-dnf-circuit network-circuit learned-coincidence; do cp -r "$repo/research/$d" "$work/research/$d"; done
cp -r "$here" "$work/research/prerun5"
export LEAN_PATH="$build"
(
  cd "$work/research/learned-coincidence"
  for module in Target Recognition TwoLayerTarget MonotoneTarget MonotoneSupport MonotoneRecognition \
    MonotoneCharacterization MonotoneOneSidedTarget MonotoneOneSidedRecognition MonotonePremiseTargets \
    MonotonePremiseCompletenessTargets MonotonePremiseSoundness MonotonePremiseCompleteness; do
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
  done
)
echo "theory: compiled"
cd "$work/research/prerun5"
"$python" -B diag5.py "$out/DIAG.json" "$out/Diag5.lean" "$out/Diag5Targets.lean" | tee "$out/diag.log"
for module in Diag5 Diag5Targets; do
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' "$out/$module.lean"; then echo "$module: forbidden token" >&2; exit 1; fi
  cp "$out/$module.lean" "$build/$module.lean"
  (cd "$build" && lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean")
  echo "$module: compiled" | tee -a "$out/lean.log"
done
"$python" -B budget5.py "$out/BUDGET.json" "$repo" | tee "$out/budget.log"
(cd "$out" && sha256sum DIAG.json Diag5.lean Diag5Targets.lean diag.log lean.log BUDGET.json budget.log ENVIRONMENT.txt > SHA256SUMS)
echo "prerun2.sh: done"
