#!/usr/bin/env bash
# Campaign 5, the third pre-run, before PREDICTION.md is pushed (coordinator's review 3, B3): everything of prerun.sh and
# prerun2.sh again, with predicted5.py (the guarded fit in exact rationals) in place of predicted.py in the scratch tree,
# and a check that solve() refuses a float in a row.
#
#   prerun3.sh OUT_DIR
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
grep -qw avx512f /proc/cpuinfo || { echo "prerun3.sh: refused: no avx512f" >&2; exit 1; }
export OPENBLAS_CORETYPE=SkylakeX
core=$(OPENBLAS_VERBOSE=2 "$python" -B -c 'import numpy' 2>&1 | grep -m1 -o 'Core: .*' || true)
[[ "$core" == "Core: SkylakeX" ]] || { echo "prerun3.sh: OpenBLAS reports '$core'" >&2; exit 1; }
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
cp "$here/predicted5.py" "$work/research/prerun5/predicted.py"
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
"$python" -B - <<'PY2' | tee "$out/float_refusal.log"
import predicted as P
from fractions import Fraction as F
try:
    P.solve([[1, 0.0], [0, 1]], [1, 2])
except AssertionError as e:
    print("float in a row: refused:", e)
else:
    raise SystemExit("float in a row: NOT refused")
x = P.solve([[1, 0], [0, 1], [1, 1]], [1, 2, 3])
assert all(type(v) is F for v in x), x
print("int rows: solution", [str(v) for v in x], "all Fractions")
PY2
"$python" -B cases5.py "$out/CASES.json" "$out/Gate5CasesTargets.lean" Gate5Cases | tee "$out/python.log"
"$python" -B gate4.py cases "$out/CASES.json" "$out/Gate5Cases.lean"
for module in Gate5Cases Gate5CasesTargets; do
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' "$out/$module.lean"; then echo "$module: forbidden token" >&2; exit 1; fi
  cp "$out/$module.lean" "$build/$module.lean"
  (cd "$build" && lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean")
  "$python" -B - "$build/$module.lean" "$build/${module}Audit.lean" "$module" <<'PY' | tee -a "$out/audit.log"
import re, subprocess, sys
src, audit, module = sys.argv[1:]
text = open(src).read()
names = re.findall(r"^theorem ([A-Za-z0-9_']+)", text, flags=re.M)
ns = re.search(r"^namespace (\S+)", text, flags=re.M).group(1)
assert names, "no theorem"
open(audit, "w").write(f"import {module}\nopen {ns}\n" + "".join(f"#print axioms {n}\n" for n in names))
out = subprocess.run(["lean", audit], capture_output=True, text=True, cwd=src.rsplit("/", 1)[0])
assert out.returncode == 0, out.stdout + out.stderr
flat = " ".join(out.stdout.split())
found = [(n, {a.strip() for a in ax.split(",")}) for n, ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat)]
found += [(n, set()) for n in re.findall(r"'([^']+)' does not depend on any axioms", flat)]
assert len(found) == len(names), (len(found), len(names), out.stdout[-2000:])
for name, axioms in found:
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, (name, sorted(axioms))
print(f"{module}: {len(names)} theorems, each on a subset of [propext, Classical.choice, Quot.sound]")
PY
done
"$python" -B diag5.py "$out/DIAG.json" "$out/Diag5.lean" "$out/Diag5Targets.lean" | tee "$out/diag.log"
for module in Diag5 Diag5Targets; do
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' "$out/$module.lean"; then echo "$module: forbidden token" >&2; exit 1; fi
  cp "$out/$module.lean" "$build/$module.lean"
  (cd "$build" && lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean")
  echo "$module: compiled" | tee -a "$out/lean.log"
done
"$python" -B size5.py "$out/SIZE.json" | tee "$out/size.log"
"$python" -B budget5.py "$out/BUDGET.json" "$repo" | tee "$out/budget.log"
(cd "$out" && sha256sum * > SHA256SUMS)
echo "prerun3.sh: done"
