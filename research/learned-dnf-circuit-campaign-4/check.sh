#!/usr/bin/env bash
# Campaign 4: the kernel gate, checked by the pinned Lean (no Lake package).
#
# 1. Compiles the theory of research/learned-coincidence the gate imports, with warnings as errors.
# 2. Writes, with the campaign code, the gate on the cases P0 to P6 and P4' (cases.py, gate4.py) and the mirror
#    mutations (mirror_mutations.py), from CALIBRATION.json of #172 only, and requires them to equal, byte for
#    byte, the files committed under rehearsal/ (gate-cases-4, mirror-mutations-3: the runs under the pinned
#    interpreter and the exact arithmetic of amendment 3).
# 3. Compiles each generated file with warnings as errors, refuses sorry, admit, native_decide, axiom, unsafe,
#    implemented_by and extern, and requires `#print axioms` of every theorem to be a subset of
#    [propext, Classical.choice, Quot.sound] (amendment 8: a theorem on no axiom passes, such as M8's
#    `no_eligible_instance`; a theorem on any other axiom, sorryAx or Lean.ofReduceBool among them, fails).
#
#   check.sh                 the steps above
#   check.sh FILE.lean ...   also checks each FILE.lean (the gate of the campaign, written from PREDICTED.json; the
#                            analysis's M8.lean), the same way, after the steps above
#
# PYTHON names the interpreter; it must be the pinned one (amendment 3, section 3: Python 3.12.3, numpy 2.3.5, and in
# the pinned venv the SHA-256 of both), which is recorded and checked first. Default: the pinned venv.
#
# The kernel (amendment 8): numpy's OpenBLAS is pinned to its SkylakeX kernel, the one the files under rehearsal/ were
# written with, on a CPU with avx512f; on another CPU check.sh refuses, except in CI with C4_CI_STRUCTURAL=1, where the
# JSON files are compared structurally (structural_compare.py) instead of byte for byte. The Lean files are compared
# byte for byte, compiled and audited on every CPU.
set -euo pipefail

cd "$(dirname "$0")"
here=$PWD
theory=$(cd ../learned-coincidence && pwd)
python=${PYTHON:-/home/user/owner-prep/venv312/bin/python}
cpu=$(grep -m1 '^model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')
if grep -qw avx512f /proc/cpuinfo; then
  export OPENBLAS_CORETYPE=SkylakeX
  compare=bytes
elif [[ "${C4_CI_STRUCTURAL:-}" == 1 ]]; then
  compare=structural
else
  echo "check.sh: refused (amendment 8): this CPU ($cpu) has no avx512f, so OpenBLAS cannot run the SkylakeX kernel the" \
    "files under rehearsal/ were written with" >&2
  exit 1
fi
core=$(OPENBLAS_VERBOSE=2 "$python" -B -c 'import numpy' 2>&1 | grep -m1 -o 'Core: .*' || true)
[[ "$compare" != bytes || "$core" == "Core: SkylakeX" ]] || { echo "check.sh: OpenBLAS reports '$core', not SkylakeX" >&2; exit 1; }
echo "check.sh: CPU $cpu; OpenBLAS ${core:-core not reported}; comparison of the generated JSON files: $compare"
"$python" -B -c 'import c4; print(c4.require_pinned())'
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"

(
  cd "$theory"
  for module in Target Recognition TwoLayerTarget MonotoneTarget MonotoneSupport MonotoneRecognition \
    MonotoneCharacterization MonotoneOneSidedTarget MonotoneOneSidedRecognition MonotonePremiseTargets \
    MonotonePremiseCompletenessTargets MonotonePremiseSoundness MonotonePremiseCompleteness; do
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
  done
)
echo "theory: compiled"

audit() {
  local file=$1 module
  module=$(basename "$file" .lean)
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' "$file"; then
    echo "$file: forbidden token" >&2
    exit 1
  fi
  [[ "$file" -ef "$build/$module.lean" ]] || cp "$file" "$build/$module.lean"
  (cd "$build" && lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean")
  "$python" -B - "$build/$module.lean" "$build/${module}Audit.lean" "$module" <<'PY'
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
on_three = sum(axioms == {"propext", "Classical.choice", "Quot.sound"} for _, axioms in found)
print(f"{module}: {len(names)} theorems, each on a subset of [propext, Classical.choice, Quot.sound] ({on_three} on all three)")
PY
}

"$python" -B cases.py "$build/CASES.json" "$build/Gate4CasesTargets.lean" Gate4Cases > "$build/cases.log"
tail -n +2 "$build/cases.log" | cmp - <(tail -n +2 rehearsal/gate-cases-4/python.log)
"$python" -B gate4.py cases "$build/CASES.json" "$build/Gate4Cases.lean"
"$python" -B mirror_mutations.py "$build/MUTATIONS.json" "$build/MirrorMutations.lean" > "$build/mutations.log"
grep -q "^mirror mutation test: passed$" "$build/mutations.log"
for pair in gate-cases-4/Gate4Cases.lean gate-cases-4/Gate4CasesTargets.lean mirror-mutations-3/MirrorMutations.lean; do
  cmp "$build/$(basename "$pair")" "rehearsal/$pair"
done
for pair in gate-cases-4/CASES.json mirror-mutations-3/MUTATIONS.json; do
  if [[ "$compare" == bytes ]]; then
    cmp "$build/$(basename "$pair")" "rehearsal/$pair"
  else
    "$python" -B structural_compare.py "$build/$(basename "$pair")" "rehearsal/$pair"
  fi
done
echo "generated files: equal to rehearsal/ (Lean files byte for byte; JSON files: $compare)"

audit "$build/Gate4Cases.lean"
audit "$build/Gate4CasesTargets.lean"
audit "$build/MirrorMutations.lean"

for file in "$@"; do
  audit "$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"
done
echo "check.sh: passed"
