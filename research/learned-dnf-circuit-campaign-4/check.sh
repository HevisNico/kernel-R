#!/usr/bin/env bash
# Campaign 4: the kernel gate, checked by the pinned Lean (no Lake package).
#
# 1. Compiles the theory of research/learned-coincidence the gate imports, with warnings as errors.
# 2. Writes, with the campaign code, the gate on the cases P0 to P6 and P4' (cases.py, gate4.py) and the mirror
#    mutations (mirror_mutations.py), from CALIBRATION.json of #172 only, and requires them to equal, byte for
#    byte, the files committed under rehearsal/ (gate-cases-2, mirror-mutations).
# 3. Compiles each generated file with warnings as errors, refuses sorry, admit, native_decide, axiom, unsafe,
#    implemented_by and extern, and requires `#print axioms` of every theorem to be exactly
#    [propext, Classical.choice, Quot.sound].
#
#   check.sh                 the steps above
#   check.sh FILE.lean       also checks FILE.lean (the gate of the campaign, written from PREDICTED.json), the
#                            same way, after the steps above
#
# PYTHON names the interpreter (with numpy); default python3.
set -euo pipefail

cd "$(dirname "$0")"
here=$PWD
theory=$(cd ../learned-coincidence && pwd)
python=${PYTHON:-python3}
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
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", " ".join(out.stdout.split()))
assert len(found) == len(names), (len(found), len(names), out.stdout[-2000:])
for name, axioms in found:
    assert sorted(a.strip() for a in axioms.split(",")) == ["Classical.choice", "Quot.sound", "propext"], (name, axioms)
print(f"{module}: {len(names)} theorems, each on exactly [propext, Classical.choice, Quot.sound]")
PY
}

"$python" -B cases.py "$build/CASES.json" "$build/Gate4CasesTargets.lean" Gate4Cases > "$build/cases.log"
"$python" -B gate4.py cases "$build/CASES.json" "$build/Gate4Cases.lean"
"$python" -B mirror_mutations.py "$build/MUTATIONS.json" "$build/MirrorMutations.lean" > "$build/mutations.log"
grep -q "^mirror mutation test: passed$" "$build/mutations.log"
for pair in gate-cases-2/CASES.json gate-cases-2/Gate4Cases.lean gate-cases-2/Gate4CasesTargets.lean \
  mirror-mutations/MUTATIONS.json mirror-mutations/MirrorMutations.lean; do
  cmp "$build/$(basename "$pair")" "rehearsal/$pair"
done
echo "generated files: equal to rehearsal/"

audit "$build/Gate4Cases.lean"
audit "$build/Gate4CasesTargets.lean"
audit "$build/MirrorMutations.lean"

if [[ $# -ge 1 ]]; then
  audit "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
fi
echo "check.sh: passed"
