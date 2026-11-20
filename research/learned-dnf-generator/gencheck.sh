#!/usr/bin/env bash
# The generator's kernel check (GENERATOR_DESIGN.md 4.5). New script; campaign 5's check.sh is not edited. It keeps
# the meaning of that script's steps 1 and 3 (C5/check.sh:52-90) and drops its step 2, which regenerates campaign 5's
# own fixtures:
#
# 1. compiles the 13 theory modules of research/learned-coincidence that the gate imports, with warnings as errors,
#    into BUILD (kept between calls: GENCHECK_BUILD, default a fresh temporary directory);
# 2. for each FILE.lean: refuses sorry, admit, native_decide, axiom, unsafe, implemented_by, extern; compiles it with
#    warnings as errors; requires `#print axioms` of every theorem to be a subset of
#    [propext, Classical.choice, Quot.sound]; prints the compile's wall time.
#
#   gencheck.sh FILE.lean ...          every file must pass
#   gencheck.sh --expect-fail FILE ... every file must FAIL to compile (the controls of 4.4); prints Lean's first error
#
# GENCHECK_TIMEOUT: seconds allowed per file compile (default 1800, the coordinator's 30-minute limit).
#
# LEAN names the lean binary (default: lean on PATH); PYTHON the interpreter of the audit (default python3).
# THEORY overrides the theory directory (default ../learned-coincidence next to this directory).
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
theory=${THEORY:-$(cd "$here/../learned-coincidence" && pwd)}
lean=${LEAN:-lean}
python=${PYTHON:-python3}
expect_fail=0
if [[ "${1:-}" == --expect-fail ]]; then expect_fail=1; shift; fi
"$lean" --version
if [[ -n "${GENCHECK_BUILD:-}" ]]; then
  build=$GENCHECK_BUILD; mkdir -p "$build"
else
  build=$(mktemp -d); trap 'rm -rf "$build"' EXIT
fi
export LEAN_PATH="$build"

modules="Target Recognition TwoLayerTarget MonotoneTarget MonotoneSupport MonotoneRecognition \
  MonotoneCharacterization MonotoneOneSidedTarget MonotoneOneSidedRecognition MonotonePremiseTargets \
  MonotonePremiseCompletenessTargets MonotonePremiseSoundness MonotonePremiseCompleteness"
(
  cd "$theory"
  for module in $modules; do
    # A kept build is reused only if its source is unchanged (sha256 recorded beside the .olean).
    sum=$(sha256sum "$module.lean" | cut -d' ' -f1)
    if [[ -f "$build/$module.olean" && "$(cat "$build/$module.sha256" 2>/dev/null)" == "$sum" ]]; then continue; fi
    "$lean" -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
    echo "$sum" > "$build/$module.sha256"
  done
)
echo "theory: compiled ($theory)"

audit() {
  local file=$1 module start end
  module=$(basename "$file" .lean)
  if grep -nE '\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b' "$file"; then
    echo "$file: forbidden token" >&2
    return 1
  fi
  [[ "$file" -ef "$build/$module.lean" ]] || cp "$file" "$build/$module.lean"
  start=$(date +%s.%N)
  if ! (cd "$build" && timeout "${GENCHECK_TIMEOUT:-1800}" "$lean" -DwarningAsError=true -o "$build/$module.olean" "$module.lean") > "$build/$module.out" 2>&1; then
    end=$(date +%s.%N)
    echo "$module: compile FAILED after $(echo "$end - $start" | bc) s (timeout ${GENCHECK_TIMEOUT:-1800} s)"
    head -c 3000 "$build/$module.out"
    return 2
  fi
  end=$(date +%s.%N)
  echo "$module: compiled in $(echo "$end - $start" | bc) s"
  "$python" -B - "$build/$module.lean" "$build/${module}Audit.lean" "$module" "$lean" <<'PY'
import re, subprocess, sys
src, audit, module, lean = sys.argv[1:]
text = open(src).read()
names = re.findall(r"^theorem ([A-Za-z0-9_']+)", text, flags=re.M)
ns = re.search(r"^namespace (\S+)", text, flags=re.M).group(1)
assert names, "no theorem"
open(audit, "w").write(f"import {module}\nopen {ns}\n" + "".join(f"#print axioms {n}\n" for n in names))
out = subprocess.run([lean, audit], capture_output=True, text=True, cwd=src.rsplit("/", 1)[0])
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

status=0
for file in "$@"; do
  path="$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"
  if [[ $expect_fail == 1 ]]; then
    if audit "$path"; then echo "$file: compiled, but it was expected to FAIL" >&2; status=1
    else echo "$file: failed to compile, as expected"; fi
  else
    audit "$path" || status=1
  fi
done
[[ $status == 0 ]] && echo "gencheck.sh: passed" || echo "gencheck.sh: FAILED"
exit $status
