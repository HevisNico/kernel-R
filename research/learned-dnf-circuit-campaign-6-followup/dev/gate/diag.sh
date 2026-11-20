#!/usr/bin/env bash
# Diagnostic, mine, NOT the gate: each checker's Boolean on each cascade and trace of the four gate files.
# It compiles the theory exactly as campaign 5's check.sh does (same modules, same order, warnings as errors), then
# each gate file, then one small file per gate file that evaluates the checkers one by one with #eval.
#   diag.sh        writes DIAG_<name>.lean and DIAG_<name>.out beside the gate files
set -euo pipefail
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
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
  done
)
for dose in 1x 2x; do
  for rule in frozen oneport; do
    name=Gate6_${dose}_${rule}
    cp "$here/$name.lean" "$build/$name.lean"
    if ! (cd "$build" && lean -DwarningAsError=true -o "$build/$name.olean" "$name.lean") > "$here/DIAG_$name.out" 2>&1; then
      echo "$name: the gate file itself does not compile; no diagnostic" >> "$here/DIAG_$name.out"
      continue
    fi
    {
      echo "import $name"
      echo
      echo "namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4"
      for K in K0 K3; do
        c=cascade_${dose}_$K
        t=trace_${dose}_$K
        echo
        echo "#eval (\"$name $K: conjunctions (layer 1), Disjunctions.check (layer 2), reachable\","
        echo "  checkConjunctions $c.first, $c.second.check, $c.reachable)"
        echo "#eval (\"$name $K: checkCascadeValid, checkTrainingSeparation, checkCascadeCalibrationOneSided, checks\","
        echo "  checkCascadeValid $c,"
        echo "  checkTrainingSeparation $c left right $t.observations,"
        echo "  checkCascadeCalibrationOneSided $c left right $t.observations $t.scoreAt,"
        echo "  checks $c $t)"
      done
      echo
      echo "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4"
    } > "$here/DIAG_$name.lean"
    cp "$here/DIAG_$name.lean" "$build/DIAG_$name.lean"
    (cd "$build" && lean "DIAG_$name.lean") > "$here/DIAG_$name.out" 2>&1 || echo "DIAG_$name: lean exited with an error" >> "$here/DIAG_$name.out"
  done
done
echo "diag: done"
