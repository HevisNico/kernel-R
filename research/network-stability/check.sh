#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"
repo=$(git rev-parse --show-toplevel)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
core="$repo/proof/lean"
dependencies=$(cd "$core" && lake env printenv LEAN_PATH)
export LEAN_PATH="$build:$core/.lake/build/lib/lean:$dependencies"
mkdir "$build/SelfCertifyingLearning"
self_certifying="$repo/research/self-certifying-learning"

# Compile the unmodified ledger with the same Lean as the new model.
(
  cd "$self_certifying"
  for module in Budget Composition; do
    lean -o "$build/SelfCertifyingLearning/$module.olean" "SelfCertifyingLearning/$module.lean"
  done
)

modules=(ChipFiring GuardedFeedback Counterexample NativeReciprocal RoutedCalendar RoutedCalendarExamples
  AutonomousFeedback FeedbackExamples PerpetualFeedback PerpetualExamples ScheduleCounterexample
  ScheduleConfluence ScheduleExamples FairMemory NetworkTheorem PortMemory FairnessExamples
  ConcreteFairness NativeEndpoint MarkFeedback MarkCounterexample NativeMarkTrace NativeRefinement)
expected=$(printf '%s\n' Audit.lean "${modules[@]/%/.lean}" | sort)
actual=$(find . -name '*.lean' -printf '%P\n' | sort)
if [[ "$expected" != "$actual" ]]; then
  diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual")
  exit 1
fi
for module in "${modules[@]}"; do
  lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
done
lean -DwarningAsError=true Audit.lean
python3 check_controls.py "$build"
