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
(
  cd "$repo/research/self-certifying-learning"
  for module in Budget Composition; do
    lean -DwarningAsError=true -o "$build/SelfCertifyingLearning/$module.olean" "SelfCertifyingLearning/$module.lean"
  done
)

# Only the imported stable interfaces are needed for this statement check.
(
  cd "$repo/research/network-stability"
  modules=(RoutedCalendar AutonomousFeedback PerpetualFeedback ScheduleCounterexample
    ScheduleConfluence FairMemory NetworkTheorem PortMemory MarkFeedback NativeReciprocal
    NativeEndpoint NativeMarkTrace NativeRefinement PhaseAdmission
    NativeAdmissions DatedFairness DatedReplay DatedNetwork NativeStrongStep)
  for module in "${modules[@]}"; do
    lean -DwarningAsError=true -o "$build/$module.olean" "$module.lean"
  done
)

expected=$(printf '%s\n' LaunchWave.lean NativeMultiTokenAudit.lean NativeMultiTokenMilestone.lean \
  NativeMultiTokenTarget.lean ProtectedReceipt.lean SynchronizedProduct.lean)
actual=$(find . -name '*.lean' -printf '%P\n' | sort)
if [[ "$expected" != "$actual" ]]; then
  diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual")
  exit 1
fi

lean -DwarningAsError=true -o "$build/NativeMultiTokenTarget.olean" NativeMultiTokenTarget.lean
lean -DwarningAsError=true -o "$build/NativeMultiTokenMilestone.olean" NativeMultiTokenMilestone.lean
lean -DwarningAsError=true -o "$build/SynchronizedProduct.olean" SynchronizedProduct.lean
failed=0
lean -DwarningAsError=true -o "$build/LaunchWave.olean" LaunchWave.lean || failed=1
lean -DwarningAsError=true -o "$build/ProtectedReceipt.olean" ProtectedReceipt.lean || failed=1
if ((failed)); then
  exit 1
fi
lean -DwarningAsError=true NativeMultiTokenAudit.lean
