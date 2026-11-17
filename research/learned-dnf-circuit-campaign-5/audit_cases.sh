#!/usr/bin/env bash
# Campaign 5 (campaign 4's audit_cases.sh at 093995b, adapted to campaign 5's folders): the cases of check.sh's audit
# (the subset rule, PREDICTION.md 7.3).
#
# Each negative case is a file of audit-cases/, written by hand and never by the campaign code, whose theorem rests on
# an axiom outside [propext, Classical.choice, Quot.sound] with no forbidden token in its text. check.sh must refuse
# each one on the axiom check, not on the token filter. The positive cases (a theorem on no axiom: M8's
# no_eligible_instance; and M8's eligible path) run in check.sh's own step of the CI.
#
# Also: no campaign Lean file committed (the gate cases, their targets, the mirror mutations, the rehearsal's gate and
# M8) contains any construct these cases use.
set -uo pipefail
cd "$(dirname "$0")"
here=$PWD
fail() { echo "audit cases: $*" >&2; exit 1; }

expect_refused() {   # case name, the axiom expected in the refusal, check.sh's arguments
  local name=$1 axiom=$2 out
  shift 2
  if out=$(bash "$here/check.sh" "$@" 2>&1); then fail "$name passed check.sh"; fi
  if grep -q "forbidden token" <<<"$out"; then fail "$name was refused by the token filter, not the axiom check"; fi
  grep -qF "AssertionError: ('" <<<"$out" && grep -qF "'$axiom'" <<<"$out" ||
    fail "$name was not refused by the axiom check: $(tail -n 3 <<<"$out")"
  echo "$name: refused by the axiom check, on $axiom"
}

expect_refused NegNative NativeTest.four_native._native.native_decide.ax_1_1 "$here/audit-cases/NativeDecl.lean" "$here/audit-cases/NegNative.lean"
expect_refused NegSorry sorryAx "$here/audit-cases/NegSorry.lean"
expect_refused NegOwnAxiom OwnAxiomTest.own_false "$here/audit-cases/OwnAxiomDecl.lean" "$here/audit-cases/NegOwnAxiom.lean"

campaign=$(find expected drafts/prerun -name '*.lean' -not -path '*/audit-cases/*' | sort)
[[ -n "$campaign" ]] || fail "no campaign Lean file found"
if grep -nE 'run_cmd|addDecl|axiomDecl|sorryAx|warningAsError|_native|trustCompiler|ofReduceBool|^import Lean$' $campaign; then
  fail "a campaign Lean file uses a construct of the negative cases"
fi
echo "audit cases: passed ($(wc -w <<<"$campaign") campaign Lean files free of the constructs of the negative cases)"
