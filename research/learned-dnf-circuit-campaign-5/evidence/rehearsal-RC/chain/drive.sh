#!/usr/bin/env bash
# The RC chain test (PREDICTION.md 11.3) on the frozen code at 362755c, every check appended to the real checks file.
set -uo pipefail
export PATH=/home/user/lean/bin:$PATH
PY=/home/user/owner-prep/venv312/bin/python
R=/home/user/reh5; D=$R/research/learned-dnf-circuit-campaign-5
X=/home/user/c5run/rehearsal/CHECKS.jsonl
C=/home/user/c5run/chain_real
A=/home/user/c5run/collected/RC_a; B=/home/user/c5run/collected/RC_b
cd $R
[ "$(git rev-parse HEAD)" = 362755c82c79c30dc8c13eafbfa1a8b0b1203dbe ] && [ -z "$(git status --porcelain)" ] || { echo "not at 362755c or not clean"; exit 1; }
step() { echo "== $1 $(date -u +%FT%TZ)"; }
step collection; $PY -B $D/rehearsal.py check $X collection $A $B || exit 1
step rc_wall_times; $PY -B $D/rehearsal.py check $X limits $D/STAGE_RC_RUNS.json $A $B || exit 1
$PY -B $D/rehearsal.py check $X chain collection ok "collect.py once per machine on RC; the links of the stopped runs recorded as text (RC_a, RC_b: 56 files, 1 link each)"
step prediction
$PY -B $D/rehearsal.py before $C/before rc && $PY -B $D/rehearsal.py predict $C/before $C/predicted $A \
  && $PY -B $D/rehearsal.py check $X chain prediction ok "PREDICTED.json sha256 $(sha256sum $C/predicted/PREDICTED.json | cut -c1-64); Gate4.lean sha256 $(sha256sum $C/predicted/Gate4.lean | cut -c1-64)" \
  || { $PY -B $D/rehearsal.py check $X chain prediction failed; exit 1; }
step gate
if bash $D/check.sh $C/predicted/Gate4.lean > $C/check_gate.log 2>&1 && grep -q "check.sh: passed" $C/check_gate.log; then
  $PY -B $D/rehearsal.py check $X chain gate_and_check_sh ok "check.sh on the rehearsal's Gate4.lean: $(grep '^Gate4:' $C/check_gate.log)"
else $PY -B $D/rehearsal.py check $X chain gate_and_check_sh failed; exit 1; fi
step analysis
$PY -B $D/rehearsal.py check $X analysis $C/before $C/predicted $C/analysis $A $B $A $B || exit 1
$PY -B $D/rehearsal.py check $X chain analysis_with_M8 ok "analysis RESULTS.json sha256 $(sha256sum $C/analysis/RESULTS.json | cut -c1-64); M8 on the no-eligible path; check.sh on Gate4 and M8"
echo "== done $(date -u +%FT%TZ)"
