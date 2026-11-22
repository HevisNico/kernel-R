#!/bin/bash
# The family campaign's one analysis (PREDICTION.md 9): amendment 2c sections 1-3, then amendment 2b section 4's
# declared comparison. On the analysing machine (M6). No simulation; Lean on the 15 gates. Never --no-lean.
# Fill the six SHAs (the coordinator's verified tips of evidence/function-family-campaign-M1..M6) before running.
#   bash analysis_step.sh
set -euo pipefail
TIP_M1=ca9baf56810a7fe85632c359a9e207a03f47c72f; TIP_M2=43e554fef1b217af320676d04cd8a7aa37ed3dad; TIP_M3=7e7ab4465fc190431e4bf42f2a4389968e765a2c; TIP_M4=b30588b8ae95673f5abf74bb6d0aac5c35f17102; TIP_M5=edc095d5ea75a9492ed8c9d5b674b0ca94687a8a; TIP_M6=ce29f9d729dc4796cb1d9a1fa53ad61e6b472a43
O=/home/user/owner-prep; W=$O/wt; K=/home/user/kernel-R; PY=$O/venv312-dev/bin/python
A=$O/analysis; RP=$A/RUNS_PARENT; DRV=$A/drivers
LEAN_ARCHIVE=$O/lean-dl/lean-4.35.0-linux.tar.zst; LEAN=$O/lean/lean-4.35.0-linux/bin/lean   # M6's existing extraction
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
FF=research/function-family-campaign
for s in "$TIP_M1" "$TIP_M2" "$TIP_M3" "$TIP_M4" "$TIP_M5" "$TIP_M6"; do [[ "$s" =~ ^[0-9a-f]{40}$ ]] || { echo "refused: a tip is not filled"; exit 1; }; done
test ! -e "$A" || { echo "refused: $A exists"; exit 1; }
[ "$(pgrep -c ngspice || true)" = 0 ] || { echo "refused: ngspice is running"; exit 1; }
mkdir -p "$A" "$RP" "$DRV"
exec > >(tee "$A/analysis_step.log") 2>&1
date -u +%FT%TZ

# 1. Lean 4.35.0 (2c section 3): the archive's SHA-256, then the existing bin/lean's SHA-256 and its version (no re-extraction)
test -f "$LEAN_ARCHIVE" || { echo "refused: no $LEAN_ARCHIVE"; exit 1; }
echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $LEAN_ARCHIVE" | sha256sum -c
test -x "$LEAN" || { echo "refused: no $LEAN"; exit 1; }
echo "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  $LEAN" | sha256sum -c
"$LEAN" --version | tee "$A/lean_version.txt"; grep -q "4.35.0" "$A/lean_version.txt"

# 2. the frozen tips and FREEZE.txt
for x in "ffimpl 920413ec" "ffnet 70d9d795" "campaign-6-impl ecfcd1c1" "campaign-6-followup 56f9e83e" "campaign-7-prep b956efe4" "learned-dnf-generator 4fca6256"; do
  set -- $x
  [ "$(git -C "$W/$1" rev-parse --short=8 HEAD)" = "$2" ] && [ -z "$(git -C "$W/$1" status --short)" ] || { echo "refused: $1 is not clean at $2"; exit 1; }
done
git -C "$K" fetch -q origin research/function-family-campaign-freeze
[ "$(git -C "$K" rev-parse origin/research/function-family-campaign-freeze)" = df3851b241433d3608d2e895014ed678cba3f0c1 ]
git -C "$K" show df3851b2:$FF/FREEZE.txt | grep -E "^  [0-9a-f]{64}  $FF/(net|impl)/[^ ]+$" | \
  while read -r h p; do case $p in */net/*) r=$W/ffnet;; *) r=$W/ffimpl;; esac; echo "$h  $r/$p"; done | sha256sum -c --quiet
echo "tips and FREEZE.txt: ok"

# 3. the record and the noise values, each by name at its SHA
git -C "$K" fetch -q origin evidence/function-family-campaign-predicted
[ "$(git -C "$K" rev-parse origin/evidence/function-family-campaign-predicted)" = d7e4fcc2d0fbf71c7ea90bd24ebfe389f86d37d6 ] || { echo "refused: predicted tip"; exit 1; }
git -C "$K" show d7e4fcc2:$FF/predicted/PREDICTED.json > "$A/PREDICTED.json"
echo "2849a6149ab978dc7a68f3d7e2122e783245066b7b45b47e091be4289f246482  $A/PREDICTED.json" | sha256sum -c
git -C "$K" fetch -q origin evidence/function-family-campaign-noise-values
[ "$(git -C "$K" rev-parse origin/evidence/function-family-campaign-noise-values)" = cf58f9c3dbe7fd0f234dbe60ac67f265c0062ec9 ] || { echo "refused: noise-values tip"; exit 1; }
git -C "$K" show cf58f9c3:$FF/noise-values/NOISE_VALUES.json > "$A/NOISE_VALUES.json"
echo "65145fa3fbefa31cef34da82ccd24408a872bb582385151aa54d7973d2b4380b  $A/NOISE_VALUES.json" | sha256sum -c

# 4. the six branches: fetched by name at their tips; free space measured first against 2.2 x their files
#    (the total size of the files = the sum of `git ls-tree -r -l` sizes under runs/Mn at each tip, parts included,
#    as accepted for 2c section 4; SHA256SUMS lists no sizes)
declare -A TIP=([M1]=$TIP_M1 [M2]=$TIP_M2 [M3]=$TIP_M3 [M4]=$TIP_M4 [M5]=$TIP_M5 [M6]=$TIP_M6)
total=0
for m in M1 M2 M3 M4 M5 M6; do
  br=evidence/function-family-campaign-$m
  git -C "$K" fetch -q origin "$br"
  [ "$(git -C "$K" rev-parse "origin/$br")" = "${TIP[$m]}" ] || { echo "refused: $br is not at ${TIP[$m]}"; exit 1; }
  n=$(git -C "$K" ls-tree -r -l "${TIP[$m]}" "$FF/runs/$m" | awk '{s+=$4} END {print s+0}')
  echo "$m: ${TIP[$m]}, $n bytes in its files"; total=$((total + n))
done
need=$((total * 22 / 10)); avail=$(( $(df --output=avail -B1 "$A" | tail -1) ))
echo "files $total bytes; need 2.2 x = $need; free $avail"
[ "$avail" -ge "$need" ] || { echo "refused: free space is short"; exit 1; }

#    each branch: parts joined per its PARTS files, every file checked against its SHA256SUMS files, and no file left
#    outside them. M1..M5 carry the measure sums and the network sums _QN; M6 the measure sums and _Q.
for m in M1 M2 M3 M4 M5 M6; do
  case $m in M6) EXTRA=Q;; *) EXTRA=QN;; esac
  git -C "$K" archive "${TIP[$m]}" "$FF/runs/$m" | tar -x -C "$A"
  mv "$A/$FF/runs/$m" "$RP/$m"
  ( cd "$RP/$m"
    for P in PARTS.txt PARTS_$EXTRA.txt; do
      test -f "$P" || { echo "refused: $m has no $P"; exit 1; }
      while read -r p sz n h; do
        [ -n "$p" ] || continue
        cat "$p".part-* > "$p"
        [ "$(ls "$p".part-* | wc -l)" = "$n" ] && [ "$(stat -c %s "$p")" = "$sz" ] && [ "$(sha256sum "$p" | cut -c1-64)" = "$h" ] || { echo "refused: $m $p"; exit 1; }
        rm "$p".part-*
      done < "$P"
    done
    for S in SHA256SUMS SHA256SUMS_$EXTRA; do
      test -f "$S" || { echo "refused: $m has no $S"; exit 1; }
      sha256sum -c --quiet "$S" || { echo "refused: $m does not match $S"; exit 1; }
    done
    cut -c67- SHA256SUMS SHA256SUMS_$EXTRA | sort > "$A/listed_$m.txt"
    [ -z "$(sort "$A/listed_$m.txt" | uniq -d)" ] || { echo "refused: $m lists a file twice"; exit 1; }
    find . -type f ! -name SHA256SUMS ! -name "SHA256SUMS_$EXTRA" ! -name PARTS.txt ! -name "PARTS_$EXTRA.txt" | sort > "$A/present_$m.txt"
    [ -z "$(comm -23 "$A/present_$m.txt" "$A/listed_$m.txt")" ] || { echo "refused: $m has files in no sums file:"; comm -23 "$A/present_$m.txt" "$A/listed_$m.txt"; exit 1; } )
  if [ -d "$RP/$m/drivers" ]; then mv "$RP/$m/drivers" "$DRV/$m"; fi    # checked above; kept out of RUNS_PARENT
  echo "$m: $(wc -l < "$A/listed_$m.txt") files ok"
done
rm -r "$A/research"
df -h "$A" | tail -1

# 5. RUNS.json (2c section 2)
cd "$W/ffnet/research/function-family-campaign/net"
"$PY" -B -c "
import json; from pathlib import Path
import family_net as N; N.paths('$W/campaign-6-impl')
import family_reads as R
P = Path('$A/PREDICTED.json'); rec = json.loads(P.read_text())
runs = {}
for m in ('M1', 'M2', 'M3', 'M4', 'M5', 'M6'):
    ids = [r['id'] for r in rec['network_runs'] if r['machine'] == m]
    runs.update(R.collect(ids, Path('$A/RUNS_PARENT') / m, with_rows=True, predicted=P))
assert sorted(runs) == sorted(r['id'] for r in rec['network_runs'])
Path('$A/RUNS.json').write_text(json.dumps(runs, sort_keys=True) + '\n')"
echo "RUNS.json written"

# 6. the analysis (2c section 3), never --no-lean
cd "$W/ffimpl/research/function-family-campaign/impl"
LEAN=$LEAN "$PY" -B analysis.py "$A/PREDICTED.json" "$A/RUNS.json" "$W/campaign-6-impl" "$W/learned-dnf-generator" "$A/RUNS_PARENT" > "$A/RESULTS.json"
echo "RESULTS.json written"

# 7. the declared comparison (2b section 4), counting nothing
test ! -e "$A/sensitivity"
LEAN=$LEAN "$PY" -B -c "
import json, os, sys
from pathlib import Path
assert __debug__, 'refused: not with python -O, the guards are asserts'
import family_net as N; N.paths('$W/campaign-6-impl')
import campaign_predict as CP
rec = json.loads(Path('$A/PREDICTED.json').read_text())
nv = json.loads(Path('$A/NOISE_VALUES.json').read_text())['pooled']
measured = {k: nv[k] for k in ('between_mV', 'within_mV', 'per_dose_mV')}
regen = lambda: CP.campaign('$W/campaign-6-impl', '$W/learned-dnf-generator', '$A/RUNS_PARENT', '$A/sensitivity', True, os.environ['LEAN'])
print(json.dumps(CP.noise_sensitivity(rec, regen, measured), indent=1, default=str))" > "$A/NOISE_SENSITIVITY.json"
echo "NOISE_SENSITIVITY.json written"

cd "$A" && sha256sum RESULTS.json RUNS.json NOISE_SENSITIVITY.json PREDICTED.json NOISE_VALUES.json | tee "$A/ANALYSIS_SHA256SUMS"
date -u +%FT%TZ
