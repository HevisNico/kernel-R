#!/bin/bash
# The family campaign's prediction record (PREDICTION.md 3), on M6. No simulation; Lean on the 15 gates.
# Fill the six SHAs (the coordinator's verified tips of evidence/function-family-campaign-M1..M6) before running.
#   bash predict_step.sh
set -euo pipefail
SHA_M1=801c251ff0f25c69dbd5f47110fb2ee0dde062c2
SHA_M2=dff5c14b4e12ae34c46763a45d21859af3e3d71f; SHA_M3=a1d1aaa082e7ff995f4bc9e1d16f3f001ca100b7; SHA_M4=295b235104cb95877548f8b3be4bd4af503d420d; SHA_M5=57b58f16ec074f03b5cb99410feba00a97b32d31; SHA_M6=59d9964cbfe53691bbb21fe0f5e64c98a93b1d7f
O=/home/user/owner-prep; W=$O/wt; K=/home/user/kernel-R; PY=$O/venv312-dev/bin/python
A=$O/predicted-step; RP=$A/RUNS_PARENT
LEAN_ARCHIVE=$O/lean-dl/lean-4.35.0-linux.tar.zst; LEAN=$O/lean/lean-4.35.0-linux/bin/lean
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
for s in "$SHA_M2" "$SHA_M3" "$SHA_M4" "$SHA_M5" "$SHA_M6"; do [ "$s" != __FILL__ ] || { echo "refused: a SHA is not filled"; exit 1; }; done
test ! -e "$A" || { echo "refused: $A exists"; exit 1; }
mkdir -p "$A" "$RP"
exec > >(tee "$A/predict_step.log") 2>&1
date -u +%FT%TZ

# 1a. Lean 4.35.0, checked: the archive's SHA-256 BEFORE extraction, then bin/lean and its version
if [ ! -x "$LEAN" ]; then
  test -f "$LEAN_ARCHIVE" || { echo "refused: put the v4.35.0 release archive lean-4.35.0-linux.tar.zst at $LEAN_ARCHIVE"; exit 1; }
  echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $LEAN_ARCHIVE" | sha256sum -c
  command -v zstd >/dev/null || { echo "refused: zstd is missing (apt-get install -y zstd)"; exit 1; }
  tar --zstd -xf "$LEAN_ARCHIVE" -C "$O/lean"
fi
echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $LEAN_ARCHIVE" | sha256sum -c
echo "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  $LEAN" | sha256sum -c
"$LEAN" --version | tee "$A/lean_version.txt"; grep -q "4.35.0" "$A/lean_version.txt"

# 1b. the frozen tips and FREEZE.txt
for x in "ffimpl 920413ec" "ffnet 70d9d795" "campaign-6-impl ecfcd1c1" "campaign-6-followup 56f9e83e" "campaign-7-prep b956efe4" "learned-dnf-generator 4fca6256"; do
  set -- $x
  [ "$(git -C "$W/$1" rev-parse --short=8 HEAD)" = "$2" ] && [ -z "$(git -C "$W/$1" status --short)" ] || { echo "refused: $1 is not clean at $2"; exit 1; }
done
git -C "$K" fetch -q origin research/function-family-campaign-freeze
[ "$(git -C "$K" rev-parse origin/research/function-family-campaign-freeze)" = df3851b241433d3608d2e895014ed678cba3f0c1 ]
git -C "$K" show df3851b2:research/function-family-campaign/FREEZE.txt | grep -E "^  [0-9a-f]{64}  research/function-family-campaign/(net|impl)/[^ ]+$" | \
  while read -r h p; do case $p in */net/*) r=$W/ffnet;; *) r=$W/ffimpl;; esac; echo "$h  $r/$p"; done | sha256sum -c --quiet
echo "tips and FREEZE.txt: ok"

# 2. the six measure branches, by name at their SHAs, joined and checked, in amendment 2c's RUNS_PARENT layout
declare -A SHA=([M1]=$SHA_M1 [M2]=$SHA_M2 [M3]=$SHA_M3 [M4]=$SHA_M4 [M5]=$SHA_M5 [M6]=$SHA_M6)
for m in M1 M2 M3 M4 M5 M6; do
  br=evidence/function-family-campaign-$m
  git -C "$K" fetch -q origin "$br"
  [ "$(git -C "$K" rev-parse "origin/$br")" = "${SHA[$m]}" ] || { echo "refused: $br is not at ${SHA[$m]}"; exit 1; }
  git -C "$K" archive "${SHA[$m]}" "research/function-family-campaign/runs/$m" | tar -x -C "$A"
  mv "$A/research/function-family-campaign/runs/$m" "$RP/$m"
  ( cd "$RP/$m"
    while read -r p sz n h; do
      [ -n "$p" ] || continue
      cat "$p".part-* > "$p"
      [ "$(ls "$p".part-* | wc -l)" = "$n" ] && [ "$(stat -c %s "$p")" = "$sz" ] && [ "$(sha256sum "$p" | cut -c1-64)" = "$h" ] || { echo "refused: $m $p"; exit 1; }
      rm "$p".part-*
    done < PARTS.txt
    sha256sum -c --quiet SHA256SUMS ) || { echo "refused: $m does not match its SHA256SUMS"; exit 1; }
  echo "$m: $(wc -l < "$RP/$m/SHA256SUMS") files ok"
done
rmdir -p "$A/research/function-family-campaign/runs" 2>/dev/null || true
df -h "$A" | tail -1

# 3. the record, with its Lean gates (never --no-lean)
cd "$W/ffimpl/research/function-family-campaign/impl"
LEAN=$LEAN "$PY" -B campaign_predict.py campaign "$W/campaign-6-impl" "$W/learned-dnf-generator" "$RP" "$A/predicted" | tee "$A/eligibility.json"
cd "$A/predicted" && sha256sum PREDICTED.json Family_*.lean Family_*.log | tee "$A/PREDICTED_SHA256SUMS"
date -u +%FT%TZ
