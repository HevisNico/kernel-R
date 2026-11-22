#!/bin/bash
# Amendment 2b's b, w and d, by FREEZE_NOISE.txt section 2 (research/function-family-campaign-noise-freeze at 7ad98b14),
# on M6 after M6's stage Q. No simulation. Every input is fetched by name, pinned, and checked before use.
#   bash values_step.sh
set -euo pipefail
O=/home/user/owner-prep; W=$O/wt; K=/home/user/kernel-R; PY=$O/venv312-dev/bin/python; M=M6
A=$O/noise-values; RUNS=$A/RUNS; DECKS=$A/DECKS; X=$A/extract
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
REH=research/function-family-campaign/rehearsal
PREP=research/learned-dnf-circuit-campaign-7-prep/evidence
test ! -e "$A" || { echo "refused: $A exists"; exit 1; }
python3 -c "import json; s=json.load(open('$O/campaign-runs/$M/Q/STATE.json'))['runs']; assert 'running' not in [v['status'] for v in s.values()]" || { echo "refused: $M's stage Q is not over"; exit 1; }
[ "$(pgrep -c ngspice || true)" = 0 ] || { echo "refused: ngspice is running"; exit 1; }
mkdir -p "$A" "$RUNS" "$DECKS" "$X"
exec > >(tee "$A/values_step.log") 2>&1
date -u +%FT%TZ

# 1. the frozen tips and FREEZE.txt (as predict_step.sh)
for x in "ffimpl 920413ec" "ffnet 70d9d795" "campaign-6-impl ecfcd1c1" "campaign-6-followup 56f9e83e" "campaign-7-prep b956efe4"; do
  set -- $x
  [ "$(git -C "$W/$1" rev-parse --short=8 HEAD)" = "$2" ] && [ -z "$(git -C "$W/$1" status --short)" ] || { echo "refused: $1 is not clean at $2"; exit 1; }
done
git -C "$K" fetch -q origin research/function-family-campaign-freeze
[ "$(git -C "$K" rev-parse origin/research/function-family-campaign-freeze)" = df3851b241433d3608d2e895014ed678cba3f0c1 ]
git -C "$K" show df3851b2:research/function-family-campaign/FREEZE.txt | grep -E "^  [0-9a-f]{64}  research/function-family-campaign/(net|impl)/[^ ]+$" | \
  while read -r h p; do case $p in */net/*) r=$W/ffnet;; *) r=$W/ffimpl;; esac; echo "$h  $r/$p"; done | sha256sum -c --quiet
echo "tips and FREEZE.txt: ok"

# 2. the noise code: the freeze marker, then $W/ffnoise at 7bc064e8 with its two files checked against the marker
git -C "$K" fetch -q origin research/function-family-campaign-noise-freeze
[ "$(git -C "$K" rev-parse origin/research/function-family-campaign-noise-freeze)" = 7ad98b14b66921c7a08648b7ed25fd062a3da8aa ] || { echo "refused: noise-freeze tip"; exit 1; }
git -C "$K" fetch -q origin research/function-family-campaign-noise
[ "$(git -C "$K" rev-parse origin/research/function-family-campaign-noise)" = 7bc064e88641ad084532b75f0054a0b8d5ca118c ] || { echo "refused: noise tip"; exit 1; }
if [ -e "$W/ffnoise" ]; then
  [ "$(git -C "$W/ffnoise" rev-parse HEAD)" = 7bc064e88641ad084532b75f0054a0b8d5ca118c ] && [ -z "$(git -C "$W/ffnoise" status --short)" ] || { echo "refused: $W/ffnoise is not clean at 7bc064e8"; exit 1; }
else
  git -C "$K" worktree add --detach "$W/ffnoise" 7bc064e88641ad084532b75f0054a0b8d5ca118c
fi
echo "d7cc5078ee5d77a343a1c6642a289e996ccb431f1d6142eaf9995b19d14f02f7  -" > "$A/freeze_noise.sum"
git -C "$K" show 7ad98b14:research/function-family-campaign/FREEZE_NOISE.txt | sha256sum -c "$A/freeze_noise.sum"
git -C "$K" show 7ad98b14:research/function-family-campaign/FREEZE_NOISE.txt | grep -E "^  [0-9a-f]{64}  research/function-family-campaign/noise/(noise_constants|test_noise_constants)\.py$" | \
  awk '{print $1"  '"$W/ffnoise"'/"$2}' | tee "$A/noise_code.sums" | sha256sum -c
[ "$(wc -l < "$A/noise_code.sums")" = 2 ]
grep -q "^a704b8909dfe06560cab53583ae0e58356f7cf59825e5191b9a343cfae45ca9a " "$A/noise_code.sums"
grep -q "^6c4eabb314a07e35ff0ec79d5e8631624a12273c9efdd9a99a203937ca0e2323 " "$A/noise_code.sums"
echo "noise code: ok"

# 3. the rehearsal record, checked against RECORD_SHA256SUMS and the pinned SHA-256
git -C "$K" fetch -q origin evidence/function-family-campaign-rehearsal
[ "$(git -C "$K" rev-parse origin/evidence/function-family-campaign-rehearsal)" = a82c3c659b39aeb513164dd00fd1e025ea87d5b4 ] || { echo "refused: rehearsal tip"; exit 1; }
git -C "$K" show a82c3c65:$REH/record/PREDICTED.json > "$A/PREDICTED.json"
git -C "$K" show a82c3c65:$REH/RECORD_SHA256SUMS | grep "  PREDICTED.json$" | (cd "$A" && sha256sum -c)
echo "c02057d38fe6119d4fa5cac50a82ab7063c34546cb2e11265c93b6e1a73c15cb  $A/PREDICTED.json" | sha256sum -c

# 4. the runs. Per machine: its branch by name at its SHA, only the listed run folders and the stage's STATE.json
#    extracted, parts joined per PARTS.txt, every extracted file checked against the machine's own SHA256SUMS (and
#    every SHA256SUMS line of those paths present). RUNS/<id>/ is the run; RUNS/<Mn>/STATE.json the machine's state.
take_runs() {   # machine-folder branch sha commit stage id...
  local mf=$1 br=$2 sha=$3 c=$4 st=$5; shift 5
  local src=$REH/runs/$mf d=$X/$mf
  git -C "$K" fetch -q origin "$br"
  [ "$(git -C "$K" rev-parse "origin/$br")" = "$sha" ] || { echo "refused: $br is not at $sha"; exit 1; }
  mkdir -p "$d"
  git -C "$K" archive "$c" "$src/SHA256SUMS" "$src/PARTS.txt" "$src/$st/STATE.json" $(for id in "$@"; do echo "$src/$id"; done) | tar -x -C "$d" --strip-components=5
  ( cd "$d"
    while read -r p sz n h; do
      [ -n "$p" ] && [ -e "$p.part-000" ] || continue
      cat "$p".part-* > "$p"
      [ "$(ls "$p".part-* | wc -l)" = "$n" ] && [ "$(stat -c %s "$p")" = "$sz" ] && [ "$(sha256sum "$p" | cut -c1-64)" = "$h" ] || { echo "refused: $mf $p"; exit 1; }
      rm "$p".part-*
    done < PARTS.txt
    pat="^[0-9a-f]{64}  \./($(IFS='|'; echo "$*")|$st/STATE\.json)(/|$)"
    grep -E "$pat" SHA256SUMS > SUMS.used
    sha256sum -c --quiet SUMS.used || { echo "refused: $mf does not match its SHA256SUMS"; exit 1; }
    [ "$(find "$@" "$st/STATE.json" -type f | wc -l)" = "$(wc -l < SUMS.used)" ] || { echo "refused: $mf has files outside its SHA256SUMS"; exit 1; } )
  for id in "$@"; do test ! -e "$RUNS/$id"; mv "$d/$id" "$RUNS/$id"; done
  mkdir "$RUNS/${mf%-extra}"; mv "$d/$st/STATE.json" "$RUNS/${mf%-extra}/STATE.json"
  echo "$mf: $* and $st/STATE.json ok ($(wc -l < "$d/SUMS.used") files)"
}
take_runs M1 evidence/function-family-campaign-rehearsal-M1 6071b93b2a22296f99d67c83a910540e03685d9a 6071b93b2a22296f99d67c83a910540e03685d9a R-N 8303-F2-r1 8303-F2-r2
take_runs M2 evidence/function-family-campaign-rehearsal-M2 8ab9a063ce9e83fdbf7c5bd5a19edf41f8431fbc 8ab9a063ce9e83fdbf7c5bd5a19edf41f8431fbc R-N 8303-F2-r3 8303-F2-r4
take_runs M3 evidence/function-family-campaign-rehearsal-M3 d800c72016dc86e5c056ed5d84cf889e82f28cee d800c72016dc86e5c056ed5d84cf889e82f28cee R-N 8303-F2-quiet 8306-F2-r1 8306-F2-r2
take_runs M4 evidence/function-family-campaign-rehearsal-M4 dbe8928f9b4029aefb9442bffbe4d0e738a644ff dbe8928f9b4029aefb9442bffbe4d0e738a644ff R-N 8306-F2-r3 8306-F2-r4
# M5: the run's own commit e85e4aa5, the parent of the tip 8c9fa1e8, which adds only machine/ files
git -C "$K" fetch -q origin evidence/function-family-campaign-rehearsal-M5
[ "$(git -C "$K" rev-parse 8c9fa1e890c655fb958a3ed6aaa8f2ff71be3f5a^)" = e85e4aa5fbdecbcdb6a49ca5036fbbc4d6e102e1 ]
[ -z "$(git -C "$K" diff --name-only e85e4aa5 8c9fa1e8 | grep -v "^$REH/runs/M5-extra/machine/")" ] || { echo "refused: 8c9fa1e8 changes more than machine/"; exit 1; }
take_runs M5-extra evidence/function-family-campaign-rehearsal-M5 8c9fa1e890c655fb958a3ed6aaa8f2ff71be3f5a e85e4aa5fbdecbcdb6a49ca5036fbbc4d6e102e1 R-N-extra 8306-F2-quiet
[ "$(ls "$RUNS" | sort | tr '\n' ' ')" = "8303-F2-quiet 8303-F2-r1 8303-F2-r2 8303-F2-r3 8303-F2-r4 8306-F2-quiet 8306-F2-r1 8306-F2-r2 8306-F2-r3 8306-F2-r4 M1 M2 M3 M4 M5 " ] || { echo "refused: RUNS is not the ten runs and five states"; exit 1; }

# 5. the guard-on decks: campaign 7 prep's evidence by name at 85199862, parts per PARTS.json, every file per COLLECTED.json
git -C "$K" fetch -q origin evidence/learned-dnf-circuit-campaign-7-prep
[ "$(git -C "$K" rev-parse origin/evidence/learned-dnf-circuit-campaign-7-prep)" = 851998627373e01d052f62e40a5a630e2cf9ce00 ] || { echo "refused: prep evidence tip"; exit 1; }
for s in 8303 8306; do
  d=$X/batch-$s
  mkdir -p "$d"
  git -C "$K" archive 85199862 "$PREP/batch-$s/PARTS.json" "$PREP/batch-$s/COLLECTED.json" "$PREP/batch-$s/$s-cal-on" | tar -x -C "$d" --strip-components=4
  "$PY" -B -I - "$d" "$s-cal-on" <<'PYEOF'
import hashlib, json, os, sys
from pathlib import Path
d, deck = Path(sys.argv[1]), sys.argv[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
parts = json.loads((d / "PARTS.json").read_text())["files"]
for f, v in parts.items():
    if not f.startswith(deck + "/"):
        continue
    with open(d / f, "wb") as out:
        for x in v["parts"]:
            b = (d / x["path"]).read_bytes()
            assert len(b) == x["bytes"] and hashlib.sha256(b).hexdigest() == x["sha256"], f"refused: part {x['path']}"
            out.write(b)
    assert (d / f).stat().st_size == v["bytes"] and sha(d / f) == v["sha256"], f"refused: {f}"
    for x in v["parts"]:
        os.remove(d / x["path"])
listed = {x["path"]: x for x in json.loads((d / "COLLECTED.json").read_text())["files"] if x["path"].startswith(deck + "/")}
have = sorted(str(p.relative_to(d)) for p in (d / deck).rglob("*") if p.is_file())
assert have == sorted(listed), f"refused: {deck} files are not COLLECTED.json's: {set(have) ^ set(listed)}"
for f, x in listed.items():
    assert (d / f).stat().st_size == x["bytes"] and sha(d / f) == x["sha256"], f"refused: {f}"
print(deck, len(have), "files ok against PARTS.json and COLLECTED.json")
PYEOF
  mv "$d/$s-cal-on" "$DECKS/$s-cal-on"
done
rm -r "$X"
du -sh "$RUNS" "$DECKS"; df -h "$A" | tail -1

# 6. section 2's values. noise_constants.main reads the runs through family_reads, which needs the frozen modules'
#    folders (family_net.paths, as family_reads' own command line sets them); section 2's literal command does not
#    set them. This calls the same main with section 2's exact arguments, after N.paths, and prints as its __main__.
cd "$W/ffnoise/research/function-family-campaign/noise"
"$PY" -B -c "
import json, sys
assert __debug__, 'refused: not with python -O, the guards are asserts'
import family_net as N; N.paths('$W/campaign-6-impl')
import noise_constants as NC
print(json.dumps(NC.main(sys.argv[1:]), indent=1))" \
  "$A/PREDICTED.json" "$RUNS" "$DECKS" -- 8303-F2 8303-F2-quiet 8303-F2-r1 8303-F2-r2 8303-F2-r3 8303-F2-r4 \
  -- 8306-F2 8306-F2-quiet 8306-F2-r1 8306-F2-r2 8306-F2-r3 8306-F2-r4 > "$A/NOISE_VALUES.json"
cd "$A" && sha256sum NOISE_VALUES.json PREDICTED.json | tee "$A/NOISE_VALUES_SHA256SUMS"
date -u +%FT%TZ
