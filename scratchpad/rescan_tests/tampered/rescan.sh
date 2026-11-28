#!/bin/bash
# The final rescan of the exclusion list (FREEZE.txt: "The exclusion list is rescanned LAST").
#   bash rescan.sh L PY WORKDIR
# L: research/layered-networks of a clean clone (with research/circuit/pdk linked), whose FREEZE.txt holds the block;
# PY: the pinned Python; WORKDIR: a new folder outside every git tree. Run only under a push hold on the whole repo.
#
# PART 1 (THE COMMAND) is FREEZE.txt's [block second-scan], unchanged: second-scan.block.sh, byte for byte.
# PARTS 0, 0a, 0b, 2 AND 3 ARE ADDITIONS, labelled as such; none of them changes the block or its output.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
L="$1"; PY="$2"; WD="$3"
python() { "$PY" "$@"; }                         # every `python` in the block is the pinned one, as in [block vars]

# ---- PART 0 (ADDED CHECK): this script's copy of the block is FREEZE.txt's [block second-scan], byte for byte
"$PY" -B "$HERE/extract_block.py" "$L/FREEZE.txt" second-scan | cmp -s - "$HERE/second-scan.block.sh" \
  || { echo "REFUSED: second-scan.block.sh differs from [block second-scan] of $L/FREEZE.txt"; exit 1; }
echo "PART 0: second-scan.block.sh = [block second-scan] of FREEZE.txt ($(sha256sum < "$HERE/second-scan.block.sh" | cut -c1-16))"
[ ! -e "$WD" ] || { echo "REFUSED: $WD already exists"; exit 1; }
git -C "$(dirname "$WD")" rev-parse --show-toplevel >/dev/null 2>&1 && { echo "REFUSED: $WD lies inside a git work tree"; exit 1; }
mkdir "$WD"; cd "$WD"

# ---- PART 0a (ADDED CHECK): the environment check, exactly as [block vars] does it; F recorded as [block vars] does
F=$(git -C "$L" rev-parse HEAD)
echo "PART 0a: F=$F"
#      (envcheck's own exit code is not trusted either way, as in [block vars]: the verdict is ENVCHECK.json's ok,
#      so a failing envcheck still reaches [block vars]'s refusal text instead of stopping this script's set -e)
PATH=$HOME/.elan/bin:$PATH "$PY" -B "$L/envcheck_layered4.py" check > ENVCHECK.json || echo "PART 0a: envcheck exited non-zero"
python -c "import json, sys; sys.exit(0 if json.load(open('ENVCHECK.json'))['ok'] is True else 1)" && echo "envcheck ok" || { echo "REFUSED: envcheck_layered4 is not ok with $PY: stop"; false; }

# ---- PART 0b (ADDED CHECK): the clone L is clean; its HEAD recorded. The only line git status may show is the
#      untracked PDK link, matched exactly
git -C "$L" rev-parse HEAD > CLONE_HEAD.txt
echo "PART 0b: clone HEAD $(cat CLONE_HEAD.txt)"
git -C "$L" status --porcelain --untracked-files=all > CLONE_STATUS.txt
if [ -s CLONE_STATUS.txt ] && [ "$(cat CLONE_STATUS.txt)" != "?? research/circuit/pdk" ]; then
  echo "REFUSED: the clone $L is not clean:"; cat CLONE_STATUS.txt; exit 1
fi
echo "PART 0b: the clone is clean (git status: $(wc -l < CLONE_STATUS.txt) line(s), the PDK link only)"

# ---- PART 1 (THE COMMAND): [block second-scan], run as FREEZE.txt's blocks are run, in this shell
. "$HERE/second-scan.block.sh"
echo "PART 1: [block second-scan] done: EXCLUDED_SECOND_SCAN.json"

# ---- PART 2 (ADDED CHECK): origin did not move during the scan (a second ls-remote after the fetch)
git ls-remote --heads https://github.com/HevisNico/kernel-R | awk '{print $1" "$2}' | sort > SCAN_LSREMOTE_AFTER.txt
cmp -s SCAN_EXPECTED.txt SCAN_LSREMOTE_AFTER.txt \
  || { echo "REFUSED: origin moved during the scan"; diff SCAN_EXPECTED.txt SCAN_LSREMOTE_AFTER.txt | head; exit 1; }
echo "PART 2: origin unchanged from the first ls-remote to after the fetch"

# ---- PART 3 (ADDED STEP): the freeze's pinned list. EXCLUDED.json is the scan's output unedited (a byte copy);
#      EXCLUDED_PRINT.txt is draw_seeds.py print of it
cp EXCLUDED_SECOND_SCAN.json EXCLUDED.json
cmp -s EXCLUDED_SECOND_SCAN.json EXCLUDED.json \
  || { echo "REFUSED: EXCLUDED.json is not a byte copy of EXCLUDED_SECOND_SCAN.json"; exit 1; }
python -B "$L/draw_seeds.py" print EXCLUDED.json > EXCLUDED_PRINT.txt
echo "PART 3: EXCLUDED.json $(sha256sum < EXCLUDED.json | cut -c1-64)"
echo "PART 3: EXCLUDED_PRINT.txt $(sha256sum < EXCLUDED_PRINT.txt | cut -c1-64)"
