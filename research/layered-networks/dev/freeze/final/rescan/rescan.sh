#!/bin/bash
# The final rescan of the exclusion list (FREEZE.txt: "The exclusion list is rescanned LAST").
#   bash rescan.sh L PY WORKDIR
# L: research/layered-networks of a clean clone (with research/circuit/pdk linked), whose FREEZE.txt holds the block;
# PY: the pinned Python; WORKDIR: a new folder outside every git tree. Run only under a push hold on the whole repo.
#
# PART 1 (THE COMMAND) is FREEZE.txt's [block second-scan], unchanged: second-scan.block.sh, byte for byte.
# PARTS 0, 2 AND 3 ARE ADDITIONS, labelled as such; none of them changes the block or its output.
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
cmp -s EXCLUDED_SECOND_SCAN.json EXCLUDED.json
python -B "$L/draw_seeds.py" print EXCLUDED.json > EXCLUDED_PRINT.txt
echo "PART 3: EXCLUDED.json $(sha256sum < EXCLUDED.json | cut -c1-64)"
echo "PART 3: EXCLUDED_PRINT.txt $(sha256sum < EXCLUDED_PRINT.txt | cut -c1-64)"
