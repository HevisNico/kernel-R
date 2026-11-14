#!/bin/sh
# Identity test of the netlist construction (simulations of the schematic; no area, no parasitic).
#   sh identity.sh          (from research/sky130-layout/phase1; MODELS as in ../checks/run.sh)
# Five runs of ../../circuit/run.py, unchanged:
#   nom_flat   nominal cell, sub-circuits expanded by netlist.py
#   nom_zero   nominal cell, expanded, every area at zero and the capacitors of identity_caps.csv at zero
#   mm_ref     seed 6002, section tt_mm, no noise, the deck of run.py as it is
#   mm_flat    the same, expanded
#   mm_zero    the same, expanded, areas and capacitors at zero
# The test passes if nom_flat and nom_zero are identical to ../../circuit/results/nom.csv and
# mm_flat and mm_zero are identical to mm_ref.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
MODELS=${MODELS:-$HERE/../../circuit/pdk}
REAL=${P1_NGSPICE:-/usr/bin/ngspice}
rm -rf "$HERE/build/identity"
one() {   # one NAME MODE SECTION [options of run.py]
    name=$1; mode=$2; section=$3; shift 3
    d="$HERE/build/identity/$name"
    mkdir -p "$d/work" "$d/results"
    cp "$HERE/../../circuit/cell.spice" "$HERE/../../circuit/blocks.spice" "$HERE/../../circuit/run.py" \
       "$HERE/../../circuit/noise.json" "$d/"
    cp "$HERE/../../circuit/spiceinit.txt" "$d/.spiceinit"
    ln -s "$MODELS" "$d/pdk"
    if [ "$mode" = ref ]; then
        (cd "$d" && python3 -I run.py cell "$name" "$section" "$@" > run.log 2>&1) || echo "$name FAILED"
    else
        (cd "$d" && PATH="$HERE/shim:$PATH" P1_HOME="$HERE" P1_NGSPICE="$REAL" P1_MODE="$mode" \
            P1_CAPS="$HERE/identity_caps.csv" python3 -I run.py cell "$name" "$section" "$@" > run.log 2>&1) || echo "$name FAILED"
    fi
}
one nom_flat flat tt &
one nom_zero zero tt &
one mm_ref ref tt_mm seed=6002 &
one mm_flat flat tt_mm seed=6002 &
wait
one mm_zero zero tt_mm seed=6002
cd "$HERE/build/identity"
ls nom_flat/work/nom_flat.spice.p1 nom_zero/work/nom_zero.spice.p1 mm_flat/work/mm_flat.spice.p1 mm_zero/work/mm_zero.spice.p1 > /dev/null
{
  cmp nom_flat/results/nom_flat.csv "$HERE/../../circuit/results/nom.csv" && echo "nom_flat: identical to research/circuit/results/nom.csv"
  cmp nom_zero/results/nom_zero.csv "$HERE/../../circuit/results/nom.csv" && echo "nom_zero: identical to research/circuit/results/nom.csv"
  cmp mm_flat/results/mm_flat.csv mm_ref/results/mm_ref.csv && echo "mm_flat: identical to mm_ref"
  cmp mm_zero/results/mm_zero.csv mm_ref/results/mm_ref.csv && echo "mm_zero: identical to mm_ref"
  cmp -s mm_ref/results/mm_ref.csv "$HERE/../../circuit/results/nom.csv" || echo "mm_ref differs from the nominal cell, as a cell with mismatch must"
} 2>&1 | tee identity.txt
sha256sum */results/*.csv | tee -a identity.txt
