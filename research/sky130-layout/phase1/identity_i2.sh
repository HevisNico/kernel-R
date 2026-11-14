#!/bin/sh
# Identity test I2 of ../AMENDMENT_1.md with the capacitor list of stage P, every value at 0 F.
#   sh identity_i2.sh     (from research/sky130-layout/phase1; MODELS as in ../checks/run.sh)
# Simulations of the schematic: every area is written at zero and every capacitor is 0 F, so no
# run shows a post-layout result. The two lists of ../AMENDMENT_3.md hold the same pairs of
# nodes; at 0 F they give the same deck, and the script checks that they do.
#   nom_i2   nominal cell, expanded, areas at zero, the 1436 capacitors at 0 F
#   mm_ref   seed 6002, section tt_mm, no noise, the deck of run.py as it is
#   mm_i2    the same cell, expanded, areas at zero, the 1436 capacitors at 0 F
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
MODELS=${MODELS:-$HERE/../../circuit/pdk}
REAL=${P1_NGSPICE:-/usr/bin/ngspice}
rm -rf "$HERE/build/i2"
one() {   # one NAME MODE SECTION [options of run.py]
    name=$1; mode=$2; section=$3; shift 3
    d="$HERE/build/i2/$name"
    mkdir -p "$d/work" "$d/results"
    cp "$HERE/../../circuit/cell.spice" "$HERE/../../circuit/blocks.spice" "$HERE/../../circuit/run.py" \
       "$HERE/../../circuit/noise.json" "$d/"
    cp "$HERE/../../circuit/spiceinit.txt" "$d/.spiceinit"
    ln -s "$MODELS" "$d/pdk"
    if [ "$mode" = ref ]; then
        (cd "$d" && python3 -I run.py cell "$name" "$section" "$@" > run.log 2>&1) || echo "$name FAILED"
    else
        (cd "$d" && PATH="$HERE/shim:$PATH" P1_HOME="$HERE" P1_NGSPICE="$REAL" P1_MODE=zero \
            P1_CAPS="$HERE/p_caps_primary.csv" python3 -I run.py cell "$name" "$section" "$@" > run.log 2>&1) || echo "$name FAILED"
    fi
}
one nom_i2 zero tt &
one mm_ref ref tt_mm seed=6002 &
one mm_i2 zero tt_mm seed=6002 &
wait
cd "$HERE/build/i2"
{
  (cd nom_i2 && python3 -I "$HERE/i2_compare.py" decks work/nom_i2.spice "$HERE/p_caps_primary.csv" "$HERE/p_caps.csv") || true
  grep -c "^cpar" nom_i2/work/nom_i2.spice.p1 | sed 's/^/capacitors of 0 F in the deck of nom_i2: /'
  python3 -I "$HERE/i2_compare.py" rows nom_i2 nom_i2/results/nom_i2.csv "$HERE/../../circuit/results/nom.csv" || true
  python3 -I "$HERE/i2_compare.py" rows mm_i2 mm_i2/results/mm_i2.csv mm_ref/results/mm_ref.csv || true
  cmp -s mm_ref/results/mm_ref.csv "$HERE/../../circuit/results/nom.csv" || echo "mm_ref differs from the nominal cell, as a cell with mismatch must"
} 2>&1 | tee i2.txt
sha256sum */results/*.csv nom_i2/work/nom_i2.spice.p1 mm_i2/work/mm_i2.spice.p1 | tee -a i2.txt
