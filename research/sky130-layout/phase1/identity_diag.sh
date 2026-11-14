#!/bin/sh
# Diagnosis of the identity test: which addition changes the last printed digit?
#   sh identity_diag.sh     (after identity.sh; nominal cell, schematic, no noise)
#   nom_zero_areas   expanded, ad=0 as=0 pd=0 ps=0 written on every transistor, no capacitor
#   nom_zero_caps    expanded, the eight capacitors of identity_caps.csv at 0 F, no area written
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
MODELS=${MODELS:-$HERE/../../circuit/pdk}
REAL=${P1_NGSPICE:-/usr/bin/ngspice}
one() {
    name=$1; mode=$2; caps=$3
    d="$HERE/build/identity/$name"
    rm -rf "$d"; mkdir -p "$d/work" "$d/results"
    cp "$HERE/../../circuit/cell.spice" "$HERE/../../circuit/blocks.spice" "$HERE/../../circuit/run.py" \
       "$HERE/../../circuit/noise.json" "$d/"
    cp "$HERE/../../circuit/spiceinit.txt" "$d/.spiceinit"
    ln -s "$MODELS" "$d/pdk"
    (cd "$d" && PATH="$HERE/shim:$PATH" P1_HOME="$HERE" P1_NGSPICE="$REAL" P1_MODE="$mode" P1_CAPS="$caps" \
        python3 -I run.py cell "$name" tt > run.log 2>&1) || echo "$name FAILED"
}
one nom_zero_areas zero "" &
one nom_zero_caps zerocaps "$HERE/identity_caps.csv" &
wait
cd "$HERE/build/identity"
{
  for n in nom_zero_areas nom_zero_caps; do
    if cmp -s $n/results/$n.csv "$HERE/../../circuit/results/nom.csv"; then echo "$n: identical to research/circuit/results/nom.csv"
    else echo "$n: differs from research/circuit/results/nom.csv"; fi
  done
} | tee identity_diag.txt
sha256sum nom_zero_areas/results/*.csv nom_zero_caps/results/*.csv | tee -a identity_diag.txt

# The same question on a cell with mismatch: seed 6002, areas written at zero, no capacitor.
d="$HERE/build/identity/mm_zero_areas"
rm -rf "$d"; mkdir -p "$d/work" "$d/results"
cp "$HERE/../../circuit/cell.spice" "$HERE/../../circuit/blocks.spice" "$HERE/../../circuit/run.py" "$HERE/../../circuit/noise.json" "$d/"
cp "$HERE/../../circuit/spiceinit.txt" "$d/.spiceinit"
ln -s "$MODELS" "$d/pdk"
(cd "$d" && PATH="$HERE/shim:$PATH" P1_HOME="$HERE" P1_NGSPICE="$REAL" P1_MODE=zero P1_CAPS="" \
    python3 -I run.py cell mm_zero_areas tt_mm seed=6002 > run.log 2>&1) || echo "mm_zero_areas FAILED"
cd "$HERE/build/identity"
if cmp -s mm_zero_areas/results/mm_zero_areas.csv mm_ref/results/mm_ref.csv; then echo "mm_zero_areas: identical to mm_ref" | tee -a identity_diag.txt
else echo "mm_zero_areas: differs from mm_ref" | tee -a identity_diag.txt; fi
sha256sum mm_zero_areas/results/*.csv | tee -a identity_diag.txt
