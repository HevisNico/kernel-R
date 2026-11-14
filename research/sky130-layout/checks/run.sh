#!/bin/sh
# Model checks of phase 0 (simulations).   sh run.sh   (from research/sky130-layout/checks)
# MODELS points at the clone made by ../../circuit/fetch_pdk.sh.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
MODELS=${MODELS:-$HERE/../../circuit/pdk}
rm -rf "$HERE/build"
mkdir -p "$HERE/build/circuit/work" "$HERE/build/circuit/results"
cd "$HERE/build"
cp ../mim.spice ../jleak.spice ../mm.py .
cp ../../../circuit/spiceinit.txt .spiceinit
ln -s "$MODELS" pdk

echo "== 1. MIM capacitance: m3_1 30x30, m3_2 30x30, m3_1 14.14x14.14, m3_1 10x10 (F)"
ngspice -b mim.spice 2>&1 | grep -E "^c[1-4] =" | tee mim.txt

echo "== 2. junction current of a switch at 0.4 V, at 27, 85 and 125 C (A): i0 without areas, i1 with"
ngspice -b jleak.spice 2>&1 | grep -E "^i[01] =" | tee jleak.txt

echo "== 3. mismatch sample of a seed after changes of the netlist"
python3 -I mm.py | tee mm.csv

echo "== 4. the nominal cell of the circuit study, run again with this installation"
cd circuit
cp ../../../../circuit/cell.spice ../../../../circuit/blocks.spice ../../../../circuit/run.py ../../../../circuit/noise.json .
cp ../../../../circuit/spiceinit.txt .spiceinit
ln -s "$MODELS" pdk
START=$(date +%s)
python3 -I run.py cell nom tt
echo "wall time $(( $(date +%s) - START )) s"
cmp results/nom.csv ../../../../circuit/results/nom.csv && echo "nom.csv is identical to research/circuit/results/nom.csv"
cd ..
sha256sum mim.txt jleak.txt mm.csv circuit/results/nom.csv | tee SHA256SUMS
