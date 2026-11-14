#!/bin/sh
# The extraction of layout 2.1 and the verdicts X1 to X7 of ../PREDICTION.md. Run once.
#   sh run_x.sh      (after sh run.sh; under a minute)      Nothing is simulated.
# Capacitance only, on the flattened cell; the plate term of the MIM capacitors taken out by a
# second extraction (../../AMENDMENT_3.md); the device floor measured on the switch drawn alone.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TECH=${PDK_ROOT:-/usr/local/share/pdk}/sky130A/libs.tech
MAGIC="magic -dnull -noconsole -rcfile $TECH/magic/sky130A.magicrc"
cd "$HERE/build"
$MAGIC ../cell_pex.tcl > cell_pex.log 2>&1
python3 -I ../pex.py rcell_pex_c.spice p_areas.csv p_caps.csv | tee pex.txt
cd "$HERE"
python3 -I plates.py build/p_caps.csv build/p_caps_primary.csv | grep -E "^PLATE" | tee build/plates.txt
cd build
$MAGIC ../floor.tcl > floor.log 2>&1
grep "^C" dev_nfet_01v8_l0p15_w1_fl.spice | tee floor.txt
cd "$HERE"
python3 -I x_check.py | tee build/x.txt
cd build
sha256sum rcell.mag rport.mag rcell_pex_c.spice rcell_np_c.spice p_areas.csv p_caps.csv p_caps_primary.csv pex.txt plates.txt floor.txt x.txt | tee SHA256SUMS_X.new
