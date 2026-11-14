#!/bin/sh
# Extraction of the cell laid out by run.sh: capacitance only, on the flattened cell (Magic),
# then the two tables that stage P needs.   sh run_pex.sh   (after sh run.sh; a few seconds)
# Nothing is simulated.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TECH=${PDK_ROOT:-/usr/local/share/pdk}/sky130A/libs.tech
cd "$HERE/build"
magic -dnull -noconsole -rcfile $TECH/magic/sky130A.magicrc ../cell_pex.tcl > cell_pex.log 2>&1
python3 -I ../pex.py rcell_pex_c.spice p_areas.csv p_caps.csv | tee pex.txt
sha256sum rcell_pex_c.spice p_areas.csv p_caps.csv pex.txt | tee SHA256SUMS_PEX.new
