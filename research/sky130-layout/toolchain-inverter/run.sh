#!/bin/sh
# The whole loop on one inverter: schematic, layout, DRC, LVS, extraction, simulation.
#   sh run.sh            (from research/sky130-layout/toolchain-inverter)
# Needs the tools of ../TOOLCHAIN.md, and the device models fetched by ../../circuit/fetch_pdk.sh
# (MODELS points at that clone). Everything is written to build/, which is not committed.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
PDK_ROOT=${PDK_ROOT:-/usr/local/share/pdk}
MODELS=${MODELS:-$HERE/../../circuit/pdk}
TECH=$PDK_ROOT/sky130A/libs.tech
MAGIC="magic -dnull -noconsole -rcfile $TECH/magic/sky130A.magicrc"
rm -rf "$HERE/build"
mkdir "$HERE/build"
cd "$HERE/build"
cp ../inv.sch ../inv_layout.tcl ../inv_drc.tcl ../inv_extract.tcl ../neg_drc.tcl ../inv_tb.py ../lyrdb_count.py .
cp ../../../circuit/spiceinit.txt .spiceinit
ln -s "$MODELS" pdk

echo "== 1. schematic netlist (xschem)"
xvfb-run -a xschem --rcfile $TECH/xschem/xschemrc -n -s -q -x \
    --tcl "set lvs_netlist 1; set netlist_dir [pwd]" -N inv_sch_raw.spice inv.sch > xschem.log 2>&1
grep -v sch_path inv_sch_raw.spice > inv_sch.spice
cat inv_sch.spice

echo "== 2. layout (Magic)"
$MAGIC inv_layout.tcl > layout.log 2>&1
grep BBOX layout.log

echo "== 3. DRC (Magic, style drc(full))"
$MAGIC inv_drc.tcl > drc.log 2>&1
grep -E "DRC_STYLE|DRC_COUNT" drc.log

echo "== 4. extraction, GDS, parasitics (Magic)"
$MAGIC inv_extract.tcl > extract.log 2>&1
ls inv_lvs.spice inv_pex_c.spice inv_pex_rc.spice inv.gds

echo "== 5. DRC of the GDS (KLayout, front-end, back-end and grid rules)"
sed 's/^FEOL    = false/FEOL    = true/' $TECH/klayout/drc/sky130A.lydrc > sky130A_feol.lydrc
grep -c "^FEOL    = true" sky130A_feol.lydrc > /dev/null
klayout -b -r sky130A_feol.lydrc -rd input=inv.gds -rd report=inv_klayout.lyrdb > klayout_drc.log 2>&1
python3 -I lyrdb_count.py inv_klayout.lyrdb

echo "== 6. LVS (netgen)"
netgen -batch lvs "inv_lvs.spice inv" "inv_sch.spice inv" $TECH/netgen/sky130A_setup.tcl inv_lvs.out > netgen.log 2>&1
grep -E "^Final result|Property errors" inv_lvs.out || true

echo "== 7. negative controls: a wrong width must fail LVS, a thin wire must fail DRC"
sed 's/W=0.42/W=0.5/' inv_sch.spice > neg_sch.spice
netgen -batch lvs "inv_lvs.spice inv" "neg_sch.spice inv" $TECH/netgen/sky130A_setup.tcl neg_lvs.out > neg_netgen.log 2>&1
grep -E "^Final result|Property errors" neg_lvs.out || true
$MAGIC neg_drc.tcl > neg_drc.log 2>&1
grep DRC_COUNT neg_drc.log
klayout -b -r sky130A_feol.lydrc -rd input=neg.gds -rd report=neg_klayout.lyrdb > neg_klayout.log 2>&1
python3 -I lyrdb_count.py neg_klayout.lyrdb

echo "== 8. simulation of the schematic and of the extracted netlists (ngspice)"
python3 -I inv_tb.py ../../../circuit/blocks.spice | tee inv_sim.csv

echo "== hashes of the outputs that carry no date (the GDS and the .mag files carry one)"
sha256sum inv_sch.spice inv_lvs.spice inv_pex_c.spice inv_pex_rc.spice inv_sim.csv | tee SHA256SUMS
