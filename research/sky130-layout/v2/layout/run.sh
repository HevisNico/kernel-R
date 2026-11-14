#!/bin/sh
# The second layout of one R cell: from the netlists of ../../../circuit to DRC, LVS and the antenna check.
#   sh run.sh            (from research/sky130-layout/v2/layout; about two minutes)
# Tools and versions: ../../TOOLCHAIN.md. MODELS points at the clone made by ../../circuit/fetch_pdk.sh.
# Everything is written to build/, which is not committed. The hashes of what must come out the
# same on another machine are in SHA256SUMS.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
MODELS=${MODELS:-$HERE/../../../circuit/pdk}
TECH=${PDK_ROOT:-/usr/local/share/pdk}/sky130A/libs.tech
MAGIC="magic -dnull -noconsole -rcfile $TECH/magic/sky130A.magicrc"
cd "$HERE"
rm -rf build
mkdir -p build/parts

echo "== 1. every block, bottom-up: Magic DRC (style drc(full)) and netgen LVS"
python3 -I build.py | tee build/blocks.txt

cd build
echo "== 2. the whole cell, flattened: Magic DRC, and the GDS"
$MAGIC ../cell_flat.tcl > cell_flat.log 2>&1
grep -E "CELL_BBOX|FLAT_DRC" cell_flat.log | tee cell_flat.txt

echo "== 3. DRC of the GDS (KLayout, deck of the PDK, front-end, back-end and grid rules)"
sed 's/^FEOL    = false/FEOL    = true/' $TECH/klayout/drc/sky130A.lydrc > sky130A_feol.lydrc
grep -c "^FEOL    = true" sky130A_feol.lydrc > /dev/null
klayout -b -r sky130A_feol.lydrc -rd input=rcell.gds -rd report=rcell_klayout.lyrdb > klayout_drc.log 2>&1
python3 -I ../lyrdb_cells.py rcell_klayout.lyrdb | tee klayout.txt
echo "== 3b. the wide-metal spacing rule, asked independently of the deck"
klayout -b -r ../wide_metal_check.py -rd input=rcell.gds 2>&1 | grep WIDE | tee wide.txt

echo "== 4. antenna check (Magic)"
$MAGIC ../cell_antenna.tcl > antenna.log 2>&1
grep -E "Antenna violation|Effective antenna ratio" antenna.log | sort | uniq -c | tee antenna.txt

echo "== 5. negative controls: each must be caught"
$MAGIC ../neg_drc.tcl > neg_drc.log 2>&1
grep NEG_DRC_COUNT neg_drc.log | tee neg.txt
sed 's/^Xx1_xop_xm5 vmem1 x1_xop_o1 /Xx1_xop_xm5 vmem1 x1_xop_o1m /' rcell_sch.spice > neg_wire.spice
netgen -batch lvs "rcell_lay.spice rcell" "neg_wire.spice rcell" $TECH/netgen/sky130A_setup.tcl neg_wire.out > /dev/null 2>&1 < /dev/null
echo "wrong connection: $(grep '^Final result' neg_wire.out | tail -1)" | tee -a neg.txt
sed 's/^\(Xx2_xmin .*\) W=40 /\1 W=36 /' rcell_sch.spice > neg_size.spice
netgen -batch lvs "rcell_lay.spice rcell" "neg_size.spice rcell" $TECH/netgen/sky130A_setup.tcl neg_size.out > /dev/null 2>&1 < /dev/null
echo "wrong width: $(grep -i 'with property errors' neg_size.out | tail -1)" | tee -a neg.txt

echo "== 6. the drawn capacitors and resistors in the pinned models (simulation of single devices)"
cd parts
cp ../../parts.spice .
cp ../../../../../circuit/spiceinit.txt .spiceinit
ln -s "$MODELS" pdk
ngspice -b parts.spice 2>&1 | grep -E "^[rc][0-9a-z]+ =" | tee ../parts.txt
cd ..

echo "== 7. hashes"
sha256sum rcell.mag rport.mag opamp.mag comp_wc4_lc1.mag comp_wc16_lc4.mag srlatch.mag nand3.mag nand2.mag inv.mag \
    dev_cfcs.mag rcell_sch.spice rcell_lay.spice blocks.txt cell_flat.txt klayout.txt wide.txt antenna.txt neg.txt parts.txt \
    | tee SHA256SUMS.new
