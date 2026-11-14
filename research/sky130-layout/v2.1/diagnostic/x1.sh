#!/bin/sh
# Exploratory: the FIRE comparator of layout 2.1 and of the second layout, each drawn alone,
# flattened and extracted as the cell is. What is between its two inputs (inn is vq, inp is vrefmn)?
#   sh x1.sh      (after run.sh and run_x.sh in ../layout and in ../../v2/layout; seconds)
# Works on copies, in build/: nothing is written in the build folders of the layouts.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
TECH=${PDK_ROOT:-/usr/local/share/pdk}/sky130A/libs.tech
MAGIC="magic -dnull -noconsole -rcfile $TECH/magic/sky130A.magicrc"
cd "$HERE"
rm -rf build
for which in v2.1 v2; do
    mkdir -p build/$which
    if [ $which = v2.1 ]; then cp ../layout/build/*.mag build/$which/; else cp ../../v2/layout/build/*.mag build/$which/; fi
    (cd build/$which && BLOCK=comp_wc16_lc4 $MAGIC ../../comp_alone.tcl > comp_alone.log 2>&1)
    echo "== FIRE comparator of layout $which, alone: $(grep -c '^C' build/$which/comp_wc16_lc4_alone.spice) capacitances; on inn (vq):"
    grep '^C' build/$which/comp_wc16_lc4_alone.spice | awk '$2=="inn"||$3=="inn"' | sort -k4 -g -r
done
(cd build && sha256sum v2.1/comp_wc16_lc4.mag v2.1/comp_wc16_lc4_alone.spice v2/comp_wc16_lc4.mag v2/comp_wc16_lc4_alone.spice | tee SHA256SUMS.new)
