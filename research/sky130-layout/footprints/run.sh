#!/bin/sh
# Footprints from the device generator.   sh run.sh   (from research/sky130-layout/footprints)
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
PDK_ROOT=${PDK_ROOT:-/usr/local/share/pdk}
rm -rf "$HERE/build"
mkdir "$HERE/build"
cd "$HERE/build"
magic -dnull -noconsole -rcfile $PDK_ROOT/sky130A/libs.tech/magic/sky130A.magicrc ../footprints.tcl > magic.log 2>&1
grep -E "^FP" magic.log > footprints.txt
grep -E "^X" stk.spice > stack_overlap_devices.txt
cat footprints.txt stack_overlap_devices.txt
sha256sum footprints.txt stack_overlap_devices.txt | tee SHA256SUMS
