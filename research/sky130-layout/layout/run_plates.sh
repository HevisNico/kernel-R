#!/bin/sh
# The plate term of finding F4 and the list of capacitances without it (../AMENDMENT_3.md).
#   sh run_plates.sh     (after sh run.sh and sh run_pex.sh; a few seconds)   Nothing is simulated.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE"
python3 -I plates.py build/p_caps.csv build/p_caps_primary.csv | grep -E "^PLATE" | tee build/plates.txt
cd build
sha256sum rcell_np_c.spice p_caps.csv p_caps_primary.csv plates.txt | tee SHA256SUMS_PLATES.new
