#!/bin/sh
# Fetch the SKY130 primitive device models at the commit used for the results.
set -e
git clone https://github.com/efabless/skywater-pdk-libs-sky130_fd_pr pdk
git -C pdk checkout 1232782c1b9fab3aacda74d67ce7c92bf7da8105
