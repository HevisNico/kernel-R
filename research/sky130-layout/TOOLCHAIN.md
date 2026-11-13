# Toolchain proof: the whole loop on one inverter

Phase 0, item 1. The open-source flow was installed and run end to end on
one inverter: schematic, layout, DRC, LVS, parasitic extraction and
simulation. **No R cell was laid out.** Everything below was run on
2026-11-13 on one machine (Ubuntu 24.04.5, x86-64, 4 cores).

## Versions

| Tool | Version | Source | Commit or package |
|---|---|---|---|
| ngspice | 42 | Ubuntu package | `42+ds-3build1`; `/usr/bin/ngspice` sha256 `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`, the hash recorded in `../circuit/certification/manifest.json` |
| Magic | 8.3.700 | built from source | `f790f2f1ec35f422cd9512cd2570be3f6e87020d` |
| netgen | 1.5.328 | built from source | `9a0fb6faec499be5489fd0d429cd3fdc8a16d4c1` |
| xschem | 3.4.7 | built from source | `92dd8fe5f4d5c1057489710d8a22f18fdc9d7ed0` |
| KLayout | 0.28.16 | Ubuntu package | `0.28.16-0ubuntu0.24.04.1` |
| open_pdks | 1.0.556 | built from source, variant sky130A | `dd64ab492bca7e7a93f5a673351a239e87697ebc` |
| sky130_fd_pr (device models, device layouts) | | the repository and commit of `../circuit/fetch_pdk.sh` | `1232782c1b9fab3aacda74d67ce7c92bf7da8105` |
| xschem_sky130 (symbols) | | cloned by the open_pdks build | `2bfd7d654e12492d47986b78e68bb770e633b5da` |
| klayout_sky130 (DRC deck) | | cloned by the open_pdks build | `4ea0975391feacbdac697bf07029d8908d292613` |

Build tools: gcc 13.3.0, Tcl/Tk 8.6.14, Python 3.13.

**Same PDK version as the campaigns.** open_pdks 1.0.556 names
`1232782c…` as its reference commit of `sky130_fd_pr`
(`sky130/sky130.json`). The installed PDK was built from a clone of
`efabless/skywater-pdk-libs-sky130_fd_pr` at that commit, and its
`.config/nodeinfo.json` records it. The simulations of this folder read
the models from that same clone, through `pdk/models/sky130.lib.spice`,
as the campaigns do. Magic's technology file, the device generator, the
netgen setup and the KLayout deck come from open_pdks, not from
`sky130_fd_pr`.

## Installation commands

As run, as root, on a fresh Ubuntu 24.04 container.

```sh
apt-get update
apt-get install -y --no-install-recommends ngspice klayout build-essential m4 tcsh \
    tcl-dev tk-dev libcairo2-dev libx11-dev libncurses-dev xvfb python3-pip python3-venv \
    libxpm-dev flex bison gawk libxrender-dev libx11-xcb-dev libxcb1-dev libjpeg-dev git

git clone --depth 1 --branch 8.3.700 https://github.com/RTimothyEdwards/magic magic-src
(cd magic-src && ./configure --prefix=/usr/local && make -j4 && make install)

git clone --depth 1 --branch 1.5.328 https://github.com/RTimothyEdwards/netgen netgen-src
(cd netgen-src && ./configure --prefix=/usr/local && make -j4 && make install)

git clone --depth 1 --branch 3.4.7 https://github.com/StefanSchippers/xschem xschem-src
(cd xschem-src && ./configure --prefix=/usr/local && make -j4 && make install)

# device models and device layouts: the repository and commit of research/circuit/fetch_pdk.sh
git clone https://github.com/efabless/skywater-pdk-libs-sky130_fd_pr fd_pr_pinned
git -C fd_pr_pinned checkout 1232782c1b9fab3aacda74d67ce7c92bf7da8105

git clone --depth 1 --branch 1.0.556 https://github.com/RTimothyEdwards/open_pdks open_pdks
cd open_pdks
./configure --enable-sky130-pdk --with-sky130-variants=A \
    --enable-primitive-sky130=$PWD/../fd_pr_pinned \
    --enable-xschem-sky130 --enable-klayout-sky130 \
    --disable-io-sky130 --disable-sc-hs-sky130 --disable-sc-ms-sky130 --disable-sc-ls-sky130 \
    --disable-sc-lp-sky130 --disable-sc-hd-sky130 --disable-sc-hdll-sky130 --disable-sc-hvl-sky130 \
    --disable-alpha-sky130 --disable-precheck-sky130 --disable-sram-sky130 \
    --disable-sram-space-sky130 --disable-reram-sky130 \
    --disable-osu-t12-sky130 --disable-osu-t15-sky130 --disable-osu-t18-sky130
make -j4 && make install          # installs /usr/local/share/pdk/sky130A, 108 MB
```

Only the primitive library is installed: no standard cells, no I/O
cells. The PDK build takes about ten minutes on four cores.

The symbol library and the KLayout deck were cloned by the build at the
head of their repositories; the commits it took are in the table. To
pin them, clone them at those commits and give their paths to
`--enable-xschem-sky130=` and `--enable-klayout-sky130=`. The build was
not rerun in that form.

## What failed on the way

Reported as it happened. Each line cost one retry.

| What | Result | What was done |
|---|---|---|
| Prebuilt PDK through `ciel` 3.2.0 (`pip install ciel`) | The network policy of this machine refuses `fossi-foundation.github.io` (HTTP 403). Not retried, not bypassed | The PDK was built from the open_pdks sources instead. On a machine without that restriction `ciel` may work; it was not tested |
| First open_pdks build with `--enable-primitive-sky130` and no path | The build cloned `fossi-foundation/skywater-pdk-libs-sky130_fd_pr` at its head, `29b55153…`, not at the reference commit named in `sky130.json`. That head is 16 commits after `1232782c…` and includes a rework of the Monte Carlo parameters | The installation was removed and rebuilt from a clone at `1232782c…`. `nodeinfo.json` now records that commit |
| xschem 3.4.4 from the Ubuntu package | The symbols of `xschem_sky130` use an `expr(...)` syntax that 3.4.4 writes into the netlist unevaluated | xschem 3.4.7 was built from source. The package is not in the commands above |
| Magic 8.3.105 and netgen 1.5.133 from the Ubuntu packages | Not tried: they date from 2020 | Both were built from source |
| Magic device generator in batch mode (`-dnull`) | `magic::gencell` draws the device but places its instance at the cursor box, which batch mode does not move as expected | The layout script deletes that instance and places the generated cell with `getcell` at stated coordinates (`toolchain-inverter/inv_layout.tcl`) |
| First DRC of the inverter | 4 errors on local interconnect | The device cells had not been written to disk (`save` writes one cell). With `writeall force` the count is 0. The errors were of the reading, not of the layout |
| GDS file | Not the same bytes from one run to the next, even with `gds datestamp no` | The GDS is not in the list of hashes. The netlists and the simulation table are |

## The loop on the inverter

The inverter is the one of `../circuit/blocks.spice`: PMOS 1 µm / 0.15 µm,
NMOS 0.42 µm / 0.15 µm. The cell has 27 of them.

```sh
cd research/circuit && sh fetch_pdk.sh          # the device models, if not there yet
cd ../sky130-layout/toolchain-inverter && sh run.sh
```

`run.sh` writes everything to `build/`, which is not committed.

| Step | Tool | Input | Result |
|---|---|---|---|
| 1. Schematic and its netlist | xschem | [`inv.sch`](toolchain-inverter/inv.sch) | `inv_sch.spice`: two devices, four pins |
| 2. Layout | Magic, device generator and painted wires | [`inv_layout.tcl`](toolchain-inverter/inv_layout.tcl) | 2.355 µm × 5.125 µm, 12.1 µm², each device in its own guard ring |
| 3. DRC | Magic, style `drc(full)` | [`inv_drc.tcl`](toolchain-inverter/inv_drc.tcl) | **0 errors** |
| 4. Extraction and GDS | Magic | [`inv_extract.tcl`](toolchain-inverter/inv_extract.tcl) | `inv_lvs.spice`, `inv.gds` |
| 5. DRC of the GDS | KLayout, deck of the PDK with the front-end rules switched on | `inv.gds` | **0 violations** |
| 6. LVS | netgen, setup of the PDK | layout netlist against schematic netlist | **"Circuits match uniquely"**, no property error |
| 7. Parasitics | Magic on the flattened cell | | `inv_pex_c.spice`: 6 capacitors. `inv_pex_rc.spice`: the same and 3 resistors |
| 8. Simulation | ngspice 42, models of `fetch_pdk.sh`, typical corner, 27 °C | [`inv_tb.py`](toolchain-inverter/inv_tb.py) | table below |

The KLayout deck of the PDK ships with its front-end rules off
(`FEOL = false`). `run.sh` switches them on in a copy.

**Negative controls.** A tool that never complains proves nothing, so
two errors were planted:

- NMOS width 0.5 µm in the schematic netlist instead of 0.42 µm: netgen
  still prints "Circuits match uniquely", and adds **"Property errors
  were found"**. A clean LVS therefore means both: a unique match and no
  property error.
- A metal-1 wire 0.10 µm wide, below the minimum of 0.14 µm: Magic
  reports 1 error, KLayout reports 1 violation of rule `m1.1`.

### Simulation of the inverter (simulation, nominal)

The inverter under test is driven by a schematic inverter and loaded by
another. Typical corner, 27 °C, 1.8 V, input edges of 50 ps.

| Netlist | Fall delay | Rise delay | Energy drawn from the supply per cycle |
|---|---|---|---|
| Schematic (`blocks.spice`) | 21.8 ps | 19.6 ps | 8.31 fJ |
| Extracted, capacitance only | 33.0 ps | 30.4 ps | 13.29 fJ |
| Extracted, resistance and capacitance | 33.4 ps | 30.4 ps | 13.30 fJ |

The extracted inverter is about 50% slower and draws about 60% more
energy per cycle than the schematic one. Two things add up, and this
run does not separate them:

- the wires and the guard rings: 2.57 fF in six capacitors;
- the source and drain areas. The extracted devices carry them
  (`ad`, `as`, `pd`, `ps`). The devices of `blocks.spice` and
  `cell.spice` do not, so the campaigns of the circuit study were
  simulated with no junction capacitance. See [`RISKS.md`](RISKS.md).

This says nothing about the R cell, whose time unit is 20 µs. It shows
that the loop runs and that an extracted netlist simulates with the
models of the campaigns.

### Hashes

The GDS and the `.mag` files carry a date. The files below do not, and
came out identical on three runs. They are in
[`toolchain-inverter/SHA256SUMS`](toolchain-inverter/SHA256SUMS).

| File | sha256 |
|---|---|
| `inv_sch.spice` | `fb2923779d3d6a36a8632a1c18c70cb0a5ba08be0cc1e461d42ac016262e20f8` |
| `inv_lvs.spice` | `139a3a866b9fb1a3cf653479b9d1f9732b189c12adf957d9d57b43c8bceeaaa1` |
| `inv_pex_c.spice` | `dab3e45d3a6687dc20d44789f89da88feecbc6f281c32da4eed80d397c22b659` |
| `inv_pex_rc.spice` | `22303dff4e8558b2d8114f326d6cb120a6474bd05ac37ea7a12c6f803a075840` |
| `inv_sim.csv` | `a15eb9cf768e54116c4828fd975913c8a1f2b925c1e743b27f7ca708a62d78eb` |

## This installation reproduces the circuit study

The nominal run of the circuit study was run again with this
installation: `run.py cell nom tt`, in a copy of `cell.spice`,
`blocks.spice`, `run.py` and `noise.json`
([`checks/run.sh`](checks/run.sh), step 4). The result is **identical
byte for byte** to the committed `../circuit/results/nom.csv`
(sha256 `a3dbb2cd0c72080c3a93c9dc4d614cfc7fd27635adf146fb733bd112c87e3e4c`).
It took 91 s and 95 s on two runs, one run at a time.

## Limits of this proof

- One inverter. Two transistors, no capacitor, no resistor, no matched
  pair, no device with several fingers.
- The resistance extraction of Magic kept only the ground net of the
  inverter. On so small a cell this tests that the command runs, not
  that it is accurate.
- No antenna check, no density check and no fill were run.
- Magic's extraction is rule-based. No field solver was used, and no
  extracted value was compared with a measurement.
- xschem drew a schematic of two devices. The R cell has no xschem
  schematic: its netlists are written by hand.
