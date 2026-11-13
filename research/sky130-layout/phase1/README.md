# Phase 1: preparations

**Nothing of phase 1 has been launched.** No run of stage J, no run of
stage P, no layout of the cell. This folder holds what must exist before
a stage starts, by [`../PREDICTION.md`](../PREDICTION.md).

| File | What it is | Status |
|---|---|---|
| [`netlist.py`](netlist.py) | Builds the netlist of both stages from the deck of a campaign runner: sub-circuits expanded in place, device lines in their order, areas on the transistors, wire capacitances after the devices | Written, tested by the identity test |
| [`shim/ngspice`](shim/ngspice) | Stands between a campaign runner and the simulator and applies `netlist.py`. The runners of `../../circuit/` are used unchanged | Written |
| [`identity.sh`](identity.sh), [`identity_diag.sh`](identity_diag.sh), [`IDENTITY.md`](IDENTITY.md) | The identity test and its result | **Run.** Simulations of the schematic only. Passes for areas, to the byte. Does not pass to the byte once a capacitor is added: [`../AMENDMENT_1.md`](../AMENDMENT_1.md) |
| [`build_areas.py`](build_areas.py), [`areas.csv`](areas.csv) | Source and drain areas of the 232 transistors, from each device drawn alone by Magic's generator | Built. An input of stage J |
| [`j_stage.py`](j_stage.py), [`j_manifest.json`](j_manifest.json) | The six runs of stage J, their launcher, their analysis, and the hash of every input | Written. **Not launched**: the launcher refuses to start without `--go` |
| [`test_j_stage.py`](test_j_stage.py) | The analysis of stage J applied to committed results of the schematic | Passes. No simulation |

## To launch stage J, on the owner's word

```sh
cd research/circuit && sh fetch_pdk.sh        # device models, if not there yet
cd ../sky130-layout/phase1
python3 -I j_stage.py launch --go             # six runs, four at a time
python3 -I j_stage.py report                  # writes J_REPORT.md
```

Six runs of the nominal cell, 328 simulated periods. The launcher checks
`j_manifest.json` first and stops if an input has changed.

## Not prepared yet

- The layout of the cell and of its blocks: step 1 of
  [`../PHASE1_PLAN.md`](../PHASE1_PLAN.md). Not started.
- The runner and the analysis of stage P, and its manifest. They need
  the layout.
- The slowdown `f` of a stage-P netlist is still not measured.

## The areas

`areas.csv` gives each transistor the `ad`, `as`, `pd`, `ps` that Magic
extracts from a device of its size drawn alone, with one finger per
10 µm of width at most.

| Size (W / L, µm) | Fingers | `ad` = `as` (µm²) | `pd` = `ps` (µm) |
|---|---|---|---|
| 0.42 / 0.15 and 0.42 / 8 | 1 | 0.1218 | 1.42 |
| 0.84 / 0.15 | 1 | 0.2436 | 2.26 |
| 1 / 0.15 | 1 | 0.29 | 2.58 |
| 1.26 / 0.15 | 1 | 0.3654 | 3.1 |
| 2 / 0.15, 2 / 0.5, 2 / 1 | 1 | 0.58 | 4.58 |
| 4 / 1, 4 / 2 | 1 | 1.16 | 8.58 |
| 8 / 2 | 1 | 2.32 | 16.58 |
| 16 / 1, 16 / 2, 16 / 4 | 2 | 3.48 | 24.87 |
| 32 / 2 | 4 | 5.8 | 41.45 |
| 40 / 2.5 | 4 | 7.25 | 51.45 |

sha256 of `areas.csv`:
`2d89bea15524df3e317c087216a992a443b9a3b147351e99d2d675b3dbb7d17d`.
These are not the areas of a layout of the cell.
