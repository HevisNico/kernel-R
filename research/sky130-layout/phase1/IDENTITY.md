# Identity test of the netlist construction

Run on 2026-11-13, before any run of stage J or stage P of
[`../PREDICTION.md`](../PREDICTION.md). **These are simulations of the
schematic. No junction area and no parasitic of the cell is in any of
them.** They test the tool that builds the netlist, not the cell.

```sh
cd research/sky130-layout/phase1
sh identity.sh            # five runs
sh identity_diag.sh       # three more, to find which addition matters
```

Each run is `../../circuit/run.py`, unchanged. The simulator is reached
through [`shim/ngspice`](shim/ngspice), which rewrites the deck with
[`netlist.py`](netlist.py). "Expanded" means that the sub-circuits of
`cell.spice` and `blocks.spice` are written out in place, with the names
ngspice gives them.

## Result

| Run | Cell | Deck | Against | Result |
|---|---|---|---|---|
| `nom_flat` | nominal | expanded | committed `../../circuit/results/nom.csv` | **identical byte for byte** |
| `nom_zero_areas` | nominal | expanded, `ad=0 as=0 pd=0 ps=0` on each of the 232 transistors | same | **identical byte for byte** |
| `mm_ref` | seed 6002, no noise | the deck of `run.py` as it is | | the reference |
| `mm_flat` | seed 6002, no noise | expanded | `mm_ref` | **identical byte for byte** |
| `mm_zero_areas` | seed 6002, no noise | expanded, areas at zero | `mm_ref` | **identical byte for byte** |
| `nom_zero_caps` | nominal | expanded, eight capacitors of 0 F, no area | `nom.csv` | **differs** in 4 rows of 21 |
| `nom_zero` | nominal | expanded, areas at zero, the eight capacitors of 0 F | `nom.csv` | **differs**, same file as `nom_zero_caps` |
| `mm_zero` | seed 6002, no noise | expanded, areas at zero, the eight capacitors of 0 F | `mm_ref` | **differs** in 2 rows of 21 |

The eight capacitors are those of
[`identity_caps.csv`](identity_caps.csv), an arbitrary list on nodes a
layout would couple (`x1.sum`, `x1.vs`, `vq` and others), with every
value replaced by zero.

## What differs

Where a run differs, it differs in the last printed digit and nowhere
else:

| | `nom_zero` against `nom.csv` | `mm_zero` against `mm_ref` |
|---|---|---|
| Rows that differ | 4 of 21 | 2 of 21 |
| Stored voltage | 1 µV at most | 1 µV at most |
| Step, which is a difference of two stored voltages | 0.001 mV at most | 0.001 mV at most |
| Lowest voltage of the main capacitor | 10 µV at most | no difference |
| FIRE or silent, on every pulse | identical | identical |
| Every latency, entry, exit and reopen time | identical | identical |

One microvolt is 0.0007 dose
(`../../circuit/DESIGN.md`, "Resolution of the measures").

## Reading

- **The construction keeps the cell.** Expanding the sub-circuits and
  writing areas on the transistors changes nothing, to the byte, on the
  nominal cell and on a cell with mismatch. The mismatch sample of
  seed 6002 is kept.
- **A capacitor of 0 F is not nothing to the simulator.** Eight elements
  that carry no charge change the last digit of a stored voltage. The
  areas do not. The likely cause is the order in which the solver
  eliminates a matrix that has eight more entries; this was not
  investigated further.
- **Stage J adds areas and no capacitor.** For it the test passes as
  written.
- **Stage P adds capacitors.** For it the test, as
  [`../PREDICTION.md`](../PREDICTION.md) words it ("identical byte for
  byte"), **fails**, and cannot pass with any capacitor in the deck.
  [`../AMENDMENT_1.md`](../AMENDMENT_1.md) declares this before any run.

## Hashes

| Result | sha256 |
|---|---|
| `nom_flat.csv`, `nom_zero_areas.csv`, and the committed `nom.csv` | `a3dbb2cd0c72080c3a93c9dc4d614cfc7fd27635adf146fb733bd112c87e3e4c` |
| `mm_ref.csv`, `mm_flat.csv`, `mm_zero_areas.csv` | `0b2ce7756cf917ddd7a8cb823969517676ad899c83823b45378605e31d5e0126` |
| `nom_zero.csv`, `nom_zero_caps.csv` | `2abaf8dbcab2e531895867d14ab10b2efe9853078e3b118681addb51d68dc76a` |
| `mm_zero.csv` | `829d4e7d8567c2934cea3a4f9374cc799046cc88a1fdf71388b828eea2a2b54b` |

The results are in `build/identity/`, not committed.
