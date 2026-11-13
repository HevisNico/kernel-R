# Layout of one R cell

Step 1 of [`../PHASE1_PLAN.md`](../PHASE1_PLAN.md). **A layout of the
cell of `../../circuit/cell.spice` exists: 232 transistors, 12
capacitors, 8 resistors, two ports and the shared parts.** It is drawn
by scripts, block by block. No simulation of the cell with its
parasitics has been made.

```sh
cd research/sky130-layout/layout && sh run.sh        # about two minutes; needs ../TOOLCHAIN.md
```

Everything is written to `build/`, not committed. The hashes of the
Magic cells, of the two LVS netlists and of every result quoted below
are in [`SHA256SUMS`](SHA256SUMS). Two runs on one machine gave the same
hashes. The GDS is not in the list: Magic does not write it byte for
byte the same twice ([`../TOOLCHAIN.md`](../TOOLCHAIN.md)).

## Result

| Check | Result |
|---|---|
| Magic DRC, style `drc(full)`, each block and the cell, also flattened | **0 errors** |
| netgen LVS, each block and the cell | **"Circuits match uniquely", no property error** |
| KLayout DRC of the GDS, deck of the PDK, front-end, back-end and grid rules on | **531 violations of 5 rules, none fixed. All are explained below; none is waived silently** |
| Antenna check of Magic | **3 violations, not fixed** |
| Size of the cell | **354.0 µm × 209.6 µm = 0.0742 mm²** |

The phase-0 estimate was 0.05 to 0.065 mm²
([`../FLOORPLAN.md`](../FLOORPLAN.md)). **The layout is 14% above its
upper end**: 37 100 µm² per port, 27 ports per mm².

## How it is drawn

| File | What it does |
|---|---|
| [`schematic.py`](schematic.py) | Reads `cell.spice` and `blocks.spice`, keeps the elements of role "cell" of `../inventory.py`, and writes the netlist that netgen compares each block with. It stops if the device list differs from the inventory: 252 devices |
| [`devices.py`](devices.py) | Each transistor and resistor is drawn by the device generator of the PDK in Magic, with its guard ring, then given exits that end on the routing grid. MIM capacitors are drawn plate by plate, with the layers the generator uses |
| [`route.py`](route.py) | Places the parts of a block in rows and routes its nets on a grid of 0.68 µm, on metal1 to metal4 |
| [`floorplan.py`](floorplan.py) | The floorplan: which part goes in which row. **The only hand-made input** |
| [`build.py`](build.py) | Builds the blocks bottom-up and checks each one before it is used in the next |
| [`tech.py`](tech.py) | Pitch, widths and spacings of the router |
| [`view.py`](view.py) | A picture of a block, for the eye |

**Nothing is drawn by hand.** No coordinate of a wire is typed: the
router finds every wire.

- The router is simple: nets one after the other, each by shortest path,
  no rip-up. Wires are 0.34 µm wide on metal1 and 0.38 µm on metal2 to
  metal4.
- A wire is kept away from the shapes of other nets by the spacing of
  its layer, so a block is DRC clean by construction; Magic then checks
  it.
- No wire runs on metal1 or metal2 under a capacitor (rule capm.10 of
  the PDK, which Magic does not check and KLayout does).

## Blocks

Each was checked alone, in this order, before the next used it.

| Block | Devices below | Nets routed at this level | Size (µm) | Magic DRC | LVS |
|---|---|---|---|---|---|
| `inv` | 2 | 4 | 2.1 × 8.6 | 0 | match |
| `nand2` | 4 | 6 | 6.9 × 9.2 | 0 | match |
| `nand3` | 6 | 8 | 11.6 × 10.6 | 0 | match |
| `srlatch` | 8 | 6 | 16.4 × 9.2 | 0 | match |
| `comp`, pair 4 / 1 | 12 | 11 | 34.6 × 21.6 | 0 | match |
| `comp`, pair 16 / 4 | 12 | 11 | 49.6 × 21.6 | 0 | match |
| `opamp`, with `rz` and `cc` | 10 | 10 | 68.8 × 30.3 | 0 | match |
| `rport`, one port | 105 | 47 | 147.3 × 208.9 | 0 | match |
| `rcell`, the cell | 252 | 48 | 354.0 × 209.6 | 0 | match |

- "match" is netgen's "Circuits match uniquely" with no property error.
- The cell: 254 devices and 149 nets on each side for netgen, after it
  merges parallel plates and resistors in series.
- The second port is the first one mirrored: the same Magic cell.

This is not the order of blocks of [`../PHASE1_PLAN.md`](../PHASE1_PLAN.md)
(logic row, comparator, op-amp, gain mirror, sensor, capacitor array,
port, shared, cell). The blocks here are those of the netlists: the
gain mirror, the sensor and the capacitor array are placed in the port
and checked with it, not alone.

## Capacitors and resistors as drawn

The simulations keep the ideal values (decision D3). What is drawn, and
its value in the pinned models (simulation of single devices, typical
corner, 27 °C: [`parts.spice`](parts.spice)):

| Part | Netlist | Drawn | Model value |
|---|---|---|---|
| `cf` | 30 pF | 75 MIM plates of 14 µm × 14 µm | 75 × 401.2 fF = 30.09 pF |
| `cs` | 400 fF | 1 plate of 14 µm × 14 µm | 401.2 fF |
| `cq` | 5 pF | 4 plates of 24.84 µm | 5.002 pF |
| `cc` | 1.5 pF | 1 plate of 27.22 µm | 1.500 pF |
| `cdp` | 2 pF | 2 plates of 22.2 µm | 2.001 pF |
| `cda`, `cdl` | 200 fF | 1 plate of 9.84 µm | 200.1 fF |
| `rleak` | 8 MΩ | 20 strips of 70 µm, 0.35 µm wide, 2 kΩ per square, in series | 8.011 MΩ |
| `rda`, `rdl`, `rdp` | 100 kΩ | 2 strips, 17.5 µm in all | 100.6 kΩ |
| `rz` | 4 kΩ | 1.41 µm wide, 2.66 µm long | 4.005 kΩ |

**The capacitor array of a port** is 9 × 9 plates on a pitch of
15.64 µm: 75 for `cf`, 1 for `cs`, 5 dummies.

- The `cf` plates share one metal3 sheet (`vmem`); their top plates are
  joined on metal4 (`sum`).
- The `cs` plate is in the middle of the bottom row, on its own bottom
  plate, with a dummy plate on each side, above it, and on the two
  diagonals above.
- A dummy plate has both plates on `vmem`. The five are in the LVS
  netlist as devices that `cell.spice` does not have; `schematic.py`
  adds them from the table of drawn parts.
- **There is no ring of dummy plates around the array.** A plate at the
  edge has no neighbour outside.

## KLayout DRC: 531 violations, by rule

Magic's deck reports none. KLayout's deck reports these; the count by
cell is in `build/klayout.txt`.

| Rule of the deck | Count | Where | Reading |
|---|---|---|---|
| `licon.1`, contact size 0.17 µm | 184 | Only inside the three resistor cells drawn by the generator of the PDK | The contacts of a poly resistor are bars of 0.19 µm × 2 µm. The deck exempts them under the implant of the 300 Ω resistor (RPM) and not under that of the 2 kΩ resistor (URPM) used here |
| `licon.7`, tap enclosure of a contact | 46 | The same contacts, the same three cells | The deck reports every contact that is not 0.17 µm wide. These are not on a tap |
| `licon.12`, source or drain wider than 5.7 µm without contact | 3 | Three transistor cells of several fingers, drawn by the generator | The deck measures the whole diffusion of the device, gates included. Each source and drain column has its column of contacts |
| `m3.3ab`, 0.4 µm to metal3 wider than 3 µm | 14 | Where a narrower piece of metal3 is attached to a wide one | The deck splits the layer into its wide part and the rest and reports the two where they touch: all 14 reports are pairs of touching edges. [`wide_metal_check.py`](wide_metal_check.py) asks the rule itself: 0 |
| `m4.5ab`, the same on metal4 | 284 | The same on metal4: the joints between the top plates of the arrays, and the exits of the plates | All 284 are pairs of touching edges. 0 by the independent check |

**What this table is and is not.**

- The first three rules are reported only inside cells that the
  generator of the PDK drew and that this work did not touch.
- For the last two, the independent check is this author's reading of
  the rule: a part wider than 3 µm, with what is attached to it within
  0.28 µm, against the other polygons of the layer. It finds none
  nearer than 0.4 µm. **It is not a sign-off.**
- A foundry deck was not run. No tape-out check was made.
- Two rules that KLayout reported on a first layout were real and were
  fixed in the generator: wires on metal1 crossing the edge of a
  capacitor (`capm.10`, 24) and metal2 under a capacitor (`capm.2b`, 5).

## Antenna check

Magic reports 3 violations, **not fixed**: two on metal1 (ratio 418,
limit 400; the same ratio twice, as two mirrored ports would give) and
one on metal4 (ratio 712).
They matter to fabrication and not to the extraction.

## Negative controls

Each must be caught, and is (`build/neg.txt`).

| Control | Result |
|---|---|
| A metal1 wire drawn 0.1 µm from another in a copy of the cell | Magic DRC: 2 errors |
| One wrong connection in the netlist (gate of `x1.xop.xm5`) | netgen: "Netlists do not match" |
| One wrong width in the netlist (`x2.xmin`, 36 µm for 40 µm) | netgen: "match uniquely with property errors" |

## What this layout is not

- **Not a matched layout.** The input pairs and the mirrors are placed
  side by side by the row placer: no common centroid, no
  interdigitation, no dummy device. The plan names the pairs as
  "matching-sensitive content"; nothing was done for them beyond
  identical devices in one orientation. The simulations do not model
  the effect of a layout on matching
  ([`../RISKS.md`](../RISKS.md), section 1).
- Not compact. Every transistor has its own guard ring, the logic
  included: a row of standard cells would be several times smaller.
- No pin is brought to the boundary. A net that must leave the cell
  (supply, references, bias, clocks, pulse currents) carries a label
  where it is.
- No supply grid: `vdd` and `vss` are routed as nets, on wires of
  0.34 to 0.38 µm.
- No metal fill, no density check, no seal ring, no pad.
- One floorplan, one run of a simple router. Another gives other
  parasitics.

## Not done yet

- The extraction of the capacitances and of the source and drain areas,
  and the netlist of stage P (step 2 of the plan).
- The run with resistance extracted.
- Nothing of stage P has been run.
