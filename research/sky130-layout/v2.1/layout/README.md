# Layout 2.1 of one R cell

Drawn under [`../PREDICTION.md`](../PREDICTION.md), which was pushed
alone before any of it existed. **When this file was first pushed the
layout had not been extracted, and nothing of it had been simulated.**
The first and second layouts are untouched in
[`../../layout/`](../../layout/README.md) and
[`../../v2/layout/`](../../v2/layout/README.md).

```sh
cd research/sky130-layout/v2.1/layout
sh run.sh        # every block, flattened DRC, KLayout, antenna, negative controls, the estimate: about two minutes
sh run_x.sh      # the extraction and the verdicts X1 to X7: under a minute. Run once.
```

Outputs go to `build/`, not committed. Hashes: [`SHA256SUMS`](SHA256SUMS)
and [`SHA256SUMS_X`](SHA256SUMS_X). The verdicts are in
[`../X_REPORT.md`](../X_REPORT.md), written by
[`x_check.py`](x_check.py), which was committed with this file before
the extraction (commit `bb2494d`). The report is not edited.

## After the extraction

Added once the extraction was made; the rest of this file is as it was
pushed before.

- **Extracted once. The layout was not changed after.** No script was
  changed either.
- **5 hold, 2 fail.** X2, X4, X5, X6 and X7 hold: the largest
  capacitance between `x`, `vgd` or `vs` and a steering control is
  0.033 fF (1.10 fF in the second layout), and `vs` carries 7.0 fF
  (12.0 fF).
- **X1 fails again**: 0.0426 fF between `vq` and `vrefmn`, limit
  0.03 fF (0.0492 fF in the second layout). Every other loud net is
  below 0.001 fF.
- **X3 fails**: 52.3 fF on `vq`, limit 45 fF (39.7 fF). 42.1 fF of it
  go to node 0, against 29.0 fF: the top has 454 shield nodes where the
  second layout had 273. The prediction of the second layout called a
  value of X3 outside its range a limit and not a failure.
- **A likely cause of X1, read on the drawing, not tested by any run.**
  The three rows put the device that carries `vrefmn` (`xm2`) right
  under the one that carries `vq` (`xm1`): their boxes are 2.9 µm
  apart over their whole width, two gates of 4 µm facing two gates of
  4 µm. In the second layout the two were in one row with two devices
  between them. The change took `vrefmn` away from the wire of `vq`
  (10.5 µm) and brought it next to the gate of `vq`. The estimate
  could not see it: it has no polysilicon, as said below.

## What differs from the second layout

The generator is a copy of the second one. The three changes the
prediction announced, and what was added while it was drawn (the
prediction allows it: "How it is done may change while it is drawn.
What it is judged on may not."):

1. **The FIRE comparator in three rows.** The device that carries
   `vrefmn` is in the middle row. Four empty tracks were added before
   the comparator: the nearest shape of `vq` is 10.5 µm from that
   device (4.4 µm in the second layout; Magic couples up to 8 µm).
2. **Four classes of nets** ([`route.py`](route.py),
   [`floorplan.py`](floorplan.py)):

   | Class | Nets | Kept 1.4 µm from, and never over or under |
   |---|---|---|
   | critical | `vq`, the summing nodes | loud nets, `vs` |
   | protected | `x`, `vgd`, `dq`, `gm` | loud nets |
   | `vs` | `vs` | loud nets, critical nets |
   | loud | the 102 nets that swing by more than 0.5 V | critical, protected, `vs` |

   Added while drawing, not announced:
   - **`x` and `vgd` get `vss` shields**, as `vq` and the summing nodes
     do: 244 shield nodes in a port, 454 at the top. The diagnostic of
     the dose found capacitance from `x` or `vgd` to node 0 harmless.
   - **No wrapping of a gate.** Inside the waiver around a switch, a
     wire does not pass on a track next to the exit of a terminal of
     the other class; the waiver holds on metal1 and metal2 only.
   - **A cost within 8.2 µm.** A step that ends less than 8.2 µm from a
     shape of the other class, on any layer, costs up to three times
     as much.
   - **Tracks told to stay free** around the two steering switches
     (`forbid` in [`floorplan.py`](floorplan.py)): the summing node
     rises three tracks to the right of the gate of `xmsi`; `si` comes
     down on its gate from above; neither `si` nor `sd` passes over `x`.
3. **The sensor devices under the sensor plate**, in two rows, with
   the sensor comparator right below them: `vs` is a wire of about
   40 tracks (27 µm) between the comparator, the two devices and the
   plate.
   The logic that makes `si` and `sd` is in the row below, on the left;
   its outputs rise between the amplifier and the sensor devices. The
   feedback plates have a fourth exit, in column 4, for the summing
   node of `xmsi`. `xmsi` and `xmpre` are drawn turned (source and
   drain exits exchanged), as `xms1` already was.

One more change, in [`build.py`](build.py): when Magic reports a hole
of metal below the minimum area and nothing else, the hole is filled
and the block is checked again. The metal around a hole is one net. It
happened once, in the FIRE comparator.

| Check | Layout 2.1 | Second layout |
|---|---|---|
| Magic DRC, each block and the flattened cell | 0 | 0 |
| netgen LVS, each block and the cell | match, no property error | the same |
| KLayout deck | 524 reports of the same 5 rules, read as before; none of `capm.10`, `capm.2b` | 522 |
| Wide-metal spacing, asked independently | 0 | 0 |
| Antenna check of Magic | 1, not fixed | 3 |
| Negative controls | all three caught | the same |
| Size | 375.2 µm × 215.0 µm = 0.0807 mm² | 0.0836 mm² |

## What happened while it was drawn

Said so that the verdicts can be weighed.

- **A script that estimates coupling was written and used to place
  the blocks: [`estimate.py`](estimate.py).** It is not Magic and reads
  no extraction. It applies two formulas of Magic's source to the
  shapes the generator draws on metal1 to metal4: the coupling of two
  shapes that face each other on a layer, and the fringe from an edge
  to a shape of another layer beside it. It leaves out the substrate,
  polysilicon, local interconnect and the shielding of a fringe.
  Checked on the second layout, whose extraction exists: it gives
  1.56, 1.12, 1.26, 0.36 and 0.26 fF where Magic gave 1.11 (`x`–`sd`),
  0.98 (`x`–`si`), 1.10 (`vgd`–`si`), 0.25 (`vs`–`sd`) and 0.20
  (`vs`–`si`), and 0.025 where Magic gave 0.049 (`vq`–`vrefmn`, which
  goes through polysilicon). Its output for this layout is
  `build/estimate.txt`: no pair of X1, X2 or X6 above 0.035 fF.
- **The port was placed six times on that estimate, before any
  extraction.** In order:
  1. the sensor devices stacked on the gain mirror beside the
     amplifier: `sd` went round the edge of the port and closed the
     exit of `vq`; the cell could not be routed;
  2. the logic of `si` and `sd` under the sensor devices: clean, but
     `si` ran along `vs` (estimate 0.47 fF);
  3. that logic moved to the row below: `pb` ran 2.7 µm from `vs` for
     12 µm (0.23 fF); hence the cost within 8.2 µm;
  4. with that cost on the layer of the shape only, `si` crossed over
     `x` on metal3; with the summing node passing left of the gate of
     `xmsi`, `si` went round the sensor plate. Hence the cost on every
     layer, the waiver on two layers, and the tracks told to stay free;
  5. the sensor comparator moved under the sensor devices, to shorten
     `vs`;
  6. four tracks added before the FIRE comparator.
- **[`x_check.py`](x_check.py) was run once before the extraction, on
  the build folder of the second layout**, to see it run to its end. It
  gave that layout's known numbers (X1 0.0492 fF, X3 39.73 fF, X7
  11.96 fF) and wrote nothing here.
- **X7 is the one the estimate cannot answer.** It has no substrate.
  It gives 9.3 fF on `vs` here against 12.8 fF for the second layout,
  where Magic gave 12.0 fF. The limit is 10 fF.
- **The area** was below the limit of X5 at every step (0.078 to
  0.081 mm²).
- **Not done**: the antenna violation, and the reports of the KLayout
  deck, read as for the first layout (contacts inside the PDK's device
  cells; edges that touch, counted as spacing).
