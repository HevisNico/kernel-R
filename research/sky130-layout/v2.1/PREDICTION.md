# Layout 2.1 of one R cell: predictions

Written on 2026-11-14, on the owner's go, after
[`../v2/X_REPORT.md`](../v2/X_REPORT.md),
[`../v2/S_REPORT.md`](../v2/S_REPORT.md) and
[`../v2/diagnostic/DOSE_DIAGNOSTIC.md`](../v2/diagnostic/DOSE_DIAGNOSTIC.md).

**When this file is pushed, nothing of layout 2.1 exists**: no change
to the generator, no cell, no extraction, no simulation. **It is pushed
alone, before any change**, and is not edited afterwards. The first and
second layouts stay as they are, in their folders.

## Why a layout 2.1

| In the second layout | Cause |
|---|---|
| X1 fails: 0.049 fF between `vq` and `vrefmn`, limit 0.03 fF | The device of the FIRE comparator that carries `vrefmn` sits under the wire of `vq`, 4.4 µm below it. Magic extracts lateral coupling up to 8 µm |
| S5 and L3 fail: a silent pulse writes 1.309 mV | 1.11 fF between `x` and the steering control `sd`, which the router laid side by side: `x` was not a protected net |

## What changes

The generator of the second layout, with three changes:

1. **The FIRE comparator**: its devices in three rows, the one that
   carries `vrefmn` in the middle row, more than 8 µm from the wire of
   `vq`.
2. **More protected nets.** `x`, `vgd`, `dq` and `gm` of each port are
   kept away from loud nets as `vq` and the summing nodes are. `vs` is
   kept away from the other loud nets, and stays loud for `vq` and the
   summing nodes.
3. **A shorter `vs`**: the sensor devices next to the capacitor array,
   under the sensor plate.

How it is done may change while it is drawn. What it is judged on may
not.

## Definitions

Those of [`../v2/PREDICTION.md`](../v2/PREDICTION.md), unchanged: the
primary list of capacitances, the 102 loud nets, the device floor
(0.035 fF between the gate exit of a switch and its source or drain
exit, subtracted where the loud net is the gate of a transistor on the
node).

## X1 to X7: on the extraction alone

Judged by a script committed before the extraction is made. **After
them the work stops for the owner's review.**

| | Prediction | Second layout |
|---|---|---|
| X1 | **Retested, not amended.** Between `vq` and each loud net at most 0.03 fF; in all at most 0.10 fF; device floor subtracted for `adm` | fails: 0.049 fF to `vrefmn` |
| X2 | As in the second layout: summing node to `vs` of its port at most 0.10 fF, to each other loud net at most 0.03 fF, device floor subtracted for `si` | holds |
| X3 | As in the second layout: the capacitances on `vq`, summed, at most 45 fF | holds: 39.7 fF |
| X4 | As in the second layout: the two ports seen from `vq` within 0.1 fF | holds |
| X5 | As in the second layout: DRC 0, LVS match, nothing under a capacitor, at most 0.085 mm² | holds: 0.0836 mm² |
| X6 | **New.** In each port, between `x`, `vgd` or `vs` and `si` or `sd`: at most 0.05 fF each. Device floor subtracted for `x`–`sd` and `x`–`si`, the two steering switches | `x`–`sd` 1.11, `x`–`si` 0.98, `vgd`–`si` 1.10, `vs`–`sd` 0.25, `vs`–`si` 0.20 fF |
| X7 | **New.** In each port, the capacitances with one end on `vs`, summed: at most 10 fF | 12.0 fF |

X7 is the weakest: much of what sits on `vs` belongs to the devices on
it and to its plate, and a shorter wire removes only the rest.

## S1 to S5: one nominal stage

**Not started before the owner says so.** The eight nominal runs of
[`../v2/S_STAGE.md`](../v2/S_STAGE.md), read the same way, with the
constants of stage P.

| | Prediction | Second layout |
|---|---|---|
| S1 | As in the second layout: the rest charge of the nominal train between 0.1 and 0.1001 | holds |
| S2 | As in the second layout: no step of a port at rest or of a firing pulse above 0.005 mV; first silent step within 0.003 mV of the later ones | holds |
| S3 | As in the second layout: the gap moves by −0.002 to +0.010, the two ports within 0.0005 | holds: +0.0076 |
| S4 | As in the second layout: L1, L2, L3, L5, L6, L7 and L13 hold | fails, by L3 |
| S5 | **Changed.** Every silent step of the nominal cell is between 1.350 and 1.385 mV | 1.309 mV |

**S5 is not the S5 of the second layout, and the difference is said
here, before any drawing.**

- The second layout predicted 1.340 to 1.365 mV, around the 1.3465 mV
  of the schematic.
- The diagnostic shows that this range is not where a layout lands once
  `x` is protected. The source and drain areas alone give 1.349 mV, and
  each femtofarad on `vs` adds 0.0033 mV. With 6 to 10 fF on `vs`, the
  sum is 1.364 to 1.377 mV, less about 0.005 mV for the other nodes.
- So the prediction is 1.350 to 1.385 mV. **By the range of the second
  layout it would probably fail on the high side.** The report gives
  the step against both ranges.
- A dose 1% to 3% above the schematic is common to every cell. The
  calibration measures it. L3 (1.33 to 1.42 mV) is unchanged.

## C1 to C3: the 8 cells

Those of [`../v2/PREDICTION.md`](../v2/PREDICTION.md), unchanged. No
cell with mismatch has been run on the second layout, and none will be
on layout 2.1 before this stage. **If X1 to X7 and S1 to S5 hold, the
stage on the 8 cells is confirmatory.** It starts only on the owner's
word.

## What counts against layout 2.1

- **X1 failing again**, or **X6 failing**: they are what it is drawn
  for.
- **S5 outside its range while X6 and X7 hold**: the arithmetic of the
  diagnostic would then not carry to a layout.
- X2 to X5 or S1 to S3 failing where the second layout held: a change
  that repairs one thing and breaks another.

## What these predictions do not say

As for the second layout: nothing about silicon, matching or the
resistance of the wires; one extraction of one layout, by Magic's
rules; nominal runs without noise.
