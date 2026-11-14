# Layout 2.2 of one R cell: predictions

Written on 2026-11-14, on the owner's decision, after
[`../v2.1/X_REPORT.md`](../v2.1/X_REPORT.md),
[`../v2.1/diagnostic/X1_DIAGNOSTIC.md`](../v2.1/diagnostic/X1_DIAGNOSTIC.md)
and [`../v2.1/S_REPORT.md`](../v2.1/S_REPORT.md).

**When this file is pushed, nothing of layout 2.2 exists**: no change
to the generator, no cell, no extraction, no simulation. **It is pushed
alone, before any change**, and is not edited afterwards. The three
earlier layouts stay as they are, in their folders.

## Why a layout 2.2

| In layout 2.1 | Cause |
|---|---|
| X1 fails: 0.043 fF between `vq` and `vrefmn`, limit 0.03 fF | The FIRE comparator in three rows put its two input devices one above the other, 2.9 µm apart. All of the 0.043 fF is inside the block; the comparator of the second layout, in two rows, has none |
| X3 fails: 52.3 fF on `vq`, limit 45 fF | 42.1 fF go to node 0: the shields of `vq` and the substrate under its wire |

X2, X4, X5, X6, X7 and S1 to S5 hold on layout 2.1.

## What changes

The generator of layout 2.1, with two changes:

1. **The FIRE comparator back in the two rows of the second layout**,
   its two input devices in one row with two devices between them. The
   distance of layout 2.1 between the wire of `vq` and the device that
   carries `vrefmn` is kept: more than 8 µm.
2. **A flaw of the flow repaired**: the step that measures the plate
   term no longer writes the blocks again
   ([`../v2.1/diagnostic/X1_DIAGNOSTIC.md`](../v2.1/diagnostic/X1_DIAGNOSTIC.md)).
   It changes no shape.

How it is done may change while it is drawn. What it is judged on may
not. The script that estimates coupling from the shapes
(`estimate.py`) is used again; it has no polysilicon and could not see
the coupling of X1 in layout 2.1. **The comparator is not extracted
alone before the cell is: one extraction, once, as before.**

## Definitions

Those of [`../v2/PREDICTION.md`](../v2/PREDICTION.md) and
[`../v2.1/PREDICTION.md`](../v2.1/PREDICTION.md), unchanged: the
primary list of capacitances, the 102 loud nets, the device floor.

## X1 to X7: on the extraction alone

Judged by a script committed before the extraction is made. **After
them the work stops for the owner's review.**

| | Prediction | Layout 2.1 |
|---|---|---|
| X1 | **Tested a third time, not amended, no floor declared.** Between `vq` and each loud net at most 0.03 fF; in all at most 0.10 fF; device floor subtracted for `adm` | fails: 0.043 fF to `vrefmn` |
| X2 | As in layout 2.1: summing node to `vs` of its port at most 0.10 fF, to each other loud net at most 0.03 fF, device floor subtracted for `si` | holds: 0; 0.012 fF |
| X3 | **Redeclared.** The capacitances on `vq`, summed: at most 55 fF | 52.3 fF; fails the 45 fF of the second layout |
| X4 | As in layout 2.1: the two ports seen from `vq` within 0.1 fF | holds: 0.013 fF |
| X5 | As in layout 2.1: DRC 0, LVS match, nothing under a capacitor, at most 0.085 mm² | holds: 0.0807 mm² |
| X6 | As in layout 2.1: in each port, between `x`, `vgd` or `vs` and `si` or `sd`, at most 0.05 fF each; device floor subtracted for `x`–`sd` and `x`–`si` | holds: 0.033 fF |
| X7 | As in layout 2.1: in each port, the capacitances on `vs`, summed, at most 10 fF | holds: 7.0 fF |

**X3 is not the X3 of the second layout and of layout 2.1, and the
difference is said here, before any drawing.**

- The limit was 45 fF. Layout 2.1 has 52.3 fF and would fail it again;
  layout 2.2 probably too. The report gives the sum against both
  limits.
- What the capacitance is: of the 52.3 fF, 42.1 fF go to node 0. A
  shield is a wire of `vss` 0.34 µm from the wire of `vq`; it takes
  the coupling to the loud nets, which X1 limits to 0.03 fF, and puts
  capacitance to a node that does not move in its place. The
  prediction of the second layout already said that X3 outside its
  range is a limit and not a failure.
- What it does: it adds to the 5 pF of the main capacitor, 1.1% at
  55 fF, the same for the two ports and for every cell. It moves the
  gap of every port alike, which S3 measures: +0.0076 at 39.7 fF,
  +0.0091 at 52.3 fF. **At 55 fF the shift is about +0.0096, still
  inside S3; near 57 fF it would leave it.** The limit of 55 fF is
  where S3, which is kept, still holds.
- For the 8 cells: C1 and C2 do not depend on it; C3 makes no
  prediction above a shift of 0.004, which was already so in the
  second layout.

## S1 to S5: one nominal stage

**Not started before the owner says so.** As for layout 2.1
([`../v2.1/S_STAGE.md`](../v2.1/S_STAGE.md)): the eight nominal runs,
read the same way, with the constants of stage P.

| | Prediction | Layout 2.1 |
|---|---|---|
| S1 | The rest charge of the nominal train between 0.1 and 0.1001 | holds |
| S2 | No step of a port at rest or of a firing pulse above 0.005 mV; first silent step within 0.003 mV of the later ones | holds: 0.001 mV |
| S3 | The gap moves by −0.002 to +0.010, the two ports within 0.0005 | holds: +0.0091 |
| S4 | L1, L2, L3, L5, L6, L7 and L13 hold | holds |
| S5 | Every silent step of the nominal cell between 1.350 and 1.385 mV | holds: 1.361 mV |

## C1 to C3: the 8 cells

Those of [`../v2/PREDICTION.md`](../v2/PREDICTION.md), unchanged. **If
X1 to X7 and S1 to S5 hold on layout 2.2, the stage on the 8 cells is
confirmatory.** It starts only on the owner's word.

## Stopping rule

**If X1 fails a third time, there is no further redraw.** The stage on
the 8 cells then runs as exploratory, on the best of the layouts, with
every verdict kept as it is: X1 failed three times, nothing amended.
Which layout is the best is the owner's choice, said before that stage
starts.

## What counts against layout 2.2

- **X1 failing a third time.** It is what it is drawn for.
- **X2, X4 to X7 or S1 to S5 failing where layout 2.1 held**: a change
  that repairs one thing and breaks another.

**What is a limit and not a failure:** X3 or S3 outside its range, as
for the second layout.

## What these predictions do not say

As for the earlier layouts: nothing about silicon, matching or the
resistance of the wires; one extraction of one layout, by Magic's
rules; nominal runs without noise.
