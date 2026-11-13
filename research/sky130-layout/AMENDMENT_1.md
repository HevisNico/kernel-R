# Amendment 1 to the predictions of phase 1: the identity test

Declared on 2026-11-13, before any run of stage J or stage P.
[`PREDICTION.md`](PREDICTION.md) is not edited. **This amendment is a
proposal until the owner accepts it. No stage starts before that.**

## What PREDICTION.md says

Before any run of a stage, an identity test must pass: "with all areas
and capacitances at zero, the constructed netlist gives rows identical
byte for byte to the schematic, on the nominal cell and on seed 6002
without noise. If the identity test fails, no stage starts and the plan
is rewritten."

## What the test gave

[`phase1/IDENTITY.md`](phase1/IDENTITY.md). Simulations of the
schematic, no area and no parasitic of the cell.

- Sub-circuits expanded, areas written at zero: **identical byte for
  byte**, on the nominal cell and on seed 6002.
- The same with eight capacitors of 0 F: **not identical.** 4 rows of 21
  on the nominal cell and 2 of 21 on seed 6002 differ in the last
  printed digit of a stored voltage, by 1 µV. Every FIRE, every latency
  and every count is identical.

**As worded, the test fails for any deck that holds an added capacitor,
even one of 0 F.** The wording asked for something the simulator does
not give.

## What is changed

The identity test is split in two.

| Part | Deck | Passes if | Result |
|---|---|---|---|
| **I1**, the cell is kept | Expanded, every area written at zero, no capacitor | Rows identical byte for byte, on the nominal cell and on seed 6002 without noise | **Passed** |
| **I2**, a capacitor of no charge changes nothing that is read | I1, and the capacitors of the stage at 0 F | Every FIRE flag, steering flag and count identical; every time identical; every stored voltage within 2 µV; the lowest voltage of the main capacitor within 20 µV | Passed on the eight capacitors of `phase1/identity_caps.csv`: 1 µV and 10 µV |

- **Stage J** adds areas and no capacitor. It requires I1 only. I1 has
  passed.
- **Stage P** requires I1, and I2 run again with the full list of
  extracted capacitors at 0 F, before its first run. That run shows no
  post-layout result: every capacitor is at zero.

The bounds of I2 are twice what was seen. They are fixed here, before
the list of extracted capacitors exists.

## What this changes in the reading of the results

Nothing in the predictions. One consequence for stage P: a difference of
1 or 2 µV between a post-layout stored voltage and its schematic value
is inside what an added element does by itself, and is not read as an
effect of the layout. No prediction of
[`PREDICTION.md`](PREDICTION.md) rests on a difference that small: the
narrowest, JC and L4, are 2 µV and 5 µV wide.

JC is the one to watch. Stage J has no added capacitor, so I1 applies
and the schematic rows are reproduced to the byte before the areas are
put in.
