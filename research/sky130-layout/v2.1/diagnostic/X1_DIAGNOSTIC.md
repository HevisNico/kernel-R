# Layout 2.1: where the capacitance of X1 is

**Exploratory. Not a campaign, nothing preregistered, no verdict.** It
reads [`../X_REPORT.md`](../X_REPORT.md), which is not changed: X1
fails, 0.0426 fF between `vq` and `vrefmn`, limit 0.03 fF. The layout
is not changed.

```sh
cd research/sky130-layout/v2.1/diagnostic
sh x1.sh        # after run.sh and run_x.sh in ../layout and in ../../v2/layout; seconds
```

What was run: **two extractions, no simulation.** The FIRE comparator
of each layout, the block alone, flattened and extracted as the cell is
(capacitance only, no threshold). Outputs in `build/`, not committed;
hashes in [`SHA256SUMS`](SHA256SUMS).

## The question: is 0.04 fF a floor of the devices?

**No.** The same nine devices, with the same sizes, drawn in two ways:

| FIRE comparator, alone | Between its two inputs (`vq` and `vrefmn`) | In the whole cell |
|---|---|---|
| Second layout: two rows, the two input devices in one row with two devices between them | **nothing extracted** | 0.0492 fF |
| Layout 2.1: three rows, the device of `vrefmn` right under the device of `vq` | **0.0426 fF** | 0.0426 fF |

- In the second layout the block alone has none: the 0.0492 fF came
  from outside the block, as its diagnosis said (a wire of `vq` at the
  top, 4.4 µm from the device of `vrefmn`).
- In layout 2.1 the block alone has all of it, to the last digit
  (0.04259 fF): the top adds nothing any more. **Moving the device
  away from the wire worked, and the three rows that did it put
  0.043 fF inside the block instead**: the two input devices are 2.9 µm
  apart, one above the other, over their whole width.
- So the diagnosis of the second layout was not wrong, and the remedy
  was: it removed one coupling and made another of the same size. That
  the two numbers are close is a coincidence of two different
  geometries.

The other capacitances of `vq` inside the block are the same in the two
drawings within 3%: 2.6 fF to `vdd`, 1.9 fF to `tail`, 1.7 fF to `o1m`,
0.7 fF to `vss`.

## What it says for a next layout

Not tested by any run. A comparator with the two input devices not
facing each other (the two rows of the second layout have none) and
kept more than 8 µm from the wire of `vq` at the top (as in layout 2.1)
has neither of the two couplings found so far. A floor declared
beforehand is not needed for that; whether another coupling appears is
what an extraction would say.

## A flaw of the flow found while doing this

`layout/plates.py`, the step that measures the plate term of the MIM
capacitors by a second extraction, builds the blocks again and writes
their files. It does not go through the check of `build.py`, so it
writes the FIRE comparator **without the one hole of metal1 that
`build.py` had filled** (0.34 µm × 0.155 µm). After `run_x.sh`,
`build/comp_wc16_lc4.mag` is therefore not the file of
`layout/SHA256SUMS`, and the second extraction was made on a cell that
differs from the checked one by that rectangle.

- The first extraction, the one the capacitances come from, was made
  before that step, on the checked cell.
- The second extraction is used for the plate terms only. Redone in a
  scratch copy with the fill kept: `rcell_np_c.spice` differs, and
  **the primary list is the same file, byte for byte** (sha256
  `89ba00a8…`, as in `layout/SHA256SUMS_X`). The verdicts X1 to X7 do
  not move.
- `plates.py` is left as it is, so that `run.sh` and `run_x.sh` give
  again the recorded hashes. The comparator alone gives the same
  0.04259 fF with and without the fill.
