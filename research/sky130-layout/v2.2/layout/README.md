# Layout 2.2 of one R cell

Drawn under [`../PREDICTION.md`](../PREDICTION.md), which was pushed
alone before any of it existed. **When this file was first pushed the
layout had not been extracted, and nothing of it had been simulated.**
The three earlier layouts are untouched in their folders.

```sh
cd research/sky130-layout/v2.2/layout
sh run.sh        # every block, flattened DRC, KLayout, antenna, negative controls, the estimate: about two minutes
sh run_x.sh      # the extraction and the verdicts X1 to X7: under a minute. Run once.
```

Outputs go to `build/`, not committed. Hashes: [`SHA256SUMS`](SHA256SUMS)
and [`SHA256SUMS_X`](SHA256SUMS_X). The verdicts are in
[`../X_REPORT.md`](../X_REPORT.md), written by
[`x_check.py`](x_check.py), which was committed with this file before
the extraction (commit `f0a3fc9`). The report is not edited.

## After the extraction

Added once the extraction was made; the rest of this file is as it was
pushed before.

- **Extracted once. The layout was not changed after, nor any script.**
- **X1 to X7 hold.** Between `vq` and `vrefmn` Magic extracts nothing
  any more; the largest capacitance from `vq` to a loud net is
  0.0014 fF (`adm` of port 2, after its floor).
- **X3 holds its redeclared limit and not the earlier one**: 52.45 fF
  on `vq`, limit 55 fF; by the 45 fF of the earlier layouts it fails.
- After the plate step the files of the blocks are still those of
  `SHA256SUMS`: the repair of the flow holds.
- Nothing has been simulated. The nominal stage starts on the owner's
  word.

## What differs from layout 2.1

The generator is a copy of that of layout 2.1
([`../../v2.1/layout/README.md`](../../v2.1/layout/README.md)), with
the two changes the prediction announced and what they needed at the
top of the cell ([`floorplan.py`](floorplan.py)):

1. **The FIRE comparator back in the two rows of the second layout.**
   The block that comes out is the same file as in the second layout
   (`comp_wc16_lc4.mag`, sha256 `6282d72b…` in both `SHA256SUMS`). That
   block, extracted alone for the diagnostic of layout 2.1, has no
   capacitance between its two inputs.
2. **`vq` kept 8.2 µm from the device that carries `vrefmn`, by a
   rule.** At the top, no wire of `vq` may enter the box of that device
   grown by 8.2 µm, on any layer (`forbid`). Thirteen empty tracks of
   height were added above the comparator, where `vq` passes from one
   port to the other. The four tracks that layout 2.1 had before the
   comparator are gone. The nearest shape of `vq` is 13.1 µm from that
   device (4.4 µm in the second layout, 10.5 µm in layout 2.1).
3. **The flaw of the flow repaired**: [`plates.py`](plates.py) no
   longer writes the blocks again. No hole had to be filled in this
   layout.

The port is the same file as in layout 2.1 (`rport.mag`, sha256
`3821fc82…`), and so are the amplifier and the sensor comparator.

| Check | Layout 2.2 | Layout 2.1 |
|---|---|---|
| Magic DRC, each block and the flattened cell | 0 | 0 |
| netgen LVS, each block and the cell | match, no property error | the same |
| KLayout deck | 524 reports of the same 5 rules, read as before; none of `capm.10`, `capm.2b` | 524 |
| Wide-metal spacing, asked independently | 0 | 0 |
| Antenna check of Magic | 1, not fixed | 1 |
| Negative controls | all three caught | the same |
| Size | 379.3 µm × 215.0 µm = 0.0816 mm² | 0.0807 mm² |
| Shield nodes at the top | 451 | 454 |

## What happened while it was drawn

Said so that the verdicts can be weighed.

- **The cell was assembled three times before the extraction**, with
  13, 10 and 7 empty tracks above the comparator, to see whether fewer
  tracks shorten `vq`. The estimate ([`estimate.py`](estimate.py), not
  an extraction, no substrate) gives 87.1, 87.2 and 86.4 fF on `vq`
  for the three, against 85.5 fF for layout 2.1, where Magic gave
  52.3 fF. The 13 tracks were kept: they leave the most distance to
  the device of `vrefmn`. **By that ratio X3 is expected near 53 fF,
  under its limit of 55 fF by little.**
- The estimate gives no pair of X1, X2 or X6 above 0.035 fF
  (`build/estimate.txt`). It has no polysilicon and could not see the
  coupling of X1 in layout 2.1; here the comparator is a block whose
  extraction alone is already known.
- **The comparator was not extracted alone again, and nothing of this
  layout was extracted before `run_x.sh`.**
- **[`x_check.py`](x_check.py) was run once before the extraction, on
  the build folder of layout 2.1**, to see it run to its end. It gave
  that layout's known numbers (X1 0.0426 fF, X3 52.33 fF, X7 6.99 fF)
  and wrote nothing here.
- **Not done**: the antenna violation, and the reports of the KLayout
  deck, read as for the first layout.
