# Second layout of one R cell

Drawn under [`../PREDICTION.md`](../PREDICTION.md), which was pushed
alone before any of it existed. **Extracted once. Nothing of it has
been simulated.** The first layout is untouched in
[`../../layout/`](../../layout/README.md).

```sh
cd research/sky130-layout/v2/layout
sh run.sh        # every block, flattened DRC, KLayout, antenna, negative controls: about two minutes
sh run_x.sh      # the extraction and the verdicts X1 to X5: under a minute
```

Outputs go to `build/`, not committed. Hashes: [`SHA256SUMS`](SHA256SUMS)
and [`SHA256SUMS_X`](SHA256SUMS_X). The verdicts are in
[`../X_REPORT.md`](../X_REPORT.md), written by
[`x_check.py`](x_check.py) and not edited.

## What differs from the first layout

The generator is a copy of the first one with three changes
([`route.py`](route.py), [`floorplan.py`](floorplan.py)):

1. **Two classes of nets.** A loud wire and a critical one (`vq`, the
   summing nodes) are kept 1.4 µm apart on the same layer and on the
   next ones, and never cross on any layer. The rule is waived within
   three tracks of the exit of a transistor that carries both nets.
2. **Shields.** Each critical wire gets a `vss` wire on the free tracks
   beside it: 248 shield nodes in a port, 273 at the top.
3. **Floorplan.** The admission switches at the edge of each port that
   faces the shared column, with `vq` leaving the port by a wire drawn
   inside it; the sensor plate of the capacitor array in column 6, away
   from the three columns that carry the exits of the summing node; the
   FIRE comparator under the main capacitor and the leak resistor.

| Check | Second layout | First layout |
|---|---|---|
| Magic DRC, each block and the flattened cell | 0 | 0 |
| netgen LVS, each block and the cell | match, no property error | the same |
| KLayout deck | 522 reports of the same 5 rules, read as before | 531 |
| Antenna check of Magic | 3, not fixed | 3 |
| Negative controls | all three caught | the same |
| Size | 387.5 µm × 215.7 µm = 0.0836 mm² | 0.0742 mm² |

## What happened while it was drawn

Said so that the verdicts can be weighed.

- **The area was brought under the limit of X5 before the extraction.**
  The first assembly of the cell was 0.0865 mm², above 0.085. The
  reference switches were moved beside the FIRE comparator: 0.0836 mm².
  Two other placements of those switches were tried and left the
  router without a path for `vdd`. No extraction existed then.
- **The layout was not changed after the extraction.** It was extracted
  once.
- **One script was corrected after the first run of `run_x.sh`.** The
  first extraction had succeeded; the second one, without the metal of
  the top plates, stopped in [`plates.py`](plates.py) on a net that
  Magic named after a transistor terminal. In this layout the summing
  node reaches two exits of its plates, so that without the plates it
  falls into two pieces, which the first layout did not do. The naming
  was resolved from the aliases Magic records. No criterion of
  [`x_check.py`](x_check.py) was touched; it was pushed before any
  extraction.

## What it is not

As the first: not matched, not compact, no pin at the boundary, no
supply grid. The shields are `vss` wires of 0.34 to 0.38 µm joined to
`vss` where the router found a way; nothing checks their resistance.

The zeros of the report are what Magic's rules give between two wires
once a third stands between them or once they are far apart. A field
solver would not give zero.
