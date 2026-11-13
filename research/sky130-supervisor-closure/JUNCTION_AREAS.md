# Choice: the qualification is redone on netlists with junction areas

Recorded on 2026-11-13, before any simulation of the supervisor on a netlist
with junction areas. [`BOUNDS.json`](BOUNDS.json) is not edited.

## What was learned

Stage J of the layout study (PR 125, branch `sky130-layout-phase1`, commit
`023692d`; 13 predictions of 13 held): with source and drain areas on every
transistor, the nominal cell at 125 C loses about 0.193 mV per period from
junction leakage alone, needs 8 to 10 silent pulses to learn, and falls
silent again every 7 periods.

The netlists of this qualification, like those of every earlier campaign,
give the transistors no source or drain area
(`SCHEMATIC_NO_JUNCTION_AREAS.md` of the same branch). The device model then
uses a default junction current that does not depend on temperature. So:

- `BOUNDS.json` underestimates the loss at `tt125` by a factor of about 4:
  it counts 0.059 mV per period at the reference leak, all of it from the
  imposed leak, where the junctions alone take about 0.19 mV. The same holds
  for any hot condition.
- Everything else in `BOUNDS.json` (thresholds, capacities, doses, noise) was
  also measured without junction capacitance. Stage J found it changes almost
  nothing at 27 C; that is a result on the nominal cell at the typical
  corner, not on the nine configurations of this qualification.

## The choice

**Option (a).** The netlists are rebuilt with junction areas, with the
construction of stage J, which keeps the mismatch sample, and the bounds are
measured again on them, for the nine configurations. Option (b), restricting
the domain to the temperatures where the junctions do not matter, is not taken.

The two files of stage J are copied here unchanged, because PR 125 is not
merged and this branch does not contain them:

| Copy | Origin, at commit `023692d65b6f6c5badc58ab6f668327a31291d7b` | SHA-256 |
|---|---|---|
| [`junction/netlist.py`](junction/netlist.py) | `research/sky130-layout/phase1/netlist.py` | `48175a9e44cbee3f22c8b94144ea29811c66088d6ecbf7419ce6bbd49dd642da` |
| [`junction/areas.csv`](junction/areas.csv) | `research/sky130-layout/phase1/areas.csv` | `2d89bea15524df3e317c087216a992a443b9a3b147351e99d2d675b3dbb7d17d` |

These are the hashes of the manifest of stage J. The areas are those of each
of the 232 transistors drawn alone; a layout that shares diffusions would have
smaller ones. No wire capacitance is added: there is no layout of the cell.

What will be done, in this order:

1. the deck of the supervised cell, expanded and given its areas by
   `junction/netlist.py`; an identity test with all areas at zero against the
   deck used so far, on a nominal and on a mismatch configuration;
2. the whole qualification again on that deck: thresholds, maps of the three
   reads, doses, losses, noise. The loss of a period now has a part that
   does not come from the imposed leak; it is measured, not assumed;
3. new bounds in a new file, pushed before any confirmation sequence on the
   new deck; then the confirmation.

If a configuration has no well-formed bounds on the new deck, it is stated
as it is.

## What had already been run without junction areas

All of it stays as it is, identified by its hashes, and none of it is used as
a result on the cell with junctions.

- Every measurement behind `BOUNDS.json`.
- A confirmation batch of 100 sequences with the bounds of `BOUNDS.json`,
  started at 20:20 UTC. It was stopped when the result of stage J was
  received: 65 sequences had been started and all 65 ended, among them **eight at 125 C**
  (`confn3-tt125-0`, `confn3-tt125-1`, `confn2-tt125-0`, `confn2-tt125-1`,
  `confn0-tt125-0`, `confn0-tt125-1`, `conf3-tt125-base`, `conf3-tt125-max`,
  started between 20:28 and 21:19 UTC). They are confirmation sequences of
  bounds that are now known to be wrong at 125 C; they confirm nothing about
  the cell with junctions. The 35 remaining sequences were never started.

## Also noted

In `BOUNDS.json` the bounds of `tt-40` with a noise margin of 2 and of 3
standard deviations are **not well-formed** (`well_formed: false`, `H` = 0):
at -40 C the capacity left by the joint read, 1.66 mV per port, minus one
dose, 1.35 mV, leaves less than the floor and the margins need. Only the
version without noise margin has bounds there. Whether this stays true on
the new deck will be measured.
