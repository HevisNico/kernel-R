# Amendment 3 to the predictions of phase 1: the plates of the MIM capacitors

Declared on 2026-11-13, at the owner's decision, **before any run of
stage P.** [`PREDICTION.md`](PREDICTION.md) and the two earlier
amendments are not edited.

**When this file is pushed:** the cell is laid out and extracted
([`layout/README.md`](layout/README.md),
[`layout/EXTRACTION.md`](layout/EXTRACTION.md)). No simulation of the
cell with an extracted capacitance has been made, on any netlist.

## The finding

[`layout/EXTRACTION.md`](layout/EXTRACTION.md), finding F4: between the
two plates of every MIM capacitor, Magic's extraction adds what it
would add for a metal4 wire over a metal3 wire, 4.3% to 5.1% of the
capacitor. The device model is the capacitor alone, and decision D3
keeps each capacitor at its ideal value. **The term counts the device a
second time.**

## The decision of the owner

- **Primary analysis:** the extracted term between the two plates of
  each MIM capacitor is removed. Every other extracted capacitance is
  kept.
- **Secondary, declared analysis:** the same with that term kept, as an
  upper bound.

## The rule that removes the term

"The term between the two plates" is fixed by a second extraction, not
by removing a row. A row cannot simply be removed: five of the seven
kinds of capacitor have their bottom plate on node 0, and their row
also holds the capacitance of the wires of the top node to the
substrate, which is real and is kept.

1. The cell is extracted a second time, flattened as before, with **the
   metal4 of every top plate erased inside its capacitor**, where the
   generator drew it, 0.195 µm inside the capacitor layer. The exits of
   the plates, the joints between plates and every wire stay. A dummy
   plate is left as it is.
2. For each capacitor of `cell.spice`, between its two nodes: **plate
   term = capacitance in the first extraction − capacitance in the
   second**, not below zero.
3. The primary list is the first extraction with the plate term taken
   out of that one row for each capacitor. **Every other row is the
   first extraction, unchanged.** The second extraction is used for
   nothing else.

Script: [`layout/plates.py`](layout/plates.py), run by
`layout/run_plates.sh`. Two runs gave the same files. Nothing is
simulated.

| Capacitor | Ideal | Extracted between its nodes | Plate term, removed | Kept in the primary list |
|---|---|---|---|---|
| `cf`, each port | 30 pF | 1 443.52 fF | 1 327.32 fF, 4.42% | 116.20 fF |
| `cs`, port 1 / port 2 | 400 fF | 27.34 / 27.49 fF | 17.62 fF, 4.41% | 9.72 / 9.86 fF |
| `cq` | 5 pF | 253.09 fF | 221.78 fF, 4.44% | 31.31 fF |
| `cc`, each port | 1.5 pF | 64.53 fF | 63.40 fF, 4.23% | 1.13 fF |
| `cdp` | 2 pF | 97.81 fF | 89.81 fF, 4.49% | 7.99 fF |
| `cda`, each port | 200 fF | 14.92 fF | 9.51 fF, 4.76% | 5.41 fF |
| `cdl`, each port | 200 fF | 17.15 fF | 9.53 fF, 4.76% | 7.62 to 7.63 fF |

- What is kept between the plates of `cf`, 116.2 fF or 0.39%, is the
  capacitance of the joints and exits of the top plates over the bottom
  sheet. It is a parasitic of the wires and stays.
- 3.166 pF is removed in all, of 5.585 pF extracted.

## The two lists

| | File | sha256 | Sum |
|---|---|---|---|
| Primary | `phase1/p_caps_primary.csv` | `23317ecd20e65bedd988ad07261319a338beb4e6622f4fb8666cfc932824aba2` | 2.418 pF |
| Secondary, as extracted | `phase1/p_caps.csv` | `efd1a994fa237cabeb2e61f6ba5692fbe38484ec8988313b652e3d205b8e5e4c` | 5.585 pF |
| Source and drain areas, both | `phase1/p_areas.csv` | `19bd1f27e174c22c7b8b2eea9afb8d81fe4a744993539763ab46b819dd88542a` | |

**Both lists hold the same 1 436 pairs of nodes, in the same order. 12
rows differ: one for each capacitor.** No row is dropped.

Arithmetic on these tables, not a simulation: the ratio
`(cs + kept) / (cf + kept)` is 2.0% above `cs / cf` with the primary
list and 1.9% above with the secondary one. On `vq` the primary list
has 31 fF to node 0 and the secondary one 253 fF.

## What each analysis decides

- **The primary analysis decides every prediction L1 to L13**, with the
  scope, the cells, the calibration and the rules of
  [`PREDICTION.md`](PREDICTION.md) and of
  [`AMENDMENT_2.md`](AMENDMENT_2.md), unchanged. "The extracted
  capacitances" there now reads "the primary list".
- **The secondary analysis decides no prediction.** It is reported
  apart, under the words "upper bound: the plate term kept". A
  prediction that holds on one list and fails on the other is reported
  as such, and its verdict is the primary one.

**Scope of the secondary analysis: this author's reading, which the
owner may change before the go.** "The same" is read as the same
netlist construction and the same measures, on **the nominal runs of
stage P**: cell run, ramp, read, leak scan and refresh of 100 pulses
under 0.1 TΩ at 27 °C; cell run and refresh of 60 pulses at 125 °C.
Seven runs, no cell with mismatch, no calibration.

- They are split as the nominal runs of the primary analysis are
  ([`AMENDMENT_2.md`](AMENDMENT_2.md)): the first four on machine A, the
  last three on machine B.
- They start on each machine after the last run of its primary queue,
  and are the first to go if time runs out. A secondary run with no
  result is reported as such.
- At the recorded medians they add about 1 460 s of one core times `f`,
  about 0.9 h of wall time on machine B at `f` = 6.
- Running every cell on both lists would double stage P. It is not
  planned.

## What does not change

- **The identity test I2** ([`AMENDMENT_1.md`](AMENDMENT_1.md)) is run
  once: with every capacitance at 0 F the two lists give the same deck.
- **The timing run and the scope** ([`AMENDMENT_2.md`](AMENDMENT_2.md))
  use the primary list. The thresholds of the scope rule are unchanged.
- The source and drain areas are those of the layout for both analyses.
- No prediction, bound, cell or threshold is changed.

## What this amendment rests on

The plate term is called a duplicate by reading the structure and the
model, not by a measurement: no field solver was run
([`layout/EXTRACTION.md`](layout/EXTRACTION.md)). The secondary
analysis is there for that reason.
