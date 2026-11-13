# Second layout of one R cell: predictions

Written on 2026-11-13, after the owner approved
[`../diagnostic/DIAGNOSTIC.md`](../diagnostic/DIAGNOSTIC.md) and
[`../LAYOUT_V2_PROPOSAL.md`](../LAYOUT_V2_PROPOSAL.md), accepted
decisions E1 to E4, and accepted the candidates X1 to X5, S1 to S5 and
C1 to C3 as the basis of this file.

**When this file is pushed:**

- nothing of a second layout is drawn: no cell, no block, no wire;
- no extraction of a second layout exists;
- no simulation of a second layout has been made.

**This file is pushed alone, before any drawing.** It is not edited
afterwards. A deviation is declared in an amendment, before the step it
concerns.

These are predictions about an extraction and about simulations. No
chip is built.

## What is known

- The first layout, its extraction, the report of stage P and the
  diagnostic: [`../layout/`](../layout/README.md),
  [`../phase1/P_REPORT.md`](../phase1/P_REPORT.md),
  [`../diagnostic/DIAGNOSTIC.md`](../diagnostic/DIAGNOSTIC.md). **The
  first layout stays as it is, in its folder.**
- One simulation of the schematic, made to write this file: the nominal
  train with every net saved, to list the nets that swing. No area, no
  capacitance, no layout.
- One extraction of two device cells of the first layout, drawn alone,
  to measure what a transistor's own exits add between its gate and its
  source or drain.

The predictions are not blind to these. They are blind to any drawing
and any extraction of the second layout.

## What the second layout changes

The same cell, the same devices, the same generator and checks as the
first. Three changes, as proposed:

1. the router knows quiet nets and loud nets, and keeps them apart;
2. `vq` and each summing node run between `vss` wires, with nothing of
   another net over or under; `vs` leaves the capacitor array away from
   the exits of `sum`;
3. a floorplan that makes `vq` short: the admission switches and the
   gain mirrors at the edge of each port that faces the shared column,
   the sequencing logic at the far edge.

How it is done may change while it is drawn. What it is judged on may
not.

## Definitions

- **The list of capacitances** is the primary list of
  [`../AMENDMENT_3.md`](../AMENDMENT_3.md): the cell flattened,
  extracted by Magic with capacitance only, the plate term of each MIM
  capacitor taken out by a second extraction. The scripts are those of
  the first layout, `pex.py` and `plates.py`, run on the second.
- **A loud net** is a net of the layout that swings by more than 0.5 V
  in the nominal train of the schematic. There are 102:
  - in each port, 42: `a`, `ab`, `ad`, `ad1`, `adb`, `adm`, `admb`,
    `b`, `bb`, `c`, `cbar`, `cd1`, `cd2`, `cdel`, `cmpb`, `cmps`, `en`,
    `preb`, `rst`, `sba`, `sbb`, `sbc0`, `sd`, `sen`, `si`, `sib`,
    `vs`, `xcmps.o1`, `xcmps.o2`, `xcmps.o3`, and the 12 inner nodes of
    the NAND gates (`n1` of `xnad`, `xnsa`, `xnsb`, `xnsc` and of the
    two gates of `xla`, `xlb`, `xlc`; `n1` and `n2` of `xnsi`);
  - shared, 18: `cmpm`, `cmpmb`, `p`, `pb`, `pbdel`, `pd1`, `pdel`,
    `rbp`, `sbp`, `vrefm`, `vrefmn`, `xcmpm.o1`, `xcmpm.o2`,
    `xcmpm.o3`, and `n1` of `xnsp`, `xnrp` and of the two gates of
    `xlp`.
  - `vq` (0.45 V), `dq`, `vrefs`, the nodes of the op-amps and the
    first stage of the comparators are not loud.
- **The device floor.** A transistor drawn alone, with its exits, has
  0.035 fF between its gate and its source or drain when it is the
  switch of 1 µm by 0.15 µm (measured on the first layout). Where a
  loud net is the gate of a transistor whose source or drain is the
  node in question, that transistor's own value, measured on its cell
  of the second layout drawn alone, is subtracted before the
  comparison. This concerns `adm` on `vq` (the admission switch of each
  port) and `si` on the summing node (the steering switch). It is a
  precision added to the accepted candidates: without it X1 and X2
  would fail on the device alone, whatever the wires.

## X1 to X5: on the extraction alone

Judged by a script committed before the extraction of the cell is
made. **After X1 to X5 the work stops for the owner's review.**

| | Prediction | First layout |
|---|---|---|
| X1 | Between `vq` and each loud net: at most 0.03 fF. Between `vq` and all loud nets together: at most 0.10 fF. Device floor subtracted for `x1.adm` and `x2.adm` | 1.674 fF to `x1.ad`; 0.69 fF to `vrefmn` |
| X2 | Between the summing node of a port and `vs` of that port: at most 0.10 fF. Between a summing node and each other loud net: at most 0.03 fF. Device floor subtracted for `si` of the port | 0.92 fF; 0.17 fF to `ad`, 0.23 fF to `si` |
| X3 | The capacitances with one end on `vq`, summed: at most 45 fF | 75.6 fF |
| X4 | For every net of a port: its capacitance to `vq` in port 1 and in port 2 differ by at most 0.1 fF | 0.81 fF to `x1.dq`, 9.09 fF to `x2.dq` |
| X5 | Magic DRC, style `drc(full)`: 0 on each block and on the flattened cell. netgen LVS: "Circuits match uniquely", no property error, on each block and on the cell. No wire on metal1 or metal2 under a capacitor: 0 reports of rules `capm.10` and `capm.2b` of the KLayout deck. Bounding box of the cell at most 0.085 mm² | 0, match, 0, 0.0742 mm² |

- X3 is the weakest: a shield takes `vq` away from the logic and adds
  capacitance from `vq` to the shield.
- X1 holds `vrefmn`, the other input of the FIRE comparator, which sits
  beside `vq` by construction. It is in the list because it swings by
  0.54 V.
- The other reports of the KLayout deck and the antenna check are
  given as for the first layout. They are not part of X5.

## S1 to S5: one nominal stage

**Not started before the owner says so.** The seven nominal runs of
stage P, primary list, by the same runners and the same harness, on
the netlist of the second layout.

| | Prediction | First layout |
|---|---|---|
| S1 | The rest charge before every pulse of the nominal train is between 0.1 and 0.1001 | 0.100983 after a period of port 1 |
| S2 | No step of a port at rest, of a firing pulse, or of a port that passes between pulsed and idle is above 0.005 mV. The first silent step of each port is within 0.003 mV of its later ones | 0.014 mV; 0.014 mV |
| S3 | The gap of the nominal cell moves by −0.002 to +0.010 against the schematic, the two ports within 0.0005 of each other | +0.0140 and +0.0125 |
| S4 | L1, L2, L3, L5, L6, L7 and L13 of [`../PREDICTION.md`](../PREDICTION.md) hold on the nominal runs, read as in stage P | hold |
| S5 | Every silent step of the nominal cell is between 1.340 and 1.365 mV | 1.343 to 1.358 mV |

S3 needs constants. Without a calibration on the second layout it is
read with those of the first one (`d0`, `kappa`, `mu` of stage P); this
is said again when the stage is declared.

## C1 to C3: the 8 cells

**Not started before the owner says so, and only if X1 to X5 and S1 to
S5 hold.** The cells, the runs and the rules of stage P.

| | Prediction | First layout |
|---|---|---|
| C1 | No port is refused for its rest state | 16 of 16 |
| C2 | No certified port has a count different from its need, and at least 2 of the 16 ports are certified, at status 3 or by rule A1 | none contradicted; 0 certified |
| C3 | No prediction on the four ports of L12 unless S3 gives a shift below 0.004 on both ports. If it does: at least 2 of the 4 are certified again at status 3 | 0 of 4 |

## What counts against the second layout

- **X1 or X2 failing.** They are what it is drawn for.
- **S1 failing while X1 holds**, or **S2 failing while X2 holds**: the
  mechanism of the diagnostic would then not be the whole of it.

**What is a limit and not a failure:** X3 or S3 outside its range. A
port certified on the schematic keeps its room only if the gap does not
move, and no shield removes the capacitance of a wire to the substrate.

## What these predictions do not say

- Nothing about silicon. The capacitances are those Magic extracts by
  rules; no field solver is run.
- Nothing about matching: the second layout does no more for it than
  the first.
- Nothing about the resistance of the wires.
- X1 to X5 are read on one extraction of one layout, and S1 to S5 on
  nominal runs without noise: they carry no interval.
