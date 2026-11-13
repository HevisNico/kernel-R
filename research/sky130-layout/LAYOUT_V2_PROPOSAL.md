# Proposal: a second layout of the cell

**A proposal for the owner. Nothing in it has been drawn, extracted or
run.** Written on 2026-11-13 from
[`diagnostic/DIAGNOSTIC.md`](diagnostic/DIAGNOSTIC.md). The predictions
below are candidates, written before any layout or extraction of a
second version exists.

## What the first layout showed

Three effects, by three sets of wires
([`diagnostic/DIAGNOSTIC.md`](diagnostic/DIAGNOSTIC.md)):

| Effect in stage P | Cause in the layout | Size |
|---|---|---|
| Every port refused for its rest state | `vq` next to `x1.ad`, a logic wire of port 1 | 1.674 fF |
| L4, an offset of 0.014 mV on the read of the stored voltage | The summing node next to the sensor node and to `ad` | 0.92 fF and 0.17 fF per port |
| Rooms not positive: a common shift of the gap of +0.013 | Capacitance added to `vq` | 75.6 fF, of which 31 fF to the substrate |

The router of the first layout knows one rule: the spacing of the
layer. It does not know that `vq` and the summing node are not wires
like the others.

## What would change

Same cell, same devices, same generator. Three changes, in the order
of what they cost.

**1. Three classes of nets in the router.**

| Class | Nets | Rule |
|---|---|---|
| Quiet | `vq`; `sum`, `vs`, `x`, `vmem`, `dq`, `gm` of each port; the nodes inside the op-amp and the comparators | Routed first |
| Loud | Every net that swings by more than 0.5 V in a period: the sequencing logic, `ad`, `adb`, `preb`, `rst`, `sen`, `si`, `sd`, `p`, `pb` | Never nearer than 1.4 µm to a quiet net on its layer, never over or under one |
| Still | Supplies and references | No rule |

**2. A shield for `vq` and for each summing node**: a `vss` wire on each
side, on the same layer, and nothing of another net over or under.
`vs` leaves the capacitor array on the side away from the exits of
`sum`, with a `vss` exit between them.

**3. A floorplan that makes `vq` short.** The admission switches and
the gain mirror of each port move to the edge of the port that faces
the shared column, and the sequencing logic to the far edge. `vq` then
joins the main capacitor, the leak resistor, the comparator and the two
ports over some tens of micrometres, where the first layout takes it
across both ports.

**A shield and a short wire pull against each other.** A shield takes
`vq` away from the logic and adds capacitance from `vq` to the shield:
the first effect goes down, the third goes up. This is why the
floorplan comes with the shield.

## Decisions for the owner

| | Decision | Proposal |
|---|---|---|
| E1 | What a second layout is judged on | The extraction first (predictions X1 to X5), then one nominal stage (S1 to S5). The 8 cells only if both hold |
| E2 | The main capacitor | Kept at its ideal value, as decision D3 says. The other way is to draw it smaller by the capacitance the wires add, so that the sum is 5 pF; that changes D3 and is not proposed |
| E3 | The rest band of the rule, `0.1 ≤ c_pre ≤ 0.1001` | Unchanged. It is one-sided and 50 µV wide: the layout must meet it, not the reverse |
| E4 | The first layout | Kept as it is, with its report. The second is another folder |

## Candidate predictions

Written before any drawing. The numbers are this author's reasoning
from the first extraction, not measurements. The owner fixes, changes
or drops each one.

**On the extraction alone, before any simulation.** Primary list, with
the plate rule of [`AMENDMENT_3.md`](AMENDMENT_3.md).

| | Candidate | First layout | Reasoning |
|---|---|---|---|
| X1 | Between `vq` and any loud net: at most 0.03 fF each, at most 0.10 fF in all | 1.674 fF to `x1.ad` alone | 0.03 fF × 1.8 V on 5 pF is 11 µV, a fifth of the band |
| X2 | Between a summing node and `vs` of its port: at most 0.10 fF. Between a summing node and any loud net: at most 0.03 fF each | 0.92 fF; 0.17 fF to `ad`, 0.23 fF to `si` | 0.10 fF × 0.9 V on 30 pF is 3 µV |
| X3 | Capacitance added to `vq`, everything counted: at most 45 fF | 75.6 fF | A wire of 60 µm with its shield, and the exits of the four plates. **The weakest of the five**: the shield may cost more than the shorter wire saves |
| X4 | The two ports seen from `vq`: each capacitance from `vq` to a node of port 1 within 0.1 fF of the same one of port 2 | 0.81 fF to `x1.dq`, 9.09 fF to `x2.dq` | `vq` in the middle, the two ports mirror images |
| X5 | Magic DRC 0, LVS match, no wire under a capacitor; area at most 0.085 mm² | 0.0742 mm² | Shields and keep-out distances cost area |

**On one nominal stage**: the nominal runs of stage P, primary list, by
the same runners.

| | Candidate | First layout | Follows from |
|---|---|---|---|
| S1 | The rest charge before every pulse of the nominal train is between 0.1 and 0.1001 | 0.100983 after a period of port 1 | X1 |
| S2 | No step of a port at rest, of a firing pulse, or of a port that passes between pulsed and idle is above 0.005 mV; the first silent step is within 0.003 mV of the later ones | 0.014 mV; 0.014 mV | X2 |
| S3 | The gap of the nominal cell moves by −0.002 to +0.010 against the schematic, the two ports within 0.0005 of each other | +0.0140 and +0.0125 | X3, by `log(1 + C / 5 pF)`; X4 |
| S4 | L1, L2, L3, L5, L6, L7 and L13 hold as they did | hold | Nothing that carried them changes |
| S5 | Silent step between 1.340 and 1.365 mV | 1.343 to 1.358 mV | The dose depends on the wires of `vs` and of the array, which stay |

**On the 8 cells, only as a candidate for later:**

| | Candidate | First layout |
|---|---|---|
| C1 | No port is refused for its rest state | 16 of 16 |
| C2 | L11 holds, and rests on at least 2 certified ports of 16 | holds, on 0 |
| C3 | No prediction on the four ports of L12 unless S3 gives a shift below 0.004: with a larger shift they leave the centre of their dose interval, as they did | 0 of 4 |

**What would count against the second layout:** X1 or X2 failing, since
they are what it is drawn for; S1 failing with X1 holding, which would
mean the mechanism of the diagnostic is not the whole of it.

**What it cannot fix:** a port certified on the schematic keeps its
room only if the gap does not move. The rooms of the four ports of L12
are 0.006 to 0.009: a shift above 0.006 loses the first of them and a
shift above 0.009 all four, and no shield removes the capacitance of a
wire to the substrate. C3 says so in advance.

## Cost

- Router: the classes and the shield wires, some days of work on
  `layout/route.py`, with the blocks checked again one by one. No
  estimate of the drawing time is given beyond that.
- Compute: the extraction takes seconds. The nominal stage is seven
  runs, under 15 minutes on one machine at the speed measured in
  stage P.
