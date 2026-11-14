# A network of R cells at transistor level: phase 0

**Exploratory. Nothing here is preregistered, and nothing here is the
decisive experiment of `docs/ROADMAP_V1.md` (branch `docs/roadmap-v1`, not
yet on `main`).** Phase 0 builds the bench, looks at what a
two-cell network does, measures what the theorem needs, and lists where the
circuit leaves the theorem. It stops there, for review.

Simulations only: ngspice 42, SKY130 models, the cell of
[`../circuit/cell.spice`](../circuit/cell.spice) with the junction areas of
stage J, typical corner, 27 C, **no noise, no mismatch**. No layout of a
network exists.

| File | What it is |
|---|---|
| [`net.py`](net.py) | several cells in one deck; each port takes a pulse at any date |
| [`router.py`](router.py) | the dated router around the cells, and the two calendars |
| [`percell.py`](percell.py), [`PERCELL.json`](PERCELL.json) | one cell alone: threshold, doses, phases, effect of a recent pulse |
| [`EXPECTATION.md`](EXPECTATION.md) | the learned state of the network, written and pushed before any network run (commit `f1dbd84`) |
| [`NETWORK.json`](NETWORK.json) | the two network runs, against that expectation |
| [`DEPARTURES.md`](DEPARTURES.md) | where the circuit network leaves the hypotheses of the theorem |
| [`CANDIDATES.md`](CANDIDATES.md) | candidate predictions for the decisive experiment; none of them has been run |
| [`COST.json`](COST.json) | one cell on the stage-J deck and on the extraction of layout 2.2 |

## 1. The bench

The circuit has no way to send a FIRE to another cell: a port expects a
current pulse of a fixed shape and three timing signals, which the stimulus
supplies (`../circuit/DESIGN.md`, "What the stimulus provides"). The bench
therefore puts an **ideal router** between the cells, outside the simulator:

- each cell is the unchanged circuit, as a sub-circuit: two ports, one main
  capacitor, one FIRE comparator, one protection latch;
- each port of each cell has its own timing signals and pulse current, tied
  to one date that is set while the run is stopped. A pulse can start at any
  date, not on a fixed period;
- the router stops the simulator when the protection latch of a cell rises
  (a FIRE), dates the rise, and schedules a standard pulse on the target port
  `delay` later, if the date is inside the gate of the edge.

It follows the reciprocal construction of the network theorem
([`../network-stability/MILESTONE_3.md`](../network-stability/MILESTONE_3.md),
[`RECIPROCAL_CLOSURE.md`](../network-stability/RECIPROCAL_CLOSURE.md)): two
cells A and B, a forward edge from A to a port of B, a later return edge from
B to a port of A, both delays 7/20 of a time unit, the source dates of the
witness (A at 0, 8, 16, 24, 32, 160, 168, 176; B at 320 to 368), horizon
459.9. One time unit is 20 us, the length of a pulse. Native ports 0 and 2 of
A are ports 1 and 2 of cell `a`; native ports 1 and 2 of B are ports 1 and 2
of cell `b`. The circuit cell has two ports where the native cell has three;
the witness uses two per cell.

Check of the bench against stage J of the layout study, on one cell with
pulses 22 units apart: four silent pulses then FIRE, dose 1.3495 mV, first
FIRE at latency 0.9137 (stage J: 0.9136), ERROR phase from 1.78 to 2.04
units, protection until 5.60 units.

## 2. What it does: it trains, it stops, and what it learns

Two calendars were run, each once. What each should learn was written first
([`EXPECTATION.md`](EXPECTATION.md), pushed at 13:26:18 UTC; the runs started
at 13:26:25).

| Calendar | Port | Decisions (s: silent and one dose, F: FIRE) | Writes | Expected |
|---|---|---|---|---|
| N, the witness as it is | `a1`, sources of A | `ssssFFFF` | 4 | the same |
| | `b1`, forward wire | `sss` | 3 | the same |
| | `b2`, sources of B | `ssssFFF` | 4 | the same |
| | `a2`, return wire | `sss` | 3 | the same |
| L, longer trains | `a1` | `ssssFFFFFFFFF` | 4 | the same |
| | `b1`, forward wire | `ssssFFFF` | 4 | the same |
| | `b2` | `ssssFFFFFF` | 4 | the same |
| | `a2`, return wire | `ssssFF` | 4 | the same |

Counts of FIRE (N: 4 and 3; L: 11 and 10) and of routed pulses (N: 3 and 3;
L: 8 and 6) are as expected. No pulse found its cell protected, none was
left in the queue, no port wrote when it was not pulsed, every silent pulse
wrote one dose (1.3494 to 1.3495 mV). The wire pulses arrived at 161.285,
169.205 and 177.205 (expected near 161.26, 169.19, 177.19).

**It trains and stops**: in calendar L every port learns for four pulses and
then fires on every later pulse, without a further write. In calendar N the
two wires end one dose short of their threshold, because the witness sends
three pulses on each and this circuit needs four: the witness was built for
native cells that need three (A, return) or one (B, forward).

**What it does not do as the witness**: A's source at 24 is silent (it fires
in the witness), A's source at 32 fires (in the witness it arrives protected
and writes a recovery dose), and no wire fires in calendar N.

Both runs agree with what was written before them. This is one agreement, on
nominal cells without noise, of a rule fitted on the same nominal cell: it
shows that the method can be carried out, not that the theorem predicts
circuits.

## 3. What was measured on one cell

All in [`PERCELL.json`](PERCELL.json). Reserves are in mV from the service
threshold of the port, in the capacitor coordinate of the supervisor study.

| What the theorem needs | Measured |
|---|---|
| Bias: the gap of a port at its preset | 4.850 mV, 3.594 doses (bracket 16 uV), both ports |
| Dose `d` | 1.3495 mV (8 doses, spread 0.00004 mV) |
| Need | 4 |
| Margin of the last silence, isolated | 0.801 mV |
| Margin of the first FIRE, isolated | 0.548 mV |
| Read error from noise | not measured here; in the supervisor qualification, same cell, 0.10 mV rms on a single read |
| Phases | READY; protected from the FIRE until 5.52 to 5.60 units after the start of the pulse. No FAST, no SLOW, no recovery memory |
| ERROR phase | 1.78 to 2.04 units after the start of the pulse |
| FIRE latency | 0.914 at the first FIRE, isolated; 0.999 at the threshold |

**Separation between events.** A pulse leaves charge on the main capacitor,
which leaks with a time constant of two units. A later pulse on the same
cell, on either port, is helped by what is left. Measured as an equivalent
reserve, by the latency of a FIRE against that of an isolated read:

| Earlier pulse, units before | Residual charge | Help |
|---|---|---|
| 6.5 | 0.057 to 0.062 | +1.38 to +1.50 mV, a whole dose |
| 8 (the spacing of the witness) | 0.027 to 0.030 | +0.63 mV after a silent pulse, +0.70 mV after a FIRE |
| 10 | 0.011 | +0.30 mV |
| 12 | 0.004 | +0.12 to +0.13 mV |
| 16 | 0.0006 | +0.05 mV |
| 22 | 0.0003 | +0.015 mV |

About 23 mV per unit of residual charge. At the spacing of the witness the
help is nearly half a dose, and it is larger than the noise by a factor of
six. The fourth read of a train 8 units apart keeps its silence by 0.17 mV
only.

**A pulse that arrives while the cell is protected** (after a FIRE on the
other port):

| Arrives, units after the start of the firing pulse | What happens |
|---|---|
| 2, 3 | nothing: no FIRE, no write |
| 4, 5 | no FIRE, **and one dose is written**: the pulse is not admitted, but its ERROR phase opens after the protection has cleared |
| 5.5 | the protection clears during the pulse; what is left of the pulse is admitted and the cell fires, at latency 0.87 |
| 6 and more | an ordinary read, helped as in the table above |

## 4. Where the circuit leaves the theorem

[`DEPARTURES.md`](DEPARTURES.md) lists fourteen places. The three that
matter most for a prediction:

1. **The score depends on the recent past of the cell**, not only on its
   write count: the help of the table above. At the spacing of the witness it
   is half a dose. Either the calendar separates the pulses of a cell by 16
   units or more, or the help enters the rule, as it does in
   `EXPECTATION.md`.
2. **A protected arrival can write a gain dose** with no read to stop it. The
   model writes a recovery dose there, on another coordinate. A network that
   sends pulses 4 to 5 units after a FIRE of their target raises its gain at
   each of them; nothing in the circuit bounds that.
3. **Two pulses that overlap on one cell are one joint read**, not two reads
   in some order. Same-date ties have no order to commute. Not exercised in
   phase 0.

## 5. Cost, and the netlist of layout 2.2

Measured here, without noise:

| Run | Simulated | Wall time |
|---|---|---|
| Two cells, calendar N | 9.3 ms | 241 s |
| Two cells, calendar L | 9.3 ms | 372 s |
| One cell, six pulses, stage-J deck | 2.4 ms | 41 s |
| One cell, six pulses, extraction of layout 2.2 | 2.4 ms | 49 s |

The two network runs shared the machine with each other and with another
job. A run costs by simulated time and by cell, whether anything happens or
not: about 13 to 20 s per millisecond and per cell. Four fifths of the
witness's horizon are idle (32 to 160, 184 to 320, 376 to 460). Noise
multiplies the cost by 1.6 (measured in the supervisor campaign). So one
noisy two-cell run of calendar L is about 10 minutes of one processor; with
four at a time on each of two containers, about 50 runs per hour.

**The netlist extracted from layout 2.2 can be used, cell by cell.** The bench
takes the areas and the 1 210 wire capacitances of
`research/sky130-layout/v2.2/phase1` (branch `sky130-layout-phase1`) and
repeats them inside each cell. One cell on it: four silent pulses then FIRE,
dose 1.3616 mV, first FIRE at 0.941, protection until 5.68 units; 1.2 times
the wall time. What it cannot give: anything between the cells. There is no
layout of two cells, no wire from a FIRE to a port, and the router is ideal.
No network was run on it.

## 6. Candidate predictions

[`CANDIDATES.md`](CANDIDATES.md): eight candidates, with what must be measured
per cell first and which hypothesis each one tests. None has been run, on
purpose.

## Evidence and reproduction

Raw waveforms are not in Git. Each run is identified in `PERCELL.json`,
`NETWORK.json` and `COST.json` by the SHA-256 of its deck and of its raw
waveform. The bench was changed after `f1dbd84` only to accept a layout
extraction; the deck of the network runs is byte for byte the one of that
commit.

```sh
python -B research/network-circuit/percell.py train OUT 1 22 7 /usr/bin/ngspice PDK
python -B research/network-circuit/percell.py threshold OUT 1 /usr/bin/ngspice PDK
python -B research/network-circuit/percell.py history OUT /usr/bin/ngspice PDK
python -B research/network-circuit/router.py native OUT /usr/bin/ngspice PDK
python -B research/network-circuit/router.py longer OUT /usr/bin/ngspice PDK
```
