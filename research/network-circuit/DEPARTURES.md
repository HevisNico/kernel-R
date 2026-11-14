# Where the circuit network leaves the hypotheses of the theorem

Phase 0, exploratory. The theorem is that of
[`../network-stability/THEOREM.md`](../network-stability/THEOREM.md) and its
dated form ([`DATED_TIES.md`](../network-stability/DATED_TIES.md),
[`PHASE_ADMISSION.md`](../network-stability/PHASE_ADMISSION.md)): a pending
occurrence has a score, bias plus routed contribution plus `d` times the write
count of its target; a score of at least zero is a FIRE and enqueues the
successors; a negative score writes one dose. "Measured" means on the nominal
cell of this phase ([`PERCELL.json`](PERCELL.json)); "not measured" means
that phase 0 did not look.

## The drive and the routing

| # | In the theorem | In the circuit network | Size |
|---|---|---|---|
| 1 | A FIRE enqueues successors | The circuit emits nothing a port can receive. An ideal router outside the simulator watches the protection latch and starts a standard pulse on the target | by construction |
| 2 | The drive is the event itself | The pulse on the target is the canonical current of the model, regenerated; its shape does not depend on the FIRE that caused it. With it come three ideal timing signals, since the circuit has no pulse detector | by construction |
| 3 | A wire date is the FIRE clock plus the delay | The same, then moved up to the next date allowed by the noise sources: at most 0.4 us, 0.02 unit, later. The FIRE clock is read when the latch crosses 0.9 V, on a solver step of at most 200 ns | 0.02 unit on a delay of 0.35 |
| 4 | Gates of the edges come from the native send gates | Date bands written in the calendar | by construction |

## The score

| # | In the theorem | In the circuit network | Size |
|---|---|---|---|
| 5 | The score depends on the write count, the bias and the routed contribution | It also depends on when the cell last received a pulse, on either port: the residual charge of the main capacitor helps the next read | measured: +0.63 to +0.70 mV at 8 units, half a dose; +0.05 mV at 16 units; +1.4 mV at 6.5 units |
| 6 | The read error is bounded, in `[l, h]` | The noise of the comparators and of the mirror is not bounded. A margin in standard deviations gives a rate, not a certificate | not measured here; 0.10 mV rms in the supervisor qualification |
| 7 | One dose `d`, the same at every write | Fixed in volts: 1.3495 mV, within 0.00004 mV over 8 writes. In log-gain it follows temperature (`../circuit/DESIGN.md`) | measured at 27 C only |
| 8 | Memory changes only by doses | The stored voltage also drifts through the junctions: about 0.19 mV per 22 units at 125 C (stage J), a dose in 150 units. The witness has idle spans of 128 and 136 units | not measured here; negligible at 27 C |

## Phases

| # | In the theorem | In the circuit network | Size |
|---|---|---|---|
| 9 | READY, FAST and SLOW, with a learned recovery rate and a MARK dose on a protected arrival | READY and protected. The protection lasts until the main charge is back, 5.5 to 5.6 units after the start of the firing pulse. No recovery memory, no MARK | measured |
| 10 | A protected arrival writes one recovery dose and no gain dose | It depends on when it arrives. Up to 3 units after the start of the firing pulse: nothing. At 4 and 5 units: no FIRE, and **one gain dose**, because the ERROR phase of the pulse opens after the protection has cleared. At 5.5 units: the rest of the pulse is admitted and the cell fires | measured, one case each |
| 11 | Reserves bound the writes of each cell | A gain dose written by a protected arrival is decided by no read. A stream of such arrivals raises the gain without a stop. The reserve argument does not cover it | not measured beyond the two cases of row 10 |

## Ties and overlaps

| # | In the theorem | In the circuit network | Size |
|---|---|---|---|
| 12 | Two occurrences due at the same date on one cell are processed in either order, and the orders join | Two pulses that overlap on one cell, on its two ports, are one joint read: the main capacitor adds their currents. There is one decision, not two. Two silent ports would both write | not measured in phase 0. In the supervisor qualification a joint read of two trained ports fires at latency 0.25 to 0.27, against 0.9 for one port |
| 13 | A port can hold several pending occurrences | A port is busy for about 6.2 units from the start of its pulse (sensor cycle, then precharge). The bench refuses a second pulse on a busy port and records it as not delivered. What the circuit would do is not defined by its stimulus | by construction; did not happen |
| 14 | Cells are born along the run (the witness adds B at 160) | Both cells exist from the start, preset by an ideal switch at 2 us | by construction |

## What follows for a prediction

- Rows 5 and 10 can change a decision. Row 5 is in the rule of
  `EXPECTATION.md`; row 10 is avoided by both calendars of phase 0 and is the
  subject of a candidate prediction.
- Rows 6 and 8 decide the conditions (noise, temperature) under which a
  predicted state can be expected to hold, and how often.
- Row 12 is the hypothesis of the theorem with no counterpart at all in the
  circuit. A calendar that keeps the two ports of a cell in disjoint date
  bands, as the witness does, never meets it.
- Rows 1 to 4, 13 and 14 are the bench. They limit what a network result
  says about a network of circuits: the cells are transistors, the wires are
  not.
