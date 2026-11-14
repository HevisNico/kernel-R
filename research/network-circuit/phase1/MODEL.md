# The network theorem for this circuit cell

Phase 1, exploratory. This file says which model of
[`../../network-stability`](../../network-stability/THEOREM.md) is
instantiated for the two-cell circuit network, what is proved about it in
[`CircuitNetwork.lean`](CircuitNetwork.lean), what each number of the model
is in the circuit, and what is argued without a proof.

## 1. The model

The circuit cell stores one voltage per port and nothing else: no recovery
rate, no MARK. The model is therefore the **gain-only guarded model**,
`AutonomousFeedback.Model` of
[`AutonomousFeedback.lean`](../../network-stability/AutonomousFeedback.lean),
with four stored coordinates:

| Coordinate | Port | Receives |
|---|---|---|
| 0 | `a1`, port 1 of cell A | the sources of A |
| 1 | `a2`, port 2 of cell A | the return wire, from B |
| 2 | `b1`, port 1 of cell B | the forward wire, from A |
| 3 | `b2`, port 2 of cell B | the sources of B |

A **probe** is one pulse on one port. There are six kinds: a source of A
outside or inside the forward gate, a source of B outside or inside the
return gate, a forward-wire pulse, a return-wire pulse. A source inside its
gate routes one wire pulse if it fires; nothing else routes.

The **read law** is the circuit's own. In units where one dose of the port
is `d = 100 000`:

    score = - gap(port) + d x writes(port)        FIRE iff  0 <= score + error

A silent read adds one write to its port. `drive` is zero: a pulse is the
standard pulse whatever caused it (departure 2 of
[`../DEPARTURES.md`](../DEPARTURES.md)). Each port has its own dose in mV, so
each port has its own unit; nothing in the model adds scores of two ports.

| In the model | In the circuit | Measured by |
|---|---|---|
| `gap(port)` | distance from the preset of the port to its service threshold, in doses of that port | `cellscan.py`: training reads and a bisection, reads 22 units apart |
| `d` | one dose: the step of the stored voltage at a silent read | the same |
| `writes(port)` | number of doses written since the preset | counted on the waveform |
| `error` | everything else that moves a read: see section 3 | `cellscan.py`, `noisechar.py` |
| queue | the pulses not yet delivered | the router |

## 2. What is proved

`CircuitNetwork.lean` builds on `AutonomousFeedback.certified_feedback` and
adds no axiom (`check.sh` compiles it with warnings as errors and audits the
axioms: `propext`, `Classical.choice`, `Quot.sound` only).

For **every** gap and **every** number of sources `a0`, `a1` (A, before and
inside its gate), `b0`, `b1` (B):

1. `certificate`: the weights and reserves that `certified_feedback` asks
   for. A source inside a gate weighs 2, every other probe 1.
2. `circuit_certified`, whatever the errors: the queue is empty after
   `4 (a0 + 2 a1 + b0 + 2 b1)` steps and stays empty; no port ever has more
   than `a0 + a1 + b0 + b1` writes; no stored value reaches the rail if the
   rail is beyond that many doses.
3. `circuit_certified`, if every read of the zero-error run has room for the
   bounds of its error: the run with errors **is** the zero-error run. Same
   decisions, same routed pulses, same writes.
4. `circuit_predicted`: the same with one error budget per port instead of
   one per step (`PortMargins`, `nominal_of_port`).

"Room" is `HasRoom` of the theorem: a silent read stays silent under the
largest error, a FIRE stays a FIRE under the smallest.

For numbers, the margins are a finite check, done by the Lean kernel
(`decide +kernel`, not `native_decide`). The file does it for the nominal
cell of phase 0 on the calendar of phase 1; [`Instances.lean`](Instances.lean),
written by `predict.py`, does it for each measured instance.

## 3. The error budget E

The threshold of a port is measured with reads that come 22 units after the
previous pulse of the cell. A read of the network differs from those by:

| Term | Sign | Size | From |
|---|---|---|---|
| Help of a recent pulse on the same cell, either port | toward FIRE | the largest of the help measured at 16 units and at 18 units, over the 22-unit reference | `cellscan.py` (one read 16 units after a FIRE), `noisechar.py quiet` (trains 18 units apart) |
| No recent pulse at all | toward silence | 0.015 mV: what a pulse 22 units earlier gives, phase 0, nominal cell. Not measured per instance | [`../PERCELL.json`](../PERCELL.json) |
| Noise of the read | both | `K` standard deviations; the deviation is that of the FIRE latency in a noisy train, as an equivalent stored voltage | `noisechar.py noise` |
| Noise of the doses already written | both | added in quadrature to the noise of the read: `need` times the square of the dose deviation, one value per instance | `noisechar.py noise` |
| Threshold bracket | both | half the bracket of the bisection, 8 or 16 uV | `cellscan.py` |

    noise = sqrt(read noise^2 + need x dose noise^2)
    hi = + help + K x noise + half bracket
    lo = - 0.015 mV - K x noise - half bracket

The noise is not bounded, so `K` gives a rate and not a certificate
(departure 6). With `K = 3` and about fourteen FIRE reads on a source port,
a port that sits exactly at the edge of its room would miss once in about
fifty runs; a port with more room, much less often. The value of `K` is for
the preregistration to fix. Section 6 lists what is left out of E.

## 4. Conditions that hold by construction

[`calendars.py`](calendars.py) gives the calendar, `reciprocal(18)`: the
reciprocal construction of phase 0 with every source 18 units after the
previous one.

| Hypothesis | How it holds |
|---|---|
| Two pulses on one cell are at least 16 units apart | Sources of a cell are 18 units apart. A wire pulse starts between 0.35 and 1.43 units after the start of its source pulse (latency 0 to 1.06, delay 7/20, 0.02 for the noise grid). The gates and the 2-unit offset of B are placed so that the smallest distance, over all latencies, is 16.35 units on B and 16.92 on A (`calendars.separation`) |
| No arrival while a cell is protected | Protection ends at most 6.4 units after the start of a firing pulse (measured, section 5 of the README); 16 is more |
| No overlap of two pulses on one cell | A pulse lasts one unit |
| A port is free when its pulse arrives | A port is busy for 6.2 units |
| The router enforces it | `router.run(..., guard=16)` refuses, and records, any pulse that would start less than 16 units after the previous pulse of its cell or while the cell is protected. With this calendar the guard should never act; if it does, the run is outside the hypotheses and says so |
| A source fires on one side of a gate | Every source is at least 16.9 units from a gate boundary on the side that matters (`calendars.counts` fails otherwise) |
| Each source port is taught before its gate opens | Eight sources before the gate; the largest need seen is 5. So the number of wire pulses does not depend on which read of a marginal source port is the last silent one, unless that read is inside the gate |

**The negative control** is `reciprocal(8)`: the same sources, gates and
delays with a spacing of 8 units, that of the milestone-3 witness. Pulses on
one cell are then 7.3 to 8.9 units apart at the latencies seen (6.35 at the
least, over all latencies): at those latencies no arrival is protected, but
each pulse helps the next by about half a dose (phase 0: +0.63 to +0.70 mV
on the nominal cell). `calendars.holds_by_construction`
is false for it, and `predict.py` gives no prediction for a calendar where it
is false. The control is defined here and **has not been run** on any cell
with mismatch. What it would claim, to be fixed by the preregistration: on
the ports whose last silence has less margin than the help at 8 units, the
learned state departs from the zero-error run by one dose. The help at 8
units is not yet measured per instance.

## 5. Which departures of phase 0 go where

Rows of [`../DEPARTURES.md`](../DEPARTURES.md):

| Rows | Treatment in phase 1 |
|---|---|
| 1, 2, 4 (ideal router, regenerated pulse, gates as date bands) | unchanged: the result is about cells, not wires |
| 3 (wire date moved by at most 0.02 unit) | inside the separation bound |
| 5 (recent past) | in E, at the separation the calendar guarantees |
| 6 (noise not bounded) | in E, as `K` standard deviations; a rate, not a certificate |
| 7 (one dose) | one dose per port, measured per port; its scatter under noise is in E |
| 8 (drift) | 27 C only, where it is below 1 uV over a run (measured on the idle cell of each scan) |
| 9, 10, 11 (protected arrivals) | excluded by the calendar, refused by the guard |
| 12 (overlap is a joint read) | excluded by the calendar |
| 13 (busy port) | excluded by the calendar |
| 14 (cells exist from the start) | unchanged |

## 6. What is not proved, and what is left out

- **The order of the reads.** The Lean model reads its queue in order: all
  the sources of A, then those of B, then the wire pulses. The circuit reads
  in the order of the dates, where a wire pulse comes 1.3 units after its
  source. The two orders give the same word on every port, because in this
  model a read depends only on the writes of its own port and a port's
  pulses keep their order. `predict.py` checks it on every instance
  (`model.dated_run`). It is **not a Lean theorem**. The general
  order-independence result of the theory, `Schedule.network_memory`, does
  not apply: its hypothesis fails for two pending reads of one port when the
  first is the last silent one, the obstruction already recorded in
  [`RECIPROCAL_CLOSURE.md`](../../network-stability/RECIPROCAL_CLOSURE.md).
- **Ports without room.** `circuit_predicted` needs room at every read of
  the network. When one port has a read without room, the theorem as stated
  says nothing about the other ports either. `predict.py` then takes that
  read both ways and follows every case; a port keeps a prediction when its
  own reads have room. This rests on the same argument as the previous
  point and is **not a Lean theorem**. Two ways to close it: admit only
  instances where all four ports have room, or prove that a port's word
  depends only on its own errors and on the number of pulses it receives.
- **The help of a pulse on the other port of the cell.** Measured in phase 0
  on the nominal cell (same size as on the same port). On the instances, the
  help at 16 and 18 units is measured on the same port only.
- **The noise of a silent read.** The noise is measured on FIRE reads, by
  their latency, and assumed the same for the silent reads near the
  threshold.
- **The dose noise is one number per instance.** A port writes three to
  five doses in a train, too few for a deviation of its own. The value
  includes the error of reading a stored voltage on a noisy waveform.
- **Two cells in one deck share ideal supplies.** A read of one cell does
  not move the other: checked on every scan (the idle cell never fires, its
  stored voltages move by less than 1 uV).
