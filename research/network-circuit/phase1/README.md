# A network of R cells at transistor level: phase 1

**Exploratory. Nothing here is preregistered. No network has been run on a
cell with mismatch**: every simulation of this phase pulses one port of one
cell while all the others are idle. Phase 1 prepares what a prediction needs
and stops for review before any `PREDICTION.md`.

Simulations: ngspice 42, SKY130 models, the cell of
[`../../circuit/cell.spice`](../../circuit/cell.spice) with the junction
areas of stage J, 27 C, mismatch section `tt_mm`. Three **development
instances**: two cells in one deck, mismatch seeds 7101, 7102, 7103. They
served to build the procedure; a registered experiment should use other
seeds.

| File | What it is |
|---|---|
| [`MODEL.md`](MODEL.md) | the model, what is proved, the error budget, the conditions that hold by construction, what is not proved |
| [`CircuitNetwork.lean`](CircuitNetwork.lean), [`DatedOrder.lean`](DatedOrder.lean), [`check.sh`](check.sh), [`Audit.lean`](Audit.lean) | the instance of the network theorem for this circuit network, and the lemma on the order of the dates |
| [`calendars.py`](calendars.py) | the calendar with pulses 18 units apart, and the 8-unit negative control |
| [`cellscan.py`](cellscan.py), [`noisechar.py`](noisechar.py) | the per-port measures: threshold, dose, help of a recent pulse; trains alone, without and with noise |
| [`collect.py`](collect.py), [`MEASURES.json`](MEASURES.json) | what each pulse of those runs did, and the hashes of decks and waveforms |
| [`constants.py`](constants.py), [`CONSTANTS.json`](CONSTANTS.json) | the constants of the model per port |
| [`model.py`](model.py), [`predict.py`](predict.py), [`PREDICTED.json`](PREDICTED.json), [`Instances.lean`](Instances.lean) | from the constants to the predicted learned state, and the same margins checked by the Lean kernel |
| [`summary.py`](summary.py) | prints the tables below |
| [`test_phase1.py`](test_phase1.py) | checks without a simulator; run by `.github/workflows/network-circuit.yml` with `check.sh` |

Changed outside this directory: [`../net.py`](../net.py) (each integrator
can have its own leak control; a memory fault of the bench, see section 6),
[`../router.py`](../router.py) (the guard).

## 1. The theorem, for this cell

[`MODEL.md`](MODEL.md) has the detail. In short:

- The model is the gain-only guarded model of
  `../../network-stability/AutonomousFeedback.lean`: four stored gains, the
  read law `FIRE iff 0 <= -gap + d x writes + error`, one dose per silent
  read, one wire pulse per FIRE of a source inside its gate.
- `CircuitNetwork.lean` proves, for every gap and every number of sources:
  the queue empties, no port takes more writes than there are sources, and,
  **if every read of the zero-error run has room for the error budget of its
  port, the run with errors is the zero-error run** (`circuit_predicted`).
  No new axiom; under a minute to check.
- The recent-past effect and the noise are in the budget E, per port, as
  measured (section 3).
- [`DatedOrder.lean`](DatedOrder.lean), added after the review of phase 1:
  with no same-date tie on a port, the run in the order of the dates is the
  queue run of the model, read for read, with errors inside the budgets
  (`circuit_dated_predicted`).
- Not proved in Lean, and kept out of every claim: what remains of a
  prediction when one port has a read without room.

## 2. Conditions that hold by construction

The calendar is `calendars.reciprocal(18)`: A has 18 sources 18 units apart
(8 before its forward gate, 10 inside), B has 8 sources during A's first
eight and 10 after A's last, inside the return gate; delays 7/20; horizon
500 units, 10 ms.

- Two pulses on one cell are at least 16.35 units apart for every latency
  between 0 and 1.06. So no pulse arrives on a protected cell (protection
  ends by 6.4 units), none overlaps another, none finds its port busy.
- `router.run(..., guard=16)` refuses and records any pulse that would break
  this. On this calendar it should never act.
- The **negative control** is `calendars.reciprocal(8)`, the spacing of the
  milestone-3 witness: the hypotheses do not hold (pulses 7.3 to 8.9 units
  apart, each helping the next by about half a dose), and `predict.py`
  refuses to predict it. It is defined, not run. What it should claim is for
  the preregistration; it needs the help at 8 units per instance, which is
  not measured yet.

## 3. Constants per cell, with mismatch

Per port, with every other port idle: `cellscan.py` trains the port with
reads 22 units apart, reads once 16 units after a FIRE, then finds the
threshold by bisection (bracket 16 or 32 uV). `noisechar.py` then plays a
train of 26 reads 18 units apart on each port, once without noise and once
with noise. All in mV across the storage capacitor.

| Instance | Port | Gap, mV | Dose, mV | Gap, doses | Need | Margin of the last silence, mV | Margin of the first FIRE, mV | Help at 16, mV | Help at 18 after a silence / a FIRE, mV | Noise of a read, mV | Protected until, units |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 7101 | `a1` | 5.256 | 1.3589 | 3.868 | 4 | 1.179 | 0.180 | +0.018 | +0.011 / +0.011 | 0.049 | 5.29 |
| 7101 | `a2` | 4.917 | 1.3488 | 3.645 | 4 | 0.870 | 0.479 | +0.012 | +0.004 / +0.004 | 0.050 | 5.30 |
| 7101 | `b1` | 4.127 | 1.3409 | 3.078 | 4 | 0.105 | 1.236 | +0.010 | +0.006 / +0.004 | 0.065 | 5.60 |
| 7101 | `b2` | 5.314 | 1.3467 | 3.946 | 4 | 1.274 | 0.073 | +0.010 | -0.011 / -0.002 | 0.056 | 5.59 |
| 7102 | `a1` | 3.193 | 1.3492 | 2.367 | 3 | 0.495 | 0.854 | +0.012 | +0.002 / +0.002 | 0.073 | 6.38 |
| 7102 | `a2` | 4.079 | 1.3497 | 3.022 | 4 | 0.030 | 1.320 | +0.031 | -0.021 / -0.017 | 0.059 | 6.39 |
| 7102 | `b1` | 6.127 | 1.3483 | 4.544 | 5 | 0.734 | 0.614 | +0.007 | +0.003 / -0.002 | 0.090 | 5.74 |
| 7102 | `b2` | 3.736 | 1.3562 | 2.755 | 3 | 1.024 | 0.333 | +0.011 | -0.000 / +0.001 | 0.059 | 5.74 |
| 7103 | `a1` | 3.629 | 1.3467 | 2.694 | 3 | 0.935 | 0.412 | +0.075 | +0.049 / +0.046 | 0.055 | 5.59 |
| 7103 | `a2` | 6.163 | 1.3495 | 4.567 | 5 | 0.765 | 0.585 | +0.013 | -0.016 / +0.003 | 0.093 | 5.59 |
| 7103 | `b1` | 2.970 | 1.3431 | 2.211 | 3 | 0.284 | 1.059 | +0.012 | +0.006 / +0.003 | 0.058 | 6.11 |
| 7103 | `b2` | 4.501 | 1.3558 | 3.320 | 4 | 0.433 | 0.923 | +0.011 | +0.038 / +0.004 | 0.052 | 6.11 |

What the table shows:

- **The cells differ.** Gaps from 2.2 to 4.6 doses, needs of 3, 4 and 5. The
  nominal cell of phase 0 had 3.59 on both ports.
- **At 16 units and more the recent past is small**: +0.08 mV at most, +0.01
  typically, against +0.63 to +0.70 mV at 8 units in phase 0. A latency
  repeats within about 0.003 without noise, which is 0.02 to 0.03 mV here;
  most of these helps are inside that.
- **Noise of a read: 0.05 to 0.09 mV** as an equivalent stored voltage, from
  21 to 23 FIRE reads per port. The dose under noise deviates by 0.007 to
  0.009 mV (root mean square, one value per instance).
- **Several ports sit close to a threshold.** The last silence of `a2` of
  7102 holds by 0.030 mV, that of `b1` of 7101 by 0.105 mV; the first FIRE of
  `b2` of 7101 holds by 0.073 mV. The method must say "no prediction" there.
- Every train alone, without and with noise, gave the word of the isolated
  scan: `need` silent reads, then FIRE to the end (12 ports, 24 trains).
  This includes the ports close to a threshold; one noisy train per port
  says little about them.

## 4. From the constants to the predicted learned state

`predict.py CONSTANTS.json PREDICTED.json Instances.lean [K]`. For each
port the budget is

    noise = sqrt(read noise^2 + need x dose noise^2)
    hi = + largest help measured at 16 or 18 units + K x noise + half bracket
    lo = - 0.015 mV                                - K x noise - half bracket

and the zero-error run of the model on the calendar gives the word of each
port. Each read is then checked for room. With `K = 3`:

| Instance | Port | Budget, mV | Zero-error word | Least room, mV | Verdict | Writes | FIRE |
|---|---|---|---|---|---|---|---|
| 7101 | `a1` | -0.176 to +0.179 | 4 s, 14 F | +0.005 | predicted | 4 | 14 |
| 7101 | `a2` | -0.177 to +0.174 | 4 s, 6 F | +0.301 | learned state predicted | 4 | 5 to 6 |
| 7101 | `b1` | -0.230 to +0.224 | 4 s, 6 F | -0.120 | no prediction | 3 or 4 | 6 to 7 |
| 7101 | `b2` | -0.196 to +0.191 | 4 s, 14 F | -0.123 | no prediction | 4 or 5 | 13 to 14 |
| 7102 | `a1` | -0.244 to +0.241 | 3 s, 15 F | +0.254 | predicted | 3 | 15 |
| 7102 | `a2` | -0.206 to +0.222 | 4 s, 6 F | -0.192 | no prediction | 3 or 4 | 6 to 7 |
| 7102 | `b1` | -0.307 to +0.298 | 5 s, 5 F | +0.308 | predicted | 5 | 5 |
| 7102 | `b2` | -0.206 to +0.202 | 3 s, 15 F | +0.127 | predicted | 3 | 15 |
| 7103 | `a1` | -0.193 to +0.253 | 3 s, 15 F | +0.218 | predicted | 3 | 15 |
| 7103 | `a2` | -0.309 to +0.307 | 5 s, 5 F | +0.276 | predicted | 5 | 5 |
| 7103 | `b1` | -0.203 to +0.201 | 3 s, 7 F | +0.083 | predicted | 3 | 7 |
| 7103 | `b2` | -0.195 to +0.218 | 4 s, 14 F | +0.215 | predicted | 4 | 14 |

- **predicted**: every read of the port has room and it receives the same
  pulses in every case; its word is known.
- **learned state predicted**: its own reads have room, but the number of
  pulses it receives depends on a port without room; its writes are known,
  its number of FIRE is not. `a2` of 7101 receives 9 or 10 return pulses
  because `b2`, its source, may need a fifth dose inside the gate.
- **no prediction**: one of its reads has no room. The writes are then one
  of two values.

| Instance | Every read has room | Possible terminal states | FIRE of A | FIRE of B |
|---|---|---|---|---|
| 7101 | no | 6 | 19 or 20 | 19 to 21 |
| 7102 | no | 2 | 21 or 22 | 20 |
| 7103 | **yes** | 1 | 20 | 21 |

Instance 7103 is the case the theorem covers as stated: `Instances.lean`
has its margins checked by the Lean kernel, so `circuit_predicted` gives its
learned state, 3, 5, 3 and 4 doses, for every error inside the budgets. For
7101 and 7102 the same file checks that the margins do **not** hold.

With `K = 2`, 3, 4 the ports with a known word number 1, 1, 0 of 4 for
7101; 3, 3, 3 for 7102; 4, 4, 4 for 7103. Eight ports of twelve at
`K = 3`. Whether a registered claim is per port, or only for instances
where every read has room (one of three here), is a choice for the review.

No network run exists against which to compare these lines. That is the
point of stopping here.

## 5. Cost

Measured in this phase, one processor per simulation, four at a time on a
4-processor container:

| Run | Simulated | Wall time |
|---|---|---|
| One port scanned (`cellscan.py`), two cells in the deck, no noise | 9 to 12 ms | 200 to 300 s; 16 minutes for the four ports |
| Trains alone on the four ports, no noise | 18.9 ms, 104 pulses | 970 to 1 060 s |
| The same with noise | 18.9 ms, 104 pulses | 1 390 to 1 410 s |

Noise costs a factor 1.4 here. The trains have one pulse per cell every 18
units, the density of the network calendar, so a network run should cost in
proportion to its length:

| Not run, estimated | Simulated | One processor |
|---|---|---|
| Network run, 2 cells with mismatch, noise, calendar of 18 units | 10 ms, at most 56 pulses | about 12 minutes |
| The same without noise | 10 ms | about 9 minutes |
| The 8-unit control, noise | 4.6 ms, the same pulses | 6 to 12 minutes |
| All the measures of one instance (4 scans, 2 trains) | | about 56 minutes |

**Two cells with mismatch and noise.** One instance with its measures,
three noisy network runs and one control: about 1 h 45 of one processor.
Twenty instances: about 35 processor-hours, 9 hours on one container, half
on two. Memory is 0.35 GB per simulation since the fault of section 6 is
corrected.

**The yield counts as much as the time.** With `K = 3` a port has room when
its gap is more than 0.2 to 0.3 mV away from a whole number of doses, on
both sides: roughly two ports in three, as seen here (8 of 12). An instance
with room on all four ports is then about one in five.

**Three cells**, later: a ring with three gates. Six ports to measure, three
cells in the deck, a calendar of about 700 units: about 26 minutes for a
noisy network run and 1 h 25 of measures per instance. The router takes any
number of cells and edges; `calendars.py`, `model.py` and the Lean
certificate are written for two cells and would have to be extended.

**Layout 2.2**, later: phase 0 measured a factor 1.2 on one nominal cell
with the extracted netlist. Mismatch on the extracted netlist has not been
tried; nothing between the cells is extracted.

## 6. What went wrong, and what is open

- **A memory fault in the bench, found and corrected.** The session cleared
  the simulator's list of saved signals before the run started, so ngspice
  kept all 1 832 signals in memory instead of 37: about 40 MB per pulse. The
  first attempt at the six trains ran four at a time; three were killed by
  the memory limit of the container (14.3 GB), two were stopped by hand
  before they met it, one finished. `net.py` now sets the list again before the run
  starts. One scan was run again with the correction: the waveform is the
  same byte for byte (the file differs by its date line only). The six
  trains of `MEASURES.json` are from the corrected bench; the twelve scans
  are from before the correction. Phase 0 was affected in memory only. The
  bench of the supervisor campaign
  (`../../sky130-supervisor-closure/sim.py`) has the same two lines; it is
  frozen and was not changed.
- **The 8-unit control lacks a measure**: the help at 8 units, per instance.
- **One argument is not a Lean theorem**: ports without room. `MODEL.md`,
  section 6. The order of the dates is now proved (`DatedOrder.lean`).
- **The noise of a silent read is assumed** equal to that of a FIRE read.
- **One noisy train per port.** The noise of a read rests on about 22 reads
  per port: a standard deviation known to about 15 %.
- **The latency of the simulator repeats to about 0.003** without noise,
  which bounds how small a help can be measured this way.

## For the review

1. `K`, and whether a claim is per port or per instance with full room.
2. Whether the two arguments of `MODEL.md` section 6 must become Lean
   theorems before a preregistration.
3. The content of the negative control, and its extra measure.
4. How many instances and repetitions, from the costs above.
5. New seeds for the registered instances.

## Reproduction

```sh
python -B research/network-circuit/phase1/cellscan.py OUT tt_mm 7101 a 1 /usr/bin/ngspice PDK
python -B research/network-circuit/phase1/noisechar.py OUT tt_mm 7101 noise /usr/bin/ngspice PDK
python -B research/network-circuit/phase1/collect.py DATA MEASURES.json 7101 7102 7103
python -B research/network-circuit/phase1/constants.py MEASURES.json CONSTANTS.json
python -B research/network-circuit/phase1/predict.py CONSTANTS.json PREDICTED.json Instances.lean
bash research/network-circuit/phase1/check.sh
python -B -m unittest research/network-circuit/phase1/test_phase1.py
```

Raw waveforms are not in Git; `MEASURES.json` has the SHA-256 of each deck
and waveform. The noise of a run is seeded by the simulator's process
number, so a noisy train does not repeat exactly.
