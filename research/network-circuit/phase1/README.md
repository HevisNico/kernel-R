# A network of R cells at transistor level: phase 1

**Exploratory. Nothing here is preregistered. No network has been run on a
cell with mismatch**: every simulation of this phase pulses one port of one
cell while all the others are idle. Phase 1 prepares what a prediction needs
and stops for review before any `PREDICTION.md`.

**Corrected after the review.** The version reviewed (commit `834971e`)
counted the noise of a read from the scatter inside one noisy run. Each
noisy run also shifts all the reads of a port by about 0.09 mV, the same
for the whole run. [`NOISE.md`](NOISE.md) has the finding, its origin and
what it changes. Sections 3 to 5 below carry the corrected numbers and say
where they differ from the version reviewed. No `PREDICTION.md` exists.

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
| [`NOISE.md`](NOISE.md), [`slownoise.py`](slownoise.py), [`noisegen.py`](noisegen.py), [`nominal.py`](nominal.py), [`NOISE_RUNS.json`](NOISE_RUNS.json), [`NOISE_GENERATOR.json`](NOISE_GENERATOR.json), [`NOMINAL_REHEARSAL.json`](NOMINAL_REHEARSAL.json) | the noise that a run adds to every read of a port, found after the review; the rehearsal on the nominal cell |
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
threshold by bisection (bracket 16 or 32 uV). `noisechar.py` then plays
trains of reads 18 units apart on each port: one of 26 reads without noise,
and five with noise, each in its own simulator process (one of 26 reads,
four of 10). All in mV across the storage capacitor.

| Instance | Port | Gap, mV | Dose, mV | Gap, doses | Need | Margin of the last silence, mV | Margin of the first FIRE, mV | Help at 16, mV | Help at 18 after a silence / a FIRE, mV | Noise within a run, mV | Run offsets, mV | Protected until, units |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 7101 | `a1` | 5.256 | 1.3589 | 3.868 | 4 | 1.179 | 0.180 | +0.018 | +0.011 / +0.011 | 0.055 | +0.08, +0.02, +0.05, +0.06 | 5.29 |
| 7101 | `a2` | 4.917 | 1.3488 | 3.645 | 4 | 0.870 | 0.479 | +0.012 | +0.004 / +0.004 | 0.055 | -0.02, +0.14, +0.04, -0.01, +0.03 | 5.30 |
| 7101 | `b1` | 4.127 | 1.3409 | 3.078 | 4 | 0.105 | 1.236 | +0.010 | +0.006 / +0.004 | 0.059 | +0.03, +0.07, +0.03, +0.08 | 5.60 |
| 7101 | `b2` | 5.314 | 1.3467 | 3.946 | 4 | 1.274 | 0.073 | +0.010 | -0.011 / -0.002 | 0.055 | +0.06, +0.08, +0.12 | 5.59 |
| 7102 | `a1` | 3.193 | 1.3492 | 2.367 | 3 | 0.495 | 0.854 | +0.012 | +0.002 / +0.002 | 0.066 | +0.01, -0.07, -0.01, +0.01, -0.01 | 6.38 |
| 7102 | `a2` | 4.079 | 1.3497 | 3.022 | 4 | 0.030 | 1.320 | +0.031 | -0.021 / -0.017 | 0.059 | -0.10, -0.10, -0.14, -0.16 | 6.39 |
| 7102 | `b1` | 6.127 | 1.3483 | 4.544 | 5 | 0.734 | 0.614 | +0.007 | +0.003 / -0.002 | 0.090 | +0.02, -0.09, +0.01, -0.00, +0.06 | 5.74 |
| 7102 | `b2` | 3.736 | 1.3562 | 2.755 | 3 | 1.024 | 0.333 | +0.011 | -0.000 / +0.001 | 0.062 | +0.08, -0.12, +0.04, -0.06, -0.09 | 5.74 |
| 7103 | `a1` | 3.629 | 1.3467 | 2.694 | 3 | 0.935 | 0.412 | +0.075 | +0.049 / +0.046 | 0.059 | -0.19, -0.08, +0.04, -0.07, -0.24 | 5.59 |
| 7103 | `a2` | 6.163 | 1.3495 | 4.567 | 5 | 0.765 | 0.585 | +0.013 | -0.016 / +0.003 | 0.079 | -0.24, +0.11, +0.03, -0.08, +0.14 | 5.59 |
| 7103 | `b1` | 2.970 | 1.3431 | 2.211 | 3 | 0.284 | 1.059 | +0.012 | +0.006 / +0.003 | 0.065 | +0.03, +0.06, -0.20, +0.01, -0.04 | 6.11 |
| 7103 | `b2` | 4.501 | 1.3558 | 3.320 | 4 | 0.433 | 0.923 | +0.011 | +0.038 / +0.004 | 0.054 | +0.01, +0.03, -0.06, -0.03, +0.02 | 6.11 |

A run offset is listed for each noisy train that gave the word of the train
without noise. Per instance, the noise between runs is the root mean square
of the run offsets of its four ports:

| Instance | Noise between runs, mV | Run offsets counted | Dose noise, mV |
|---|---|---|---|
| 7101 | 0.068 | 16 of 20 | 0.0082 |
| 7102 | 0.078 | 19 of 20 | 0.0088 |
| 7103 | 0.113 | 20 of 20 | 0.0081 |

What the tables show:

- **The cells differ.** Gaps from 2.2 to 4.6 doses, needs of 3, 4 and 5. The
  nominal cell of phase 0 had 3.59 on both ports.
- **At 16 units and more the recent past is small**: +0.08 mV at most, +0.01
  typically, against +0.63 to +0.70 mV at 8 units in phase 0. A latency
  repeats within about 0.003 without noise, which is 0.02 to 0.03 mV here;
  most of these helps are inside that.
- **Noise of a read: about 0.11 mV.** Inside a run, 0.05 to 0.09 mV. Between
  runs, 0.07 to 0.11 mV more: a noisy run shifts every read of a port by the
  same amount ([`NOISE.md`](NOISE.md)). The version reviewed had only the
  first.
- **Several ports sit close to a threshold.** The last silence of `a2` of
  7102 holds by 0.030 mV, that of `b1` of 7101 by 0.105 mV; the first FIRE of
  `b2` of 7101 holds by 0.073 mV. The method must say "no prediction" there.
- **Ports close to a threshold do change under noise.** Of the 60 noisy
  trains, 5 gave another word than the train without noise, all on ports
  with a margin of 0.18 mV or less: one dose more (`a1` and `b2` of 7101),
  or a FIRE one dose early (`b1` of 7101, `a2` of 7102). The version
  reviewed, with one noisy train per port, had seen none.

## 4. From the constants to the predicted learned state

`predict.py CONSTANTS.json PREDICTED.json Instances.lean [K]`. For each
port the budget is

    noise = sqrt(within a run^2 + between runs^2 + need x dose noise^2)
    hi = + largest help measured at 16 or 18 units + K x noise + half bracket
    lo = - 0.015 mV                                - K x noise - half bracket

and the zero-error run of the model on the calendar gives the word of each
port. Each read is then checked for room. With `K = 3`:

| Instance | Port | Budget, mV | Zero-error word | Least room, mV | Verdict | Writes | FIRE |
|---|---|---|---|---|---|---|---|
| 7101 | `a1` | -0.290 to +0.294 | 4 s, 14 F | -0.110 | no prediction | 4 or 5 | 13 to 14 |
| 7101 | `a2` | -0.290 to +0.286 | 4 s, 6 F | +0.189 | learned state predicted | 4 | 5 to 6 |
| 7101 | `b1` | -0.305 to +0.300 | 4 s, 6 F | -0.195 | no prediction | 3 or 4 | 5 to 7 |
| 7101 | `b2` | -0.291 to +0.286 | 4 s, 14 F | -0.218 | no prediction | 4 or 5 | 13 to 14 |
| 7102 | `a1` | -0.334 to +0.330 | 3 s, 15 F | +0.164 | predicted | 3 | 15 |
| 7102 | `a2` | -0.322 to +0.337 | 4 s, 6 F | -0.307 | no prediction | 3 or 4 | 6 to 7 |
| 7102 | `b1` | -0.394 to +0.385 | 5 s, 5 F | +0.220 | predicted | 5 | 5 |
| 7102 | `b2` | -0.325 to +0.321 | 3 s, 15 F | +0.007 | predicted | 3 | 15 |
| 7103 | `a1` | -0.407 to +0.466 | 3 s, 15 F | +0.005 | predicted | 3 | 15 |
| 7103 | `a2` | -0.439 to +0.438 | 5 s, 5 F | +0.146 | predicted | 5 | 5 |
| 7103 | `b1` | -0.415 to +0.412 | 3 s, 7 F | -0.128 | no prediction | 2 or 3 | 7 to 8 |
| 7103 | `b2` | -0.409 to +0.431 | 4 s, 14 F | +0.002 | predicted | 4 | 14 |

- **predicted**: every read of the port has room and it receives the same
  pulses in every case; its word is known.
- **learned state predicted**: its own reads have room, but the number of
  pulses it receives depends on a port without room; its writes are known,
  its number of FIRE is not.
- **no prediction**: one of its reads has no room. The writes are then one
  of two values.

The verdicts of ports of an instance that has a read without room rest on an
argument that is not a Lean theorem ([`MODEL.md`](MODEL.md), section 6);
they are shown for information and enter no claim.

| Instance | Ports with a known word: without noise, K = 2, K = 3, K = 4 | Every read has room |
|---|---|---|
| 7101 | 4, 0, 0, 0 | without noise only |
| 7102 | 3, 3, 3, 2 | never |
| 7103 | 4, 4, 3, 0 | without noise and at K = 2 |

**No development instance has room on its four ports at `K = 3`.** In the
version reviewed, with the smaller budget, 7103 had, and `a1` of 7101 was
"predicted" by 0.005 mV; one of the five noisy trains of that port then took
a fifth dose. "Without noise" is the budget of a run without noise: the help
and the threshold bracket only. Two instances of three have room for it on
their four ports, and `Instances.lean` has those margins checked by the Lean
kernel, so `circuit_dated_predicted` gives their learned state, 4, 4, 4, 4
and 3, 5, 3, 4 doses, for a run without noise.

No network run exists on these instances against which to compare these
lines.

## 5. Cost

Measured, one processor per simulation, four at a time on a 4-processor
container:

| Run | Simulated | Wall time |
|---|---|---|
| One port scanned (`cellscan.py`), two cells in the deck, no noise | 9 to 12 ms | 200 to 300 s; 16 minutes for the four ports |
| Trains alone on the four ports, 26 reads each, no noise | 18.9 ms, 104 pulses | 970 to 1 060 s |
| The same with noise | 18.9 ms, 104 pulses | 1 390 to 1 410 s |
| Trains alone with noise, 10 reads each | 7.4 ms, 40 pulses | 545 to 556 s |
| Network run on the nominal cell, noise, calendar of 18 units | 10 ms, 56 pulses | 678 to 686 s |

Memory is 0.35 GB per simulation since the fault of section 6 is corrected.

Not run, estimated: the 8-unit control with noise, 4.6 ms and the same
pulses, 5 to 11 minutes; a network run without noise, about 8 minutes.

**Per instance**: four scans, one train without noise and four noisy trains
of 10 reads cost about 70 minutes of one processor (60 if the train without
noise is cut to 10 reads). Each noisy network run adds 11.4 minutes.

**What fits in 4 h on two machines** depends on how the bound is computed.
From measured times, eight instances with three noisy runs each take about
14 processor-hours of the 16. From time limits, as for the supervisor
campaign, with limits at 1.25 times the measured times: six instances, with
ten runs on at most two of them. [`NOISE.md`](NOISE.md), section 7.

**The yield counts more than the time.** With `K = 3` and the corrected
budget a port has room about once in two, an instance on its four ports
about once in twenty.

**Three cells**, later: a ring with three gates. Six ports to measure, three
cells in the deck, a calendar of about 700 units: about 24 minutes for a
noisy network run. The router takes any number of cells and edges;
`calendars.py`, `model.py` and the Lean files are written for two cells and
would have to be extended.

**Layout 2.2**, later: phase 0 measured a factor 1.2 on one nominal cell
with the extracted netlist. Mismatch on the extracted netlist has not been
tried; nothing between the cells is extracted.

## 6. What went wrong, and what is open

- **The error budget lacked the noise between runs.** Found after the
  review, before any preregistration. [`NOISE.md`](NOISE.md).
- **A memory fault in the bench, found and corrected.** The session cleared
  the simulator's list of saved signals before the run started, so ngspice
  kept all 1 832 signals in memory instead of 37: about 40 MB per pulse. The
  first attempt at the six trains ran four at a time; three were killed by
  the memory limit of the container (14.3 GB), two were stopped by hand
  before they met it, one finished. `net.py` now sets the list again before
  the run starts. One scan was run again with the correction: the waveform is
  the same byte for byte (the file differs by its date line only). The
  trains of `MEASURES.json` are from the corrected bench; the twelve scans
  are from before the correction. Phase 0 was affected in memory only. The
  bench of the supervisor campaign
  (`../../sky130-supervisor-closure/sim.py`) has the same two lines; it is
  frozen and was not changed.
- **The 8-unit control lacks a measure**: the help at 8 units, per instance.
- **One argument is not a Lean theorem**: ports without room. `MODEL.md`,
  section 6. It is kept out of every claim. The order of the dates is
  proved (`DatedOrder.lean`).
- **The noise of a silent read is assumed** equal to that of a FIRE read.
- **Five noisy runs per port.** The noise between runs of an instance rests
  on 16 to 20 run offsets: a root mean square known to about 20 %.
- **The latency of the simulator repeats to about 0.003** without noise,
  which bounds how small a help can be measured this way.

## Decisions and what is open

Taken at the review of phase 1: `K = 3`; a claim only on instances where
all four ports have full room, the others run and reported without claim;
the order of the dates as a Lean lemma before any preregistration (done,
`DatedOrder.lean`); the 8-unit calendar on one full-room instance as
negative control, with the prediction that the predictor that ignores the
help fails on at least one port; new seeds only; ten noisy network runs per
full-room instance, three per other instance; two machines, at most 4 h.

Open again since the noise between runs was found, for the owner:
[`NOISE.md`](NOISE.md), section 7. The preregistration is paused.

## Reproduction

```sh
python -B research/network-circuit/phase1/cellscan.py OUT tt_mm 7101 a 1 /usr/bin/ngspice PDK
python -B research/network-circuit/phase1/noisechar.py OUT tt_mm 7101 noise /usr/bin/ngspice PDK
python -B research/network-circuit/phase1/noisechar.py OUT tt_mm 7101 noise /usr/bin/ngspice PDK 10
python -B research/network-circuit/phase1/collect.py DATA MEASURES.json 7101 7102 7103
python -B research/network-circuit/phase1/constants.py MEASURES.json CONSTANTS.json
python -B research/network-circuit/phase1/predict.py CONSTANTS.json PREDICTED.json Instances.lean
bash research/network-circuit/phase1/check.sh
python -B -m unittest research/network-circuit/phase1/test_phase1.py
```

Raw waveforms are not in Git; `MEASURES.json` has the SHA-256 of each deck
and waveform. The noise of a run is seeded by the simulator's process
number, so a noisy train does not repeat exactly.
