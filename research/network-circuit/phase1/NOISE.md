# The noise that a run adds to every read of a port

Phase 1, exploratory, written after the review of phase 1. **Nothing is
preregistered and no network has been run on a cell with mismatch.**

The error budget of phase 1, as reviewed (commit `834971e`), counted the
noise of a read from the scatter of the FIRE latency **inside one noisy
run**. That misses a second part: each noisy run shifts all the reads of a
port by an amount that stays the same for the whole run and changes from
run to run. It was found while preparing the preregistration, before any
`PREDICTION.md` was written. This file gives the evidence, where the shift
comes from, the corrected budget, and what it does to the plan.

## 1. What was measured

All in mV across the storage capacitor, by the latency of a FIRE divided by
the slope of latency against stored voltage, as in `constants.py`.

| Runs | What they give | File |
|---|---|---|
| 4 network runs on the nominal cell, calendar of 18 units, noise, one simulator process each | the same cell and the same reads, four draws of noise | [`NOMINAL_REHEARSAL.json`](NOMINAL_REHEARSAL.json) |
| Per development instance: the noisy train of 26 reads of phase 1, and 4 more noisy trains of 10 reads per port, one process each | 5 draws of noise per port, against the train without noise | [`MEASURES.json`](MEASURES.json), [`NOISE_RUNS.json`](NOISE_RUNS.json) |
| The noise sources alone, without a circuit: 200 draws at each of five run lengths | what the generator does | [`NOISE_GENERATOR.json`](NOISE_GENERATOR.json) |

The **run offset** of a port in a noisy run is (FIRE latency without noise
minus mean FIRE latency of the run) divided by the slope: positive when the
run reads the port as stronger than it is without noise. It is taken only
when the noisy train gave the word of the train without noise.

## 2. The evidence

**The nominal cell.** The mean FIRE latency of a port differs between the
four runs by 0.009 to 0.014 (standard deviation), where the latency inside a
run scatters by 0.007 to 0.009. A mean over 6 or 14 reads cannot move that
much by the scatter inside a run. With a slope of 0.15 per mV, the run
offset is 0.06 to 0.09 mV, the scatter inside a run 0.05 mV.

**The development instances.** 55 run offsets, 12 ports:

| | mV |
|---|---|
| Root mean square of the run offsets | 0.090 |
| Their mean | -0.011 |
| Standard deviation between the runs of one port (43 degrees of freedom) | 0.078 |
| Scatter of a read inside a run | 0.064 |
| A read against the noise-free model: both together | 0.11 |

The budget of phase 1 had 0.05 to 0.09 mV per port. The real figure is
about 0.11.

## 3. Where it comes from

The bench has four noise sources ([`../../circuit/DESIGN.md`](../../circuit/DESIGN.md),
"Noise"). Per port: the amplifier of the integrator that holds the stored
voltage (`nzo`), the window comparator (`nzc`), the mirror current. Per
cell: the FIRE comparator (`nzm`). Each voltage source is white noise
sampled every 0.4 us plus a flicker part.

A least-squares fit of the 55 run offsets on what the sources did in the
same run ([`slownoise.py`](slownoise.py)):

| Terms | Coefficients | Left, mV rms |
|---|---|---|
| none | | 0.090 |
| stored voltage before the first pulse, against the same without noise | -0.58 | 0.081 |
| mean of `nzo` over the reads of the run | -0.81 | 0.066 |
| mean of `nzm` over the reads of the run | +0.12 | 0.086 |
| the first two together | -0.99, -1.09 | 0.028 |
| the three together | -0.96, -1.07, +0.06 | 0.024 |

Two things, both of the integrator amplifier of the port, explain the run
offset, each with a coefficient of one:

1. **The preset samples the noise.** The preset sets the stored node while
   the amplifier input carries its noise; when the preset ends, the value of
   that noise stays in the stored voltage. It is there for the whole run.
   Standard deviation of the stored voltage after a noisy preset: 0.065 mV.
2. **The slow part of the amplifier noise.** The mean of `nzo` over a run
   is not zero: its standard deviation over the runs is 0.074 mV. The stored
   node follows it, so every read of the run sees the port shifted by it.

The FIRE comparator of the cell adds 0.06 mV per mV of its own run mean,
about 0.01 mV. The window comparator adds next to nothing.

**Per port, not per cell.** The two sources that matter are per port. The
run offsets of the two ports of a cell in the same run correlate at 0.23
(26 pairs).

**It does not depend on the length of the run.**

| Run length | Standard deviation of the run mean of `nzo`, mV | of its sample at the preset | of its 20 us windows inside a run |
|---|---|---|---|
| 2.5 ms | 0.065 | 0.129 | 0.056 |
| 5 ms | 0.067 | 0.123 | 0.059 |
| 10 ms | 0.068 | 0.128 | 0.061 |
| 20 ms | 0.076 | 0.132 | 0.064 |
| 40 ms | 0.076 | 0.126 | 0.067 |

A longer run does not average it out: the generator gives each run a mean
of its own. The trains of 26 reads (19 ms) have run offsets of 0.101 mV rms,
those of 10 reads (7 ms) 0.086 mV. The flicker amplitude given to the
generator for `nzo` is 0.038 mV rms; the run mean it produces is twice
that. `DESIGN.md` already says that the injection "puts more of the op-amp
noise at low frequency than the block has, which overstates the noise of a
read of the stored voltage". This is that overstatement, measured. Whether
the noise model should be changed is not decided here; the numbers below
keep it as it is.

**It cannot be removed by looking at the run before its first pulse.** The
stored node averaged over the 45 us before the first pulse, against the
same without noise, explains little of the run offset (0.071 mV left of
0.090): the slow part also wanders during the run (its windows 360 us apart
scatter by 0.06 mV inside a run). The offset is an error to budget, not a
quantity to subtract.

## 4. The corrected budget

`constants.py` now takes, per port, the scatter inside a run pooled over its
noisy trains, and, per instance, the root mean square of the run offsets of
its four ports. `predict.py` uses

    noise = sqrt(within a run^2 + between runs^2 + need x dose noise^2)
    hi = + help + K x noise + half bracket
    lo = - 0.015 mV - K x noise - half bracket

| Instance | Between runs, mV | Run offsets counted | Within a run, per port, mV |
|---|---|---|---|
| 7101 | 0.068 | 16 of 20 | 0.055 to 0.059 |
| 7102 | 0.078 | 19 of 20 | 0.059 to 0.090 |
| 7103 | 0.113 | 20 of 20 | 0.054 to 0.079 |

**A check on trains alone.** Five noisy trains per port, sixty in all. Five
gave another word than the train without noise:

| Instance | Port | Margin, mV | Words of its noisy trains that differ | Verdict at K = 3, corrected | Verdict at K = 3, as reviewed |
|---|---|---|---|---|---|
| 7101 | `a1` | first FIRE 0.180 | `sssssFFFFF`: one FIRE missed, a fifth dose | no prediction | **predicted** |
| 7101 | `b1` | last silence 0.105 | `sssFFFFsFF`: fires one dose early, takes the dose four reads later | no prediction | no prediction |
| 7101 | `b2` | first FIRE 0.073 | `sssssFFFFF`, `ssssFFFsFF` | no prediction | no prediction |
| 7102 | `a2` | last silence 0.030 | `sssFFFFFFF`: fires one dose early | no prediction | no prediction |

With the corrected budget, the seven ports that keep a verdict other than
"no prediction" gave the word of the noise-free train in 35 trains of 35;
the five ports with "no prediction" gave another word in 5 trains of 25.
With the budget as reviewed, `a1` of 7101 was "predicted", by 0.005 mV, and
one of its five trains took a fifth dose. This is a check on single ports,
with the trains that also set the budget: it shows that the correction was
needed, not that the corrected budget is right.

## 5. What it does to the predictions of phase 1

`K = 3`, corrected:

| Instance | Port | Budget, mV | Least room, mV | Verdict | Writes |
|---|---|---|---|---|---|
| 7101 | `a1` | -0.290 to +0.294 | -0.110 | no prediction | 4 or 5 |
| 7101 | `a2` | -0.290 to +0.286 | +0.189 | learned state predicted | 4 |
| 7101 | `b1` | -0.305 to +0.300 | -0.195 | no prediction | 3 or 4 |
| 7101 | `b2` | -0.291 to +0.286 | -0.218 | no prediction | 4 or 5 |
| 7102 | `a1` | -0.334 to +0.330 | +0.164 | predicted | 3 |
| 7102 | `a2` | -0.322 to +0.337 | -0.307 | no prediction | 3 or 4 |
| 7102 | `b1` | -0.394 to +0.385 | +0.220 | predicted | 5 |
| 7102 | `b2` | -0.325 to +0.321 | +0.007 | predicted | 3 |
| 7103 | `a1` | -0.407 to +0.466 | +0.005 | predicted | 3 |
| 7103 | `a2` | -0.439 to +0.438 | +0.146 | predicted | 5 |
| 7103 | `b1` | -0.415 to +0.412 | -0.128 | no prediction | 2 or 3 |
| 7103 | `b2` | -0.409 to +0.431 | +0.002 | predicted | 4 |

| Instance | Ports with a known word: without noise, K = 2, K = 3, K = 4 | Every read has room |
|---|---|---|
| 7101 | 4, 0, 0, 0 | without noise only |
| 7102 | 3, 3, 3, 2 | never |
| 7103 | 4, 4, 3, 0 | without noise and at K = 2 |

**No development instance has room on its four ports at K = 3.** In phase 1
as reviewed, 7103 had. A port has room when its gap is more than about
0.3 to 0.45 mV away from a whole number of doses on both sides; a dose is
1.35 mV. That leaves roughly half the ports (7 of 12 here, three of them by
less than 0.01 mV), and an instance with four such ports about once in
twenty.

"Without noise" is the budget with `K = 0`: the help and the threshold
bracket only, 0.02 to 0.08 mV. It concerns a run without noise, where there
is no preset sample and no slow part. Two development instances of three
have room for it on their four ports; `Instances.lean` has both budgets
checked by the Lean kernel.

## 6. The nominal rehearsal

Four noisy network runs on the nominal cell, which is not one of the
instances and whose words were in `CircuitNetwork.lean` before the runs:

| | |
|---|---|
| Words | all four ports as the model, in the four runs: `a1` and `b2` four silences then 14 FIRE, `b1` and `a2` four silences then 6 FIRE |
| FIRE, routed pulses | 40 and 20 per run; nothing left in the queue |
| Guard at 16 units | never acted; the closest two pulses on one cell were 17.24 units apart |
| Cost | 678 to 686 s per run, four at a time |

It says that the bench plays the calendar as designed and what a run
costs. The nominal cell has 0.80 and 0.55 mV of margin; it tests nothing
about cells close to a threshold.

## 7. What this changes for a preregistration

The decisions taken at the review were: `K = 3`; a claim only on instances
with room on their four ports; ten noisy network runs on those, three on
the others; nine new instances; at most 4 h on two machines.

- **With the corrected budget an instance with full room is rare**: about
  one in twenty. With the instances that fit in 4 h, the claim would most
  likely end "not established".
- **Nine instances do not fit in 4 h when the bound is computed from time
  limits**, as it was for the supervisor campaign. Measured costs, one
  processor, four at a time: a scan of one port 200 to 300 s; a noisy train
  of 10 reads per port 545 to 556 s; a noisy network run 683 s. With limits
  at 1.25 times these and four noisy trains per instance, six instances
  fit; with ten runs on at most one or two of them.

Options, for the owner:

1. **Add a claim without noise.** One network run without noise per
   instance; the claim covers the instances with room for the noise-free
   budget (about four in five by the margins seen; two of the three here).
   It tests the core statement, the learned state of mismatched cells from
   their measured margins, with nothing statistical in it. The noisy claim
   at `K = 3` stays as decided and will usually have no eligible instance.
2. **Keep the decisions as they are**, with the corrected budget and six or
   seven instances, and accept that "not established" is the likely
   outcome.
3. **`K = 2` under noise.** About six ports in ten have room, an instance
   about one in seven. A port at the edge of its room then departs in about
   2 % of the runs, so a claim over ten runs and four ports can fail by
   construction.
4. **A claim of rates instead of certainties.** For every port, the model
   and the measured noise give the probability of each number of doses; the
   runs test those probabilities. It uses every instance, but it is a
   different kind of claim and needs a statistical test fixed in advance.
5. **Change the noise model**, since the slow part is known to be
   overstated. That is a change to `../../circuit`, outside this study.

My recommendation is option 1 with five or six instances. It is not applied
anywhere: no `PREDICTION.md` exists.

## Reproduction

```sh
python -B research/network-circuit/phase1/noisechar.py OUT tt_mm 7101 noise /usr/bin/ngspice PDK 10
python -B research/network-circuit/phase1/nominal.py run OUT /usr/bin/ngspice PDK
python -B research/network-circuit/phase1/nominal.py collect NOMINAL_REHEARSAL.json OUT...
python -B research/network-circuit/phase1/slownoise.py DATA CONSTANTS.json MEASURES.json NOISE_RUNS.json
python -B research/network-circuit/phase1/noisegen.py WORK NOISE_GENERATOR.json /usr/bin/ngspice 200 0.0025 0.005 0.01 0.02 0.04
```

The noise of a run is seeded by the simulator's process number: none of
these runs repeats exactly.
