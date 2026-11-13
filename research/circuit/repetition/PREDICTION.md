# Repetition campaign: step refinement and noisy repetitions. Rules, criteria and predictions

Pushed to the public repository before the first run of this campaign.
The time at which GitHub receives this push is the date of these rules.
This file is not edited afterwards. A deviation is declared in a new
file, pushed before the run or the computation that it concerns.

## What is known when this is written

Everything of `../certification/` and `../certification-unconditional/`,
and the branch `codex/physical-readout-enclosures` at commit
`9ebe00a16c29af58cad2664f2bf7ebdb3e2b2658`: its rule A1, the 57 ports
that pass it (`asymmetric-ports.csv`, SHA-256
`e296ca2b9c97bfdbfd816ae81cfdd2883251b8fffa41b82d81ba3deb8af9eb56`), and
its two planning files `STEP_STUDY_PROTOCOL.md` and
`REPETITION_PROTOCOL.md`. No run of this campaign exists.

Runs made before this push, none on the cell: decks of one resistor and
one noise source, to find how ngspice 42 seeds its noise (below); and a
request to GitHub to create a release, which was refused.

No file of an earlier campaign is modified.

## Purpose

Two hypotheses of the certificate of the 57 ports can be measured and
have not been.

1. **The integration margin `MG` = 0.0001.** How much does `eps3` change
   when the largest step of the solver is refined?
2. **`eps3` on noisy runs, and repeatability.** `eps3` was measured
   without noise and applied to noisy reads. And the count of each port
   comes from one noisy run. Each port is run again with fresh noise.

## Simulator and sources

As in `../certification/manifest.json`: ngspice 42 (Ubuntu package
42+ds-3build1, same SHA-256), SKY130 models at the same commit, the same
netlist, noise levels and solver tolerances, 27 °C. `manifest.json` holds
these hashes, the hashes of the code reused from the two earlier
campaigns, and the complete ordered run list; `rep_run.py` checks them at
each run. Every run is made once. A run that fails stays failed.

`rep_run.py` builds the deck with the function `deck` of
`../certification/cert_run.py` and replaces three things in its text: the
largest step and the stop time of the transient analysis, and, if adopted
below, the output format and the linear solver. The rows of a run are
made by `rows_of` of `cert_run.py` and written in its format.

**Current of a mirror.** Two more signals are saved than in
`../certification-unconditional/`: the currents of the noise sources of
the two mirrors (`v(x1.nzi)`, `v(x2.nzi)`; the source is a
transconductance of 1 S in parallel with the output transistor). The
current of a mirror is the drain current of `xmout` plus the current of
its noise source. Without noise the second is zero. The charges `W`
(whole pulse) and `WE` (up to 0.75 unit) are computed on this sum by the
two functions of `../certification-unconditional/`.

**Noise.** ngspice 42 seeds the generator of its `trnoise` sources from
its process id when it starts; the seed of a deck sets the mismatch only.
Seen on decks of one resistor: two runs give two noises; with the process
id fixed they give the same noise byte for byte, whatever the mismatch
seed. `fakepid.c` is a preloaded library that makes `getpid()` return a
chosen number. The binary of the simulator is not modified. Each noisy
run has its own **noise number** in `manifest.json`; all are different.
So the noise of a run is fresh, different from every other run on either
machine, and can be replayed. The noise sources themselves are those of
the earlier campaigns.

## Stage 1: solver and output options

Four runs of the nominal training without noise, at 200 ns, started
together on one machine: the base; the KLU solver (`.option klu`); binary
output (`write` of a binary raw file in place of `wrdata` with 16
digits); both.

- The rows of the base run must be those of
  `../certification/results/preflight/nom_train.csv`, byte for byte.
  Otherwise no option is adopted and the cause is looked for.
- **Rule.** An option is adopted only if its rows and its charges are
  those of the base run byte for byte **and** its total time (simulator
  plus reading) is lower. Both options together are adopted only if the
  run with both also gives the same bytes and is the fastest.

`rep_analyze.py accel` applies the rule and writes `ACCEL.md`.

## Stage 2: step refinement

The six cases of `STEP_STUDY_PROTOCOL.md`, chosen by identifier: the
nominal cell and the calibration cells 5001 and 5002, each as a training
and as a leak scan, without noise. Each at a largest step of **400, 200,
100 and 50 ns**: 24 runs. Deviation from that protocol, decided here: a
400 ns level is added and the repeated 200 ns baseline is dropped; in its
place, each 200 ns run is compared with the same run of the earlier
campaigns, whose rows it must reproduce byte for byte.

For each case, each port and each pair of steps (400/200, 200/100,
100/50, 200/50): the FIRE of every read, the count, the latch and
steering counts of every read, the largest change of a gain `Z`, the
largest change of a latch date, and the change of `eps3`. `eps3` is the
statistic of amendment 1 of `../certification-unconditional/` (silent
reads over the whole pulse, every read with a gain up to 0.75 unit, plus
`MG`), computed twice: with its two constants `D` and `DE` refitted at
each step, and with both frozen at their 200 ns values, so that a refit
cannot hide a change.

**Rule for the step of the noisy runs.** 400 ns is adopted only if every
run is evaluable and, in every comparison of 400 ns with 200 ns:

- the FIRE of every read, the counts, and the latch and steering counts
  are the same;
- every gain moves by at most `mz` = 0.0002, the resolution margin of the
  certification campaign;
- `eps3` moves by at most `MG` = 0.0001, refitted and frozen;
- every latch date moves by at most 0.001 unit (20 ns).

Otherwise 200 ns is kept. The rule is tested without noise; a noise
source has a breakpoint every 400 ns in either case.

`rep_analyze.py step` applies the rule and writes `STEP.md`. A pass says
that the sensitivity of `eps3` to the step, over these six cases and
these settings, is within `MG`. It does not bound the error against the
exact solution.

## Stage 3: noisy repetitions

**Ports.** The 57 ports that pass rule A1, on 52 cells. They include the
37 ports of status 3 of `../certification-unconditional/`. Deviation
from `REPETITION_PROTOCOL.md`, which froze the 37: decided by the owner
of the campaign. The report gives the two groups separately.

**Repetitions.** 20 per cell, numbered 0 to 19: 1,040 runs, 1,140 trials
(one trial is one port in one repetition). Each repetition is a complete
and independent run from the initial state; nothing is restarted from a
saved state.

**Truncated trains.** A repetition of a cell is the training of the test
runs, stopped at the end of the period of read `m` of its port of rule
A1 (the later of the two if both ports pass). For a port 2 the ten
pulses of port 1 are played first, as in the complete train. The verdict
"count = m" is decided at read `m`: reads 0 to `m - 1` silent and read
`m` with a FIRE. Only the value of a count larger than `m` is lost.

**Two machines.** Even repetitions on machine A, odd repetitions on
machine B, with the same hashes of the simulator, the models and the
sources checked on both. Slices are ordered by repetition number, so
that a stop leaves a balanced sample. There is no early stop on good
results.

**Traces.** For each run, a reduced trace: for each read 0 to `m` of a
port of rule A1, the solver points from 1 µs before the pulse to 1.1
unit after its start, with the main charge, the latch, the noise of the
threshold, the two steering signals, and the drain and noise currents of
the two mirrors. One archive per slice goes to the private repository;
it is read back from GitHub and its SHA-256 compared before the local
traces are removed. The public repository holds the SHA-256 of each
trace, the name and SHA-256 of each archive, and every extracted value.
The latch and steering counts of a whole period are in the rows only.

The step, the options and these five points are fixed by an amendment
pushed before the first noisy run. `rep_run.py` refuses a noisy run
without it.

**Preflight of the repetitions**, on the nominal cell, on each machine,
after the amendment: a training cut after five pulses must give the
first five rows of the complete training of stage 2, byte for byte; two
noisy runs with the same noise number must give the same bytes; a third
with another number must give another noise.

### Frozen inputs

`frozen.json`, written by `rep_freeze.py` from public files only: for
each port its need `m`, `a_s`, start gain `G0s`, `level0`, `h3`, its
`eps3` without noise, and its two constants `D0` and `DE0` (the means
over the silent reads of its training without noise); and `kappa`, `d0`,
`eps_kappa`, `mz`, `mq`, `MG` of the earlier campaigns.

### Per trial, from the reads 0 to `m` of the port

- **Count agreement.** Reads 0 to `m - 1` are silent and read `m` has a
  FIRE.
- **Guards.** Every rest state in `[0.1, 0.1001]`; the latch rises at
  most once per period; the steering switch of the port turns on exactly
  once in a silent period and never in a period with a FIRE, that of the
  other port never; no FIRE earlier than 0.76.
- **`eps3` noisy.** The largest of `|G - GI - D0|` over the silent reads
  and of `|Y - GE - DE0|` over the reads with a gain, plus `MG`. The two
  constants are frozen; nothing is fitted on the repetition. The same
  statistic with the constants refitted on the repetition is reported
  beside it.
- **Residual.** Guards hold and `eps3` noisy is at most the `eps3` of
  the port without noise.
- **Certified repetition.** Rule A1 with every bound measured on the
  repetition itself. With `E` = `eps3` noisy, `dev(k) = Z(k) - Z(0) - k*d0`
  and `r(k) = mz`, plus `eps_kappa` if read `k` has a FIRE:

```text
a        = a_s + |Z(0) - G0s| + mz (+ eps_kappa if read 0 has a FIRE) + E
B_silent = max(0, dev(k) + r(k) + r(0) for k < m) + 2*E
B_fire   = max(0, -dev(m) + r(m) + r(0)) + 2*E
ell      = h3 + largest noise of the threshold in the reads 0..m + mq
silence room = d0/2 - a - B_silent - (20/17)*ell - 1/8000     must be > 0
FIRE room    = d0/2 - a - B_fire   - (20/17)*ell              must be >= 0
level0 - ell >= 19/20
```

  A repetition is certified when its guards hold and both rooms and the
  floor pass. The count is an outcome, not a condition.

A failed run counts as a wrong count, an unmet residual and a
repetition that is not certified, for each of its ports.

### Statistics

For each port: the number of wrong counts in its repetitions and the
one-sided 95% Clopper-Pearson upper bound on its probability of a wrong
count (13.9% for none in 20), and the same bound at 0.05/57 for the 57
ports together. For the trials pooled: the same bound on 1,140 trials
(0.26% for none). **The pooled bound assumes interchangeable ports and
independent trials.** It bounds the mean probability of a wrong count
over these 57 ports, under the noise model of the simulator. The two
ports of the five cells that have both are run together and share their
noise; the report says so. Nothing here is a claim about other cells.

`rep_analyze.py report` is run once, after the last slice is pushed, and
its report is pushed as written. If the campaign stops early, it covers
the repetitions completely run and says which.

## What is a failure

- **F1.** A repetition certified on its own measures whose count is not
  `m`.
- **F2.** A port whose count is wrong in more than 10% of its
  repetitions (3 or more of 20).
- **F3.** A change of `eps3` above 0.0001 between two of the steps 200,
  100 and 50 ns.

A failure is reported as such. Nothing is adjusted to remove it. No
rule, constant or margin is changed after a result is seen. If a rule
proves wrong, a new rule is written and pushed before it is used, and
both results are shown.

## Predictions

| | Prediction |
|---|---|
| R1 | Between 200, 100 and 50 ns, `eps3` moves by at most 0.0001 in every comparison (no failure F3) |
| R2 | No run fails |
| R3 | The count is the predicted `m` in at least 97% of the 1,140 trials |
| R4 | No port has its count wrong in more than 10% of its repetitions (no failure F2) |
| R5 | The median `eps3` noisy, constants frozen, is between 0.0005 and 0.003 |
| R6 | No repetition certified on its own measures has a wrong count (no failure F1) |
| R7 | The noise of every run is different from that of every other run |

## What this campaign does not do

- It does not change a status of an earlier campaign, nor the 37 or the
  57 ports. `mc_2064`, port 1, keeps its historical status.
- It does not prove a bound on the error of the solver.
- It does not measure the last quarter of a read with a FIRE: the gain
  of such a read is checked by the current up to 0.75 unit only.
- It is a simulation. No chip was built.
