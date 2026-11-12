# Preregistered discrete refresh comparison — protocol v1

This document must be committed and pushed, and its draft PR opened, **before
implementing or executing the comparison**. The published commit identifies
this protocol. No pilot, parameter sweep or outcome-dependent revision is
allowed. After implementation and synthetic unit checks, execute the complete
comparison once. Preserve failures, stdout/stderr, raw traces and the report.
If execution fails, publish the failure and do not silently retry. Evaluation
of the recorded trace and compilation of its proof checks are not new trials.

## Frozen dependency and interpretation

Use kernel-R PR #111 at `ba978af1edaf51572aa0af9d1bfc83e309438d3d`.
Its independent read-only review found no blocking issue in the declared
scope; its deadlock counterexample and accounting docstring are already fixed.
Do not modify or merge #111 for this experiment.

The contract controller executes the existing `ClosedLoop.choose` and
`Renewal.review` definitions through Lean, not an unverified Python rewrite.
This is the fixed hard-ceiling fallback plus observation memory from #111,
with fresh bounded-error reserve observations at decision boundaries. It is
not the complete `OfferFactory` adaptive producer, a global optimizer, or a
new R bridge. Every contract action will be logged with its input lower bound.

The known hard ceiling below covers the hidden jump. A locally fitted rate
alone would not justify a future safety deadline. Rate observations update
reopening memory; they do not relax that hard ceiling in this trial.

## Plant and calibration (integer units, no floating-point dynamics)

| Parameter | Fixed value |
|---|---:|
| Scored periods | 1 through 1320 inclusive |
| Initial post-write reserve, at t=0 | 440 |
| Service floor S | 100; service means reserve >= 100 |
| Capacity C | 660 |
| Delivered write dose D | 220 |
| Write latency | Exactly 1 period; command at t delivers at t+1 |
| Nominal leakage per period | 10 |
| Leakage after the hidden jump | 20 |
| Jump time T* | 661: first increased loss is in period 661 |
| Known all-time leakage ceiling U | 22 |
| Maximum probe spacing | 40 periods |
| Reopening granularity g | 5 rate units |

Reserve is signed: no floor clipping conceals failure. Each period subtracts
its leakage; a commanded dose is added only at completion and clipped above
at C. At most one write can complete or be commanded per period. A new write
may be commanded at the completion of the preceding write.

D/10 = 22 periods is a **nominal calibration** to the R refresh observation
of roughly one dose per 22–23 periods (`research/circuit/VERDICTS.md`, P15).
This does not identify integer reserve with circuit voltage, certify every R
cell, or establish an energy model. The doubled leakage is a fixed challenge,
not an empirically measured R response.

T* is public in this protocol but hidden from all controller inputs. The plant
owns it. Controllers receive time, reports at paid probes, their own action
history and the shared constants S/C/D/U/latency/cap, never the true reserve,
true rate, jump time, future noise or future observations.

## Bounded-error sensor and costs

One paid probe returns both a signed reserve report and a nonnegative current
rate report. The noiseless values belong only to the plant/scorer.

- Reserve report: y_x(t) = x_pre(t) + e_x(t), with
  e_x(t) = ((7*t + 1) mod 5) - 2 and advertised error radius 2.
- Rate report: y_l(t) = lambda(t) + e_l(t), with
  e_l(t) = ((5*t + 2) mod 3) - 1 and advertised error radius 1.
- At t=0, use reserve 440 and nominal rate 10; the initial probe is paid.
- Controllers use lower = y_x - 2, not the true reserve. A negative lower
  bound is preserved as signed; the contract controller refuses if it cannot
  form a valid ready state. No zero clipping is allowed.
- Each probe costs **1** unit; each commanded write costs **10** units.
  Total cost = probes + 10*writes. There are no refunds, bundled free probes,
  free repair-completion probes or free initialization. These are declared
  model prices, not joules. No measurement latency is modeled.

Noise is deterministic, identical at a given time for all controllers and
not sampled from a distribution. This is one comparison, not a statistical
estimate. The two-channel sensor is an explicit abstraction, not inferred
from FIRE bits or claimed to be physically available in R.

## Exact within-period order and initialization

At t=0, take the paid initial probe, initialize memory and choose an action;
there is no initial loss or write completion. For each t=1..1320:

1. **Leakage:** x_pre = previous post-write reserve - lambda(t).
2. **Measurement:** if a probe is scheduled at t, pay and obtain both reports.
   No scheduled probe means no new report and no controller decision.
3. **Detection:** a sampled lower < S raises a conservative service alarm.
   Latch this alarm until a sampled or dose-propagated lower certifies S again.
   Score pre-write unsafe and undetected exposure after this detection step,
   before any dose arrives. A same-period detected violation is unsafe but
   not undetected. Never treat an absent observation as success.
4. **Writing:** deliver the dose commanded at t-1, if any. If a probe occurred,
   propagate its lower through that known delivery: min(C, lower + D).
   Without a delivery keep the measured lower. Now clear the alarm only if
   this certified lower >= S, and choose the next action from this lower.
   A new write command is charged now and delivers at t+1, never at t.

A write command schedules a paid probe at its completion one period later.
The last period is scored and any pending dose is delivered, but no controller
commands a new write or schedules further work at t=1320. Do not add a free
terminal observation for a controller not already scheduled to probe.

## Three fully specified controllers

All controllers receive the same sensor bounds, prices and actuator rules.
All baseline repairs use the same proactive threshold S+2*U = 144. Equality
at 144 does not trigger a write. Alarm detection still uses S=100 separately.

**Naive.** Probe initially. If the current measured pre-write lower < S,
set preferred spacing to 1; otherwise choose the largest allowed spacing,
40. After any pending delivery, command a write if the propagated lower is
below 144, and probe in 1 period for completion. Otherwise probe after the
preferred spacing. A successful observation immediately restores preference
40; no unseen period is checked. This deliberately optimistic policy is fully
fixed before outcomes; it is not optimized after seeing the comparison.

**Prudent.** Probe at every period, including initialization and completion.
After any pending delivery, command a write iff the propagated lower < 144.
Its observation spacing is always 1.

**Contract supervisor from #111.** Use the exact configuration
`Repair.Config = (service=100, bound=22, latency=1, dose=220,
capacity=660, maxWait=40)`. At each paid probe, form the interval
`Renewal.measurement(y_l, 1)` and call `Renewal.review(5, anchor, interval)`.
Initialize the anchor to the initial interval with zero reopenings. An anchor
change is one reopening; ordinary probes and safety recomputations are not.

After any pending delivery, call `ClosedLoop.choose(config, lower)` if the
signed lower is nonnegative. Its exact rule is: refuse invalid/unready input;
otherwise choose the largest positive c<=40 with 22*c + 122 <= lower;
if none exists, command a one-period write. Refusal records a blocked outcome
and schedules no more work; it is not silently repaired by another policy.
Each wait schedules a probe at its endpoint; each write schedules one at its
completion. Its future bound is U=22 regardless of the memory anchor.

The positive write latency and guard 122 reserve one full period of worst-case
loss. New reserve measurements can strengthen the propagated estimate only
through their error bound. This per-action interface will be checked; we do
not label the wrapper as a new proved end-to-end `OfferFactory` instance.

## Measurements and evidence to retain

Produce one raw per-period trace per controller (including t=0) and a common
report. Retain pre/post reserve, true leakage and sensor errors for scoring,
probe indicator/reports, alarm before and after detection, write command and
delivery, next due time, refusal, contract lower/action and anchor/reopening.
Truth is logged by the scorer and never passed into a controller decision.

Report separately:

- Pre-write unsafe periods (x_pre < S), and post-write unsafe periods.
- Undetected unsafe periods: pre-write unsafe while the alarm is not latched
  after that period's detection step. Their count times one base period is
  the discrete exposure measure; it is not a continuous-time integral.
- Longest consecutive undetected interval and first post-jump reopening delay.
- Number/cost of probes, write commands and delivered writes; total cost.
- Genuine reopenings (zero by definition for baselines without anchor memory),
  ordinary probes, refused decisions and final reserve, with no merged counts.
- Plant conservation, sensor bounds, action provenance and contract local
  safety inequalities, including pre-delivery reserve during writes.

## Numerical predictions fixed before execution

These are falsifiable predictions, not substituted assertions or filters.
Evaluate each independently and retain every failure in the report.

| ID | Prediction |
|---|---|
| P1 | Prudent: exactly 1321 probes, 88–92 writes, zero pre/post unsafe periods and zero undetected unsafe periods |
| P2 | Contract: zero refusals, zero pre/post unsafe periods and zero undetected unsafe periods |
| P3 | Contract: 150–600 probes and 88–92 writes; total cost <= 75% of prudent cost |
| P4 | Contract: exactly 1 reopening, at the first post-jump probe and no later than 40 periods after T*; 5*reopenings <= sampled true rate variation (=10) |
| P5 | Naive: at least 100 undetected unsafe periods and at least one undetected interval of length >= 10; 80–100 writes |
| P6 | Naive: total cost strictly less than contract cost, illustrating why cost alone is an inadequate objective |
| P7 | Every recorded contract decision agrees with frozen Lean definitions; every wait/write respects the ceiling, guard, positive latency and corresponding local lower-bound law |

The write-count ranges come from total nominal loss
660*10 + 660*20 = 19800, divided by dose 220, with initial/final reserve
corrections. Probe and cost ranges are analytical expectations, not pilot
measurements. Failure of a numerical prediction does not authorize tuning.

## Run discipline and report

First publish this file alone in the new draft PR stacked on #111. Then add
the implementation and synthetic tests. Record code hashes, Python and Lean
versions, protocol hash/commit, dependency commit and the exact command.
Run the comparison **once**; a single invocation contains the three fixed
controller trajectories. Use an exclusive run marker and do not overwrite
its output directory. Do not rerun to improve a result or after an unnoticed
failure. If interrupted, retain partial traces and report the interruption.

The report must list every P1–P7 verdict, raw results, exceptions, deviations
and limitations. Publish it as generated. Any future fix or replication
requires a separately identified follow-up protocol and run, outside v1.
Do not merge either PR; the repository owner handles fusion.
