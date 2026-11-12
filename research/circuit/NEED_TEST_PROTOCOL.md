# Fixed rule for the circuit need-tolerance test

Recorded on 2026-11-12, before any new simulation for this test. The Git
commit containing this file is the versioned record; its timestamp does not
retroactively preregister results already inspected.

## What has already been seen

The existing campaign contains 100 mismatch/noise runs, `mc_2001` through
`mc_2100`, with two ports each. Its published ceiling-of-gap comparison
agrees on 190 of 200 ports. These data and their ten disagreements are known.
An exploratory calculation has also already been made: using the existing
peak-based dose estimates and assuming zero threshold error, 9 of the 10
disagreements fail the room inequality, but `mc_2064`, port 1, passes it.
The same calculation passes 93 agreeing ports, fails 96 agreeing ports,
and lacks a dose-dispersion estimate for one agreeing port.

These observations are retrospective. They will not be presented as a
prediction confirmed on unseen data, used to choose a cutoff, or removed
from a subsequent report. No new SPICE campaign has been run for this test.

## Mathematical rule

For a declared target need `m` (a nonnegative integer), nominal dose `d0`,
nominal FIRE level `level0`, and start log-gain `z0`, define

```text
firingLogGain(level0) = log((level0 - 1/10) / response(1))
needCentre(level0,d0,m) = firingLogGain(level0) - (m - 1/2)*d0
a >= abs(z0 - needCentre(level0,d0,m))
b = k*eta + sigma + e
room = d0/2 - a - m*b - (20/17)*ell - 1/8000
```

All error budgets are nonnegative deterministic bounds, not standard
deviations. Here `sigma` bounds sensor-dose error; despite its name it is
**not** a statistical sigma. The declared charge-to-log-gain scale has
`k >= 0`. At every relevant write:

```text
abs(k*(Qs(start)-Qs(stop)) - d0) <= sigma
abs(integral(Iwrite) - integral(Isensor)) <= eta
abs(z(next)-z(now) - k*(Qm(start)-Qm(stop))) <= e
z(next)-z(now) >= 0
abs(level-level0) <= ell
level >= 19/20; level0 >= 19/20
```

Charge paths satisfy the integral balances in `ChargeWindow`. The state
linkage includes every intervening change, including inter-window drift.
The scalar read obeys the declared model, with rest charge in
`[1/10, 1/10 + 1/10000]`. A physical FIRE must be linked to that read;
an observed latch transition alone does not establish the linkage.

**Prediction:** if all these hypotheses are established and `room > 0`,
the scalar need is exactly `m`: reads after fewer than `m` writes are
silent and reads after `m` or more writes fire. To predict a training
sequence with exactly `m` silent pulses before its first FIRE additionally
requires that each silent pulse writes once, firing pulses are protected,
and the read/write order implements this scalar contract. This execution
linkage is a separate obligation, not a conclusion of `NeedAlong`.

The inequality is strict. Equality does not pass. Failure of `room` makes
**no prediction of an incorrect count**: this is a sufficient condition,
not a necessary boundary. No claim that precisely the ten known exceptions
must fail is part of the test.

## Status and reporting rules

Each planned port must appear in the output, with one of these statuses:

| Status | Rule | Interpretation |
|---|---|---|
| Not evaluable | A required quantity, bound, or model/execution linkage is missing | Do not substitute zero or remove the port |
| Outside sufficient region | All required information is available, but `room <= 0` | No count guarantee |
| Qualified, agrees | All hypotheses hold, `room > 0`, observed count is `m` | Agreement with the fixed prediction |
| Qualified, disagrees | All hypotheses hold, `room > 0`, observed count differs | Report an empirical failure of the asserted model-to-circuit application and investigate it |

Measured ranges over a finite trace are sample diagnostics, not uniform
bounds on future writes. Noise standard deviations cannot replace `eta`,
`sigma`, `e`, or `ell`. A separate probabilistic claim would require its
own fixed coverage and multiple-comparison rule. No such claim is made here.

For the existing CSVs, any peak-based surrogate must be named `proxy`,
reported separately from the qualification status, and accompanied by its
normalization and missing assumptions. In particular, a minimum voltage
over a firing period is not an independent measurement of the threshold at
contact; clipping, comparator delay and overshoot matter. Consecutive silent
peaks omit the write that first makes a port fire. Fewer than two silent
peaks supply no sample dose-dispersion estimate; use missing, not zero.

## Requirements before launching a prospective campaign

Before its first simulation, commit a campaign manifest that freezes:

1. A new, disjoint calibration cohort and test cohort; the complete ordered
   run list, size, netlist/model hashes, solver settings and extraction code.
   Existing `mc_2001`--`mc_2100` results are excluded from prospective evidence.
2. The numerical `d0`, `level0`, scale and coordinate calibration, the target
   `m` for each port (or its deterministic assignment from independent
   calibration), every error-budget rule, and numerical uncertainty bounds.
   These must not be fitted to the test counts, final trained gains or
   disagreement labels. Missing calibration blocks qualification.
3. Measurements of sensor charge at window entry/exit, transferred current,
   actual gain before/after each write, inter-window drift, rest state and
   threshold/contact behavior, including the final silent write. The present
   summary CSV alone does not supply these measurements.
4. The read/write and comparator model checks needed to apply the scalar
   theorem. If these are only approximate, include their error in a proved
   bound rather than silently treating the approximation as exact.
5. A fixed stopping rule: run every listed case, include every planned port,
   retain failures and missing results, and do not extend or repeat the
   cohort based on agreement. Retain original noisy traces: the existing
   simulator's noise is not reproducible from its mismatch seed alone.

The campaign manifest and numerical calibration are not yet supplied by
this document. This file freezes the test rule, not a ready-to-run or
completed preregistered experiment. Until the manifest is committed, no new
campaign should be launched under that label. Later amendments must identify
what results were already seen and preserve the original rule and report.
