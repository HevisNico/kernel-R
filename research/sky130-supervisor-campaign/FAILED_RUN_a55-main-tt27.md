# The cause of the failed run `a55-main-tt27`

Added after the campaign. It changes no result: the run stays a missing run,
it was not run again, and the report of the campaign is as generated.

## What happened

Run `a55-main-tt27` of machine a (scenario `main-tt27`: supervised, noise,
jump inside the domain, `setseed 10055`) started at 11:03:34 UTC and ended
16 s later with status `failed-never-rerun`. Its simulator session ends with:

```
doAnalyses: TRAN:  Timestep too small; time = 3.1e-06, timestep = 2.5e-19: trouble with node "vpre#branch"
tran simulation(s) aborted
```

What it left is in
[`evidence/machine-a/a55-main-tt27`](evidence/machine-a/a55-main-tt27): the
deck, the session log, and the traceback of the runner. It wrote no waveform
and no fingerprint of its noise.

## The cause

**The simulator stopped by itself, 3.1 us into the run, before anything of
the experiment had happened.** It is not a behaviour of the cell, of the
supervisor or of the launcher.

- 3.1 us is the first edge of the stimulus: the reset of the sequencing
  latches is released 1 us before the first pulse position, at 4.1 us. That
  position is in the first of two idle slots: no port is selected, no pulse
  is admitted, the preparation has not begun. The first service would have
  come about 2 ms later.
- "Timestep too small" is the solver giving up: at that date its iteration
  did not converge, it halved the step until the step was below its floor,
  and it aborted. The quantity that did not settle is the current of the
  ideal 1.3 V source that precharges the sensor capacitors (`vpre`). The
  deck asks for that current to within 1e-13 A (`abstol`, set in
  `cell.spice` for the accuracy of the doses).
- It needs the noise. The same deck without noise never did this, in any run
  of the qualification or of the campaign. The noise sources draw a new
  value every 0.4 us; with one particular draw, the iteration at that edge
  did not settle.

This is the same event as the five aborted runs of the supervisor
qualification
([`../sky130-supervisor-closure/README.md`](../sky130-supervisor-closure/README.md)):
same date, same final step, the current of an ideal source. There the
source was the 0 V source that measured the write current; with it the abort
was systematic at one corner, it was removed, and three ways of avoiding the
abort were found (no such source, 1 ohm in series, `abstol` of 1e-12 A).
Without that source the event is rare, and `vpre` is another ideal source
whose current is near zero at that date.

## What could not be established

**The abort could not be reproduced.** The noise of a run depends on the
number of its simulator process, which nobody chose and nobody recorded, and
the run stopped before writing its fingerprint. An exploratory diagnosis
([`diagnose_a55.py`](diagnose_a55.py),
[`FAILED_RUN_a55-main-tt27.json`](FAILED_RUN_a55-main-tt27.json)) started the
same deck with the same `setseed` 517 times, with process numbers imposed
between 1 and 708, each time up to 30 us: **no abort in 517 sessions.** So
the three remedies above are not verified for this event, and the statement
"the convergence test on the current of `vpre`" rests on the simulator's
message and on the earlier case, not on a replay.

## How often

Noisy runs that started on a deck without the 0 V source:

| Where | Starts | Aborts at 3.1 us |
|---|---|---|
| The campaign | 104 | 1 (this run) |
| Qualification with junction areas (70 that ended, 3 cut later by a full disk) | 73 | 0 |
| First qualification, runs without the 0 V source | 64 | 0 |
| The diagnosis above | 517 | 0 |
| Together | 758 | 1 |

About one start in several hundred. The preregistration counts such a run as
missing: neither a success nor a failure, never replaced. The main claim was
therefore evaluated on 93 runs instead of 94, and `tt27` has 11 runs instead
of 12.

## For a later campaign

Not done here, and not to be done silently: a looser `abstol`, or a
resistance of 1 ohm in series with the ideal supplies, would change the
deck; either belongs in a preregistration, with a check that the doses and
latencies do not move.
