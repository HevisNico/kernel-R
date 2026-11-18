# Campaign 6: amendment 1 to PREDICTION.md

**Draft for review.** With both coordinators' reviews and the owner's go, this file is pushed alone on
`research/learned-dnf-circuit-campaign-6` as `research/learned-dnf-circuit-campaign-6/PREDICTION_AMENDMENT_1.md`. That
happens after `PREDICTION.md` (`df1a3cb`, SHA-256 `8e7392c5…2240`) and **before the implementation is frozen**. No seed
from 7801 has been simulated, and no stage has been launched.

## What it changes

Section 6 of `PREDICTION.md` keeps the measure runs of M1, M2 and M3 on their instance's machine. **For M2 and M3 (and
the rehearsal's RM2 and RM3), this amendment replaces that rule with section 4's two-shard alternation.**

- The runs of the stage are those whose inputs are complete, as recorded in the stage's frozen inputs file.
- They are listed in a fixed order: by instance, in seed order (machine `a`'s nominal cell before machine `b`'s in
  the rehearsal), then by run kind in this order:
  - M2: the pair scan of `a`, the pair scan of `b`, line 1 of `c`, line 2 of `c`, the both-lines check;
  - M3: the one-sided set of `a`, then of `b`.
- They then alternate `a`, `b`, `a`, … starting with `a`.

**M1 is unchanged.** Its runs stay on their instance's machine (7801 to 7803 on `a`, 7804 and 7805 on `b`; in the
rehearsal, one nominal instance on each). So M1 has runs on both machines by construction.

## Why

- **The kit refuses a one-sided stage.** It refuses a stage that has no run on one of the two machines (`launch.py`,
  line 210). Under the old rule, if only one machine's instances had complete inputs for M2 or M3, that stage would be
  refused and its runs missing.
- **The machine changes no measure.** A measure run's deck depends only on its instance's seed and on its inputs, the
  doses and bounds in the frozen inputs file. It does not depend on the machine where it runs; only its wall time does.
  Campaign 5's rehearsal stage RM ran the same calibration decks on both machines and found them identical.
- **A measure stage never holds a single run.** M2 has 5 runs per instance and M3 has 2. So with at least one instance,
  the alternation always gives both machines a run. A stage with no run (no instance with complete inputs) is not
  launched, and its runs are recorded as not started.

## What does not change

- No rule, claim, instance, limit or cost changes.
- The expected compute and the kit's bounds of section 6 are unchanged, because the alternation moves runs between the
  two machines without changing either machine's largest run kind.

  | Case | Expected compute |
  |---|---|
  | Measures (M1, M2, M3) | 7 084.9 s |
  | Measure stages' bounds | 6 902.5, 6 987.5 and 2 025.0 s |
  | With 1 to 5 eligible instances | 11 084.9; 16 953.9; 18 183.4; 19 412.9; 20 642.4 s |
  | Measure rehearsal | 4 200.6 s |

  The split per machine changes: M2 holds 13 runs on `a` and 12 on `b` (before: 15 and 10), and M3 holds 5 and 5
  (before: 6 and 4). The frozen code's CI reproduces these figures to 0.01 s.
- The prediction reads every run of an instance wherever it ran. Its runs are gathered under the instance's own
  machine folder before `predict6` reads them, as `predicted6.layout` does.
