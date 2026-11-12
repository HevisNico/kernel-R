# Reusable discrete teaching controller

This first milestone closes a **discrete** teaching loop over the unchanged
[two-block learner](../recursive-learning/RecursiveLearning/Model.lean).
After a rejected edit the controller keeps its accepted lesson, records the
rejection and continues on the other coordinate. The same transition is reused
at every round. The native R realization of this loop is **not proved**.

## Algorithm and scope

The environment is one fixed learner with natural-number preparation and
practice requirements. Each trial trains a fresh copy of that learner. The
controller keeps its current two-block lesson, two blocked-coordinate bits,
and resource counters. It starts from a lesson that already passes.

1. Try removing one preparation pulse while that coordinate is unblocked.
2. Train the validation learner with the whole candidate lesson.
3. Commit a successful reduction. On rejection retain the old lesson and
   block that coordinate. A zero-length block is blocked without a trial.
4. Continue on practice after preparation is blocked; stop when both are blocked.

The order is fixed; there is no scheduled list of successful outcomes. Only
the evaluator observes the learner requirements. The two blocked bits are
monotone, so the algorithm does not silently assume a reversible gain write.
That fact alone does not implement the bits as R cells.

This is finite coordinate minimization for the upstream separable learner,
not a new general optimization algorithm or a generalization theorem for
arbitrary learning tasks. The evaluator and the objective never change.

## Checked statements

All statements are in [Proofs.lean](ReusableController/Proofs.lean).

| Statement | Guarantee |
|---|---|
| `attempt_contract`, `round_ready` | A round preserves the valid lesson and the soundness of blocked-coordinate memory |
| `rejected_keeps_lesson` | Rejection changes neither the retained lesson nor the accepted-edit counter |
| `attempt_validation_charge` | Every actual trial pays its entire candidate lesson, whether accepted or rejected |
| `attempt_flags_monotone` | No blocked bit needs to be erased |
| `round_progress`, `halts_within` | Every active round strictly lowers a natural potential; termination does not assume that another improvement exists |
| `run_accounting` | Each accepted edit removes exactly one pulse from the retained lesson |
| `run_bounds` | After `n` rounds, at most `n` further attempts and `n * initialLesson.cost` further validation pulses have been charged |
| `terminal_optimal` | For any requirements and any passing initial lesson, at most `initialLesson.cost + 2` rounds reach the exact requirements and the minimum two-block lesson cost |
| `ready_generalizes` | Every retained lesson succeeds on every learner with coordinatewise smaller requirements |
| `deployment_break_even` | Search plus repeated deployment is no more costly than the baseline once the declared search work is covered by the deployment savings |

`Ready` is a logical invariant. It is not the R cell's READY phase. No
`Snapshot`, `Execution` or native network is constructed by this package.
The underlying learner and its retention theorem are imported unchanged
through a local Lake dependency, not copied or replaced.

## Rejection followed by further improvement

For requirements `(3, 3)` and initial lesson `(4, 5)`, Lean checks this trace:

| Round | Attempt | Result | Retained lesson | Cost | Cumulative trial pulses |
|---:|---|---|---|---:|---:|
| 0 | — | Initial | `(4, 5)` | 9 | 0 |
| 1 | `(3, 5)` | Accept | `(3, 5)` | 8 | 8 |
| 2 | `(2, 5)` | Reject; block preparation | `(3, 5)` | 8 | 15 |
| 3 | `(3, 4)` | Accept | `(3, 4)` | 7 | 22 |
| 4 | `(3, 3)` | Accept | `(3, 3)` | 6 | 28 |
| 5 | `(3, 2)` | Reject; halt | `(3, 3)` | 6 | 33 |

[Examples.lean](ReusableController/Examples.lean) also checks zero requirements,
zero-cost idling after halt, the held-out box, and amortization. With a declared
overhead of one resource unit per attempt, search costs `33 + 5 = 38` units.
Thirteen deployments amortize search (`38 + 13*6 <= 13*9`); twelve do not.

`work overhead = trialPulses + overhead * attempts` is an accounting model.
The overhead must cover proposals, reports, writes and reset in compatible
units. No hardware energy, duration or reset-cost bound is derived here.
Fresh validation learners, an initially passing lesson and exact acceptance
reports remain assumptions of this discrete model. Deployment assumes fresh
learners in the specified requirement box; reuse of a physical learner is not proved.

## Native handoff

[NATIVE_HANDOFF.md](NATIVE_HANDOFF.md) identifies the exact existing native
interfaces that fail to close and the obligations for the next milestone.
In particular, an existing selector read ends in FAST or SLOW, and the current
cycle router ignores later ignition dates. Reusing a controller requires a
real continuation and a router fixed for the whole execution; changing the
router between proof fragments is not a solution.

The [native return checkpoint](NATIVE_RETURN.md) now constructs the read's
FAST/SLOW continuation to rest for positive recovery. It preserves the gains,
recovery and sensor rest bands and inherits the native physical invariant.
**M2 remains open:** the returned charge is `1/10`, below the next read's
required `13/20`. Re-preparation by real inputs and their costs are not proved.
The subsequent milestones have not started.

## Reproduce

From this directory, with Lean **4.35.0** and Python 3 available:

```sh
lake build
lake env lean Trace.lean
python3 verify.py
```

There is no Mathlib dependency. The default build includes an axiom audit of
all declarations from the imported upstream model and this package's modules,
including private/generated declarations. Only `propext`, `Classical.choice`
and `Quot.sound` are allowed. Audit counts measure coverage, not contributions.

`verify.py` rebuilds the positive package and rejects six isolated mutations:
accepting a failing trial, losing progress after rejection, omitting validation
cost, adding the wrong credit, adding an unused project axiom, and admitting a
proof. Parser/import errors do not count as successful negative controls.
The temporary copies leave the original sources untouched.

The native Lean development and transistor simulations are not rebuilt by
these commands. This milestone neither changes their laws nor supplies a
circuit certificate.
