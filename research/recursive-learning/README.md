# Adaptive teaching with capped learning memories

Can feedback from a learner change both the next lesson and which edit the
teacher tries after that? In this discrete model, Lean checks two consecutive
improvements. The teacher needs 8, then 7, then 6 pulses to deliver the same
retained skill. Freezing only the edit selector leaves the first improvement
intact and prevents the second.

## The experiment

An abstract learner has separate preparation and practice needs. Practice
pulses contribute only after preparation finishes. A lesson sends a block
of each pulse type, and the learner retains the skill when both needs reach
zero. Each trial starts with fresh learners. Only the teacher carries its
memories from one trial to the next.

The teacher stores two capped credits and a bit selecting which credit it
may increase. A candidate spends one credit to remove one pulse from the
corresponding block. The teacher commits the candidate when it passes the
validation learners and reduces the pulse count. After acceptance, it probes
one further reduction in preparation. If that probe fails, feedback can set
the selector to practice for the next trial.

| Teacher state | Preparation pulses | Practice pulses | Next proposed edit |
|---|---:|---:|---|
| Initial | 4 | 4 | Reduce preparation |
| After first commit | 3 | 4 | Reduce practice |
| After second commit | 3 | 3 | Reduce practice again, which fails validation |
| First commit with frozen selector | 3 | 4 | Reduce preparation again, which fails validation |

The two validation learners have needs `(3, 2)` and `(2, 3)`. Two separate
learners with needs `(3, 3)` and `(2, 2)` appear only in the evaluation of the
example. More generally, Lean proves that the final lesson succeeds exactly
when both needs are at most three, and six pulses is the minimum lesson cost
for the learner with needs `(3, 3)`.

## Checked statements

- [`Example.two_successive_improvements`](RecursiveLearning/Example.lean)
  checks both committed updates, all three costs and retention on the separate
  learners. `frozen_selector_misses_second_improvement` checks the intervention.
- [`Experiment.step_contract`](RecursiveLearning/Model.lean) proves that each
  commit preserves the memory bounds, consumes exactly one teaching credit,
  retains validation success and strictly lowers lesson cost.
- [`Run.count_le_remaining`](RecursiveLearning/Model.lean) bounds the number
  of strict improvements in any run by the sum of the two credits' remaining
  headroom. Validation can stop a run before either cap is exhausted.

## Scope and connection to R

The pulse count measures a deployed lesson. Proposals and feedback probes
have their own costs. The learner, the acceptance test and the selector
are discrete definitions. A credit is a unit dose in this model. The
[native R dose theorem](../../docs/EXACT_DOSE_COUNTING.md) motivates that
abstraction through exact increments from fully exposed sensor phases.

The [native memory experiment](native/README.md) realizes the teacher's two
commits with actual R flows and arrivals for a supplied pulse script.
For the final preparation slot, a single native R execution now carries the
lesson through readout, routed feedback when the learner fires, the selector
update, and receipt of the next selected pulse. The dispatch in that round
changes the low selector gain. A [prepared read](native/SelectorRead.lean)
preserves both values and leaves a timing margin for routing the output.
A [saturated work pulse](native/SelectorPrecharge.lean) supplies the
required charge after a suitably timed reopening. A [local teacher
execution](native/TeacherReopen.lean) now schedules the work pulse from
its own FIRE and reaches that reopening in both fabrication boxes.
With recovery at its cap, a [fixed recovery clock](native/TeacherStableClock.lean)
allows bounded timing variation on that self-delivery and preserves the
read. From an admitted work pulse, a [single physical continuation](native/CappedWorkRun.lean)
builds the precharge and admits the selector pulse. In the
[prepared controller and receiver](native/CappedDispatch.lean), the
controller's own ignition FIRE schedules both work and read, and the
read FIRE routes the next pulse to the selected learner port without
changing the selector. Both stored values use the same absolute
decoder. The controller's work port and the two credit memories must
belong to separate cells in this design. Connecting the credit memory,
preparing the controller within the network and iterating the native
teaching loop remain open.

The discrete results above establish the two improvements and a bound for
the capped architecture.

## Verify

From the repository root, with the pinned Lean toolchain available:

```sh
cd research/recursive-learning
lake build
```

This package uses Lean 4.35.0 and has no external dependencies. The default
build includes [the audit](Audit.lean), which checks project declarations
against Lean's standard logical axioms.
