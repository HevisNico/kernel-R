# Native R memory for the adaptive teaching loop

The [discrete example](../README.md) has two teaching credits and a selector.
Here each is encoded in the log-gain of a separate port of one actual R cell.
One full exposed ERROR section adds `3/5` to its port, which represents one
credit or sets the selector. The encoding is relative to that port's starting
log-gain.

## What Lean checks

[`encodes_iff_counts`](NativeLearning.lean) applies to any native execution
with complete exposed ERROR covers on the three teacher ports. An endpoint
represents the claimed memory exactly when each port's actual phase count
equals the required credit increment. Missing, extra or misrouted doses
therefore cannot represent that commit. [`selector_iff`](NativeLearning.lean)
reads the selector by comparing the current log-gain on port 2 with its
starting value plus `3/10`, half the dose.

[`prepared_run_exists`](NativeLearning.lean) constructs the teacher's native
execution under either declared fabrication box. It starts from a prepared
READY state with unit gains, recovery `2/25`, full reserve and no active raw
current. The queue contains three separated canonical pulses on ports 0, 2
and 1, due at offsets 1, 9 and 17.

| Snapshot | Preparation credit | Practice credit | Selector |
|---|---:|---:|---|
| Initial | 0 | 0 | Preparation |
| Complete at offset 16.5 | 1 | 0 | Practice |
| Complete at offset 24.5 | 1 | 1 | Practice |

The actual trace carries the middle state into the second segment, consumes
the three deliveries and produces no teacher firing. The pulses arrive and
each sensor completes its own cycle under the existing [R dynamics](../../../model/CELL.md).
[`prepared_crossing_run_exists`](NativeLearning.lean) gives a complete
upward-crossing execution of the same history using its transverse contacts.

The queue in this construction is supplied in advance. The `8 → 7 → 6` pulse
count is the deployed lesson cost in the discrete experiment.

## One feedback pulse from an actual learner firing

The [two-cell experiment](Feedback.lean) starts with a canonical probe already
admitted on learner 0. The teacher's raw ports and the global pending queue
are empty. The fixed router sends any learner FIRE at time `F` to the teacher's
selector port at `F + δ(F)`, with `0.3 ≤ δ(F) ≤ 0.4`.

- With learner input gain in `[9/5, 11/5]`, `prepared_routed_feedback_of_strong_gain`
  constructs a complete first-contact execution with one learner FIRE, one
  corresponding feedback delivery and an exact increase of `3/5` on the
  selector port. `RoutedFeedback.every_complete` proves the same firing date,
  delivery and teacher gains for every first-contact execution complete through
  that horizon, from the same state with the same parameters and router.
- With learner input gain in `(0, 7/6]`, the probe is silent and the selector
  gain stays fixed. `prepared_weak_probe_crossing_exists` also constructs a
  complete upward-crossing execution with this outcome.

Both bands apply in either fabrication box. They leave a gap between
`7/6` and `9/5` where the exact firing threshold is open.

### Routed feedback under upward crossings

`causal_routed_crossing_exists` proves the strong-gain case in the model's
upward-crossing semantics. This construction numbers the teacher 0 and the
learner 1 and uses the same local starting states. The network starts with an
empty delivery queue. The learner's actual FIRE issues the token, and the
teacher consumes it at the routed date.

`CausalRoutedFeedback.every_crossing_complete` gives the same single FIRE,
single delivery, empty final queue and exact selector dose for every
upward-crossing execution complete through the constructed horizon. The other
two teacher gains stay fixed. The proof retains each candidate execution's
own paths and jumps when relating it to the first-contact semantics.

The discrete commit tests whether the accepted lesson still works with one
fewer preparation pulse. Its failure tells the teacher to switch to
practice. `prepared_probe_reports_failure` fixes the same meaning for the
physical signal. If failure is encoded by a gain in the strong band and
success by a gain in the weak band, the learner fires exactly on failure.
When the selector starts off, its final log-gain reads as on exactly when
the discrete commit selects practice. This holds for every first-contact
execution complete through the constructed horizon.

## The last preparation pulse determines the probe gain

The [one-cell assay](LessonProbe.lean) starts both runs with the same physical
state and unit gain on the probe port. It schedules a common diagnostic pulse
at offset 9 and a readout pulse on the same port at offset 17. The two lessons
differ by the preparation pulse on port 1 at offset 1.

| Last preparation pulse | State during the diagnostic | Probe log-gain at offset 17 | Readout through offset 18 |
|---|---|---:|---|
| Present | Protected recovery | 0 | Silent |
| Omitted | READY | 0.6 | One FIRE |

In the prepared case the diagnostic completes its sensor cycle during
protection and leaves the gain unchanged. In the omitted case it completes
an exposed ERROR phase and raises the log-gain by `3/5`. Lean proves that
`exp(3/5)` is in the strong band. The readout uses the actual state carried
from the lesson, including charge, recovery and energy. Only FIREs in the
readout window report failure.

`lesson_probe_run_exists` constructs the whole history and
`lesson_probe_crossing_exists` gives the same history under upward crossings.
`LessonProbeAdmission.gain_every_complete` fixes the gain at admission for
all complete first-contact histories. At offset 18, the failure signal is
the same for all complete histories under either semantics. Both fabrication
boxes are covered.

`LessonProbeRun.reports_example_failure` matches the two outcomes of the
discrete validation at its last preparation slot. The assay implements that
varying slot. The earlier discrete lesson pulses are outside this assay.

## The lesson and selector update in one execution

The [routed lesson](RoutedLesson.lean) puts the teacher in cell 0 and the
learner in cell 1. The initial network queue contains only the external
lesson inputs. The router listens to learner FIREs at or after offset 17,
when the readout pulse is admitted. An earlier preparation FIRE sends
nothing to the teacher.

- If preparation is present, the readout stays silent and the teacher's
  selector log-gain stays at 0.
- If preparation is omitted, the learner's actual readout FIRE schedules
  exactly one delivery to the selector at its firing date plus the wire
  delay. The teacher's selector log-gain reaches `3/5`.

`routed_lesson_crossing_exists` constructs this history through offset 26.
`RoutedLessonRun.every_complete` and `every_crossing_complete` give the
same physical endpoint, FIREs and deliveries in every complete execution at that
horizon. The result covers both fabrication boxes and delays in
`[0.3, 0.4]`. The selector value now comes from the actual lesson and
readout.

## The selector sends the next pulse

The [dispatch proof](Dispatch.lean) adds two clock pulses on the teacher's
selector port at offsets 50 and 58. Both clocks are in the initial queue
in both cases. The teacher starts dispatch from the state carried out of
the lesson, including its learned selector gain. The learner also retains
its state and finishes any remaining recovery before the return.

| Selector after the probe | First teacher FIRE | Learner receives |
|---|---|---|
| High, after omitted preparation | After clock 50 | Practice pulse on port 1 |
| Low, after successful preparation | After clock 58 | Preparation pulse on port 0 |

At low gain the first clock is silent and adds a full ERROR dose. The
second clock then crosses the firing threshold. The same fixed router
uses the actual FIRE date to select the destination port and schedules
the return after the wire delay.

`dispatched_lesson_crossing_exists` constructs one execution from the
initial lesson through receipt of the selected pulse on the original
learner. `DispatchedLesson.every_crossing_complete` transfers the physical
endpoint and FIREs to all complete executions through that receipt horizon.
The horizon is the selected FIRE date plus its wire delay. In the early
case the second clock is still due later. The proof covers this first
dispatch and receipt.

## A selector read that preserves the gain

The [prepared read](SelectorRead.lean) uses one canonical selector pulse
and the same starting charge band `[0.650, 0.780]` for either stored value.
The high log-gain `0.6` produces a FIRE between offsets 0.1 and 0.195.
The low log-gain `0` produces a FIRE between offsets 0.3 and 0.8.
Both fires start protection before the sensor's ERROR phase, and
protection continues through the end of ERROR.

`SelectorReadRun.reads_high_after_wire` separates the two cases even
after a delivery delay in `[0.3, 0.4]`. The receiver can compare its
delivery date with offset `0.5975` from a reference within `0.0025` of
the actual read-pulse arrival. This is a timing guarantee for a receiver
with that reference.

`prepared_selector_read_crossing_exists` constructs both reads under the
upward-crossing semantics in either fabrication box. Each read is complete
through the sensor's return to READY, with the raw input expired and all
log-gains and recovery preserved. `SelectorReadRun.gain_at_prefix` proves
gain preservation at intermediate cuts. `SelectorReadRun.every_crossing_complete`
transfers the exact FIRE and gain values to every complete crossing
execution through that horizon. `capped_selector_read_crossing_exists`
also constructs both reads at recovery `1.1`. Protection covers the
whole ERROR phase and recovery stays at the cap.

### Precharge on a saturated work port

A full pulse at the work port's fabrication cap would take a resting
READY cell above threshold. The [precharge proof](SelectorPrecharge.lean)
uses only the part of that pulse left after the cell reopens. It covers
reopening at pulse age `[0.556, 0.55965]` in either fabrication box, or at
age `[0.53, 0.59]` in the ±0.3% box.

`capped_work_precharge_of_reopened` shows that an isolated continuation
from such a reopening stays READY without firing and reaches the read
band at pulse age `1.4`. It uses the actual raw-expiry jump. The work
gain stays at its cap and the unused selector port preserves its gain
when its sensor starts at rest. The proof applies across legal sensor
transitions, including ERROR on the work port.

### The teacher schedules its own reopening

[`teacher_own_fire_reopen_exists`](TeacherReopen.lean) starts from an
admitted ignition pulse on a READY teacher with recovery `0.08` and an
empty queue. Its actual FIRE schedules a work pulse on itself at a fixed
offset of approximately `11.236009` time units. The execution goes
through FAST, admits the scheduled pulse during SLOW, and performs the
actual READY reopening while the work pulse is still active. The gains
are preserved. `TeacherOwnFireReopen.toCrossing` gives the same history
with genuine upward crossings.

The work pulse's MARK phase raises recovery to `0.18`. The calculation
uses its actual onset and duration. The resulting reopening is in
`[0.556, 0.55965]` across the full ±10% box, without choosing a delay
from the fabrication parameters or selector value. The constructed
history uses the exact offset. `teacher_reopen_age_with_jitter` gives a
conservative symmetric tolerance of `0.00005` for its solved clock.
Once recovery reaches `0.18`, the same timer would send the next work
pulse after the quiet teacher has already reopened.

`TeacherOwnFireReopen.every_complete` and
`TeacherOwnFireReopen.every_crossing_complete` identify the same
physical endpoint and the same firing date in all complete runs of
this local setup through the constructed reopening horizon.

### A reusable clock at the recovery cap

[At `b = 1.1`](TeacherStableClock.lean), every legal continuation
preserves recovery. SLOW lasts exactly `log(5/2) / 1.1` after FAST,
even when a work pulse triggers MARK. The local work delay is centred
at `1 + log(5/2) / 1.1 - 0.557825`, about `1.27517`. A different delay
may be realized at each FIRE. Every delay within `0.001825` of that
centre puts reopening in `[0.556, 0.55965]`, the window certified in
both fabrication boxes. `capped_teacher_jitter_iff` gives the exact
symmetric budget for this particular window. The output wire after
the read still has its separate timing bound.

`capped_teacher_fire_work_window` locates the real reopening in any
actual continuation through it, with the work token already admitted
and still active. `capped_teacher_precharge_of_execution` gives the
read charge band at work-pulse age `1.4` for an isolated continuation
with the work gain at its cap. It preserves the gain on other ports
whose sensors start at rest.

The capped timing and precharge results assume recovery is already at
its cap. The clock results identify the reopening in an actual
continuation that reaches the stated horizon.

### From work admission to a completed read

[`CappedWorkRun.lean`](CappedWorkRun.lean) constructs the continuation
from a prepared work pulse already admitted during SLOW. The work gain
and recovery are at their caps. The sensor still goes through MARK,
SILENT and ERROR. The execution reopens at the physical SLOW guard and
consumes raw expiry at its real date, including when expiry and the
start of ERROR coincide. The cell reaches the read charge band at
work-pulse age `1.4`, without firing during precharge.

At that date, a selector pulse from the initial queue is admitted.
`prepared_capped_work_read_crossing_exists` constructs both stored
values with the same work/read protocol for either fabrication box and
every local delay in the certified budget. The combined execution
preserves all gains and emits exactly one spike, from the read.
`CappedWorkRead.every_complete` and `CappedWorkRead.every_crossing_complete`
give the same endpoint and spike date at the common completion horizon.

### From the controller's own FIRE to the learner

[`capped_teacher_cycle_exists`](TeacherCappedCycle.lean) starts from a
prepared controller with an admitted ignition pulse and an empty queue.
Its actual ignition FIRE creates both local deliveries. Work reaches
port 0 during SLOW. The read reaches port 2 exactly 1.4 time units after
work arrives. The controller emits one ignition spike and one read
spike, keeps every gain, and finishes with recovery at its cap.
The module checks complete histories at first contact and under upward
crossings.

[`prepared_capped_dispatch_both`](CappedDispatch.lean) uses the same fixed
router for both stored values, within either fabrication box. It obtains
an absolute ignition reference from the prepared charge `q = 0.1` and
ignition gain `2`, which are shared by both cases. The high read fires
before age 0.195 and the low read after age 0.3. The decoder places its
cutoff halfway between them, at nominal read age 0.2475. That leaves
0.0525 of timing margin on either side. The work delay uses at most
0.001825 of that margin. The read delay relative to work is exact in
this construction. The output wire is selected at FIRE, before its own
delay. It delivers to learner port 1 for high and port 0 for low, with
any delay in [0.3, 0.4]. The global queue starts empty. The certified
upward-crossing execution runs through actual admission at the learner.

| Controller resource | Use |
|---|---|
| Port 0, gain at cap | Work pulse |
| Port 1, prepared gain 2 | Ignition |
| Port 2 | Selector |
| Recovery at cap | Stable reopening clock |

The two credit gains belong to a separate memory cell in this design.
The dispatch theorem contains the controller and receiver. Connecting a
credit cell and feeding the previous round into this controller remain
open, as does the full native `8 → 7 → 6` lesson sequence. Saturated
recovery and the prepared ignition gain are initial conditions. From
`b = 0.08`, ten full MARK doses of 0.1 leave recovery at 1.08, so
preparing the cap by MARK would require an eleventh protected section
with the last dose cut short. No such preparation sequence is part of
this theorem.

## Verify

Run from the repository root with Lean 4.35.0 available:

```sh
cd research/recursive-learning/native
lake exe cache get
lake build
```

The [dedicated CI workflow](../../../.github/workflows/recursive-learning.yml)
builds this package with the pinned dependencies. Its default targets compile
`NativeLearning`, `Feedback`, `LessonProbe`, `RoutedLesson`, `Dispatch`,
`SelectorRead`, `SelectorPrecharge`, `TeacherReopen`, `TeacherStableClock`
`CappedWorkRun`, `TeacherCappedCycle` and `CappedDispatch`, and run
[the axiom audit](NativeAudit.lean), which checks all imported declarations
under `RecursiveLearning`, including private ones.
Unexpected axioms and admitted proofs fail the build. The underlying R imports
and Mathlib pins come from the existing proof package.
