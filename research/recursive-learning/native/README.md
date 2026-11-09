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

The queue in this construction is supplied in advance. The later [serial
experiment](#the-native-8--7--6-experiment) constructs the deployed lesson counts.

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
credit cell to this capped controller and reusing its read remain open.
The serial experiment below uses a one-shot selector. Saturated recovery
and the prepared ignition gain are initial conditions here. From
`b = 0.08`, ten full MARK doses of 0.1 leave recovery at 1.08, so
preparing the cap by MARK would require an eleventh protected section
with the last dose cut short. No such preparation sequence is part of
this theorem.

## Full lessons and a routed acceptance test

[`native_lesson_improvement_trials`](NativeLesson.lean) constructs one
complete upward-crossing execution of five independently prepared R learners.
Each preparation or practice delivery writes a dose of 0.6 into the
corresponding input gain. Both gains start at −2.4 so that up to four
successive inputs per port stay weak. The terminal test agrees with the
discrete learner's retention test for ordered preparation and practice
blocks. Practice deliveries write to their gain counter even if the
preparation requirement is unmet.

| Preparation and practice | Actual deliveries | Native terminal result |
|---|---:|---|
| 4 and 4 | 8 | Passes validation and retains for both held-out learners |
| 3 and 4 | 7 | Passes validation and retains for both held-out learners |
| 3 and 3 | 6 | Passes validation and retains for both held-out learners |
| 2 and 4 | 6 | Fails the validation learner with needs (3, 2) |
| 3 and 2 | 5 | Fails the validation learner with needs (2, 3) |

A separate [acceptance test](NativeAcceptance.lean) starts its counter
gain at −1.2. After two pulses its gain is 0, and after three it is 0.6.
A common test pulse triggers a FIRE only in the three-pulse case.
[`native_acceptance_writes_credit`](NativeAcceptance.lean) routes that
FIRE to a chosen port of a separate credit cell. The pulse is absent
from the initial queue. It writes one dose on acceptance and no dose
on rejection.

[`native_acceptance_dispatches_six`](AcceptanceDispatch.lean) uses
the same test to release a full 3 + 3 lesson to a fresh learner. The
learner starts with no scheduled lesson inputs. The fixed router
releases all six on the actual acceptance FIRE, and the resulting
state retains the skill for needs (3, 3). With two test inputs the
receiver gets no lesson. The common test pulse is outside the six-pulse
lesson count.

## The native 8 → 7 → 6 experiment

[`native_eight_seven_six`](SerialAcceptance.lean) constructs a single
complete upward-crossing execution of seven R cells. Only the baseline
lesson, the first test and the selector's clock have external sources
in the initial queue. The seven- and six-pulse lessons come from actual
test firings. The construction holds in either fabrication box with
independent fixed parameters for each cell.

1. The first test writes one preparation credit and schedules the
   seven-pulse lesson. It also launches the second test with two
   default inputs.
2. In the adaptive run, the first test sends one extra pulse to the
   selector. The selector's own readout FIRE supplies the third input
   to the second test.
3. The second test fires, writes the practice credit on the same
   credit cell and schedules the six-pulse lesson.

| Configuration | Baseline deliveries | First improved lesson | Second improved lesson | Credit gains |
|---|---:|---:|---:|---|
| Adaptive | 8 | 7 | 6 | 0.6, 0.6 |
| Selector update blocked | 8 | 7 | 0 | 0.6, 0 |

Both runs start from the same physical snapshot. Blocking the single
selector update leaves the second test with two inputs, so it rejects.
The baseline and the seven-pulse lesson both meet needs (3, 3) in both
runs. The six-pulse learner meets those needs in the adaptive run.
At the stated horizon, all complete upward-crossing executions agree
on the terminal physical state and the ordered firing dates of each
cell. Complete first-contact executions deliver the same tokens up to
permutation.

The router contains the calendars for this particular experiment.
In this experiment the acceptance tests are counters fed by the routed
calendar. They do not yet read the learners’ physical state. Feeding
them from learner readouts is the next step. The lesson receipts
exclude probes, clock inputs and credit deliveries. The
selector is read once, and the low read can write to its sensor gain.
A reusable selector and an adaptive rule for arbitrary lesson shapes
are separate problems.

## Feedback from a learner's actual readout

[`learner_readout_commits_trial`](LearnerReadout.lean) delivers the whole
trial to one R learner. The learner's own gains record both input blocks.
A common probe then reads the port whose block was shortened. In the
preparation comparison it distinguishes 2 + 4 from 3 + 4. In the practice
comparison it distinguishes 3 + 2 from 3 + 3. The other block meets its
requirement in both comparisons. The learner's real FIRE writes a
0.6 dose on the corresponding credit port. A silent read leaves that
credit at zero.

[`preparation_failure_updates_selector`](LearnerReadout.lean) tests the
opposite signal. The 2 + 4 learner receives six lesson pulses and a
common read pulse. Its silent read leaves a diagnostic cell exposed.
That cell fires and its output writes 0.6 on the selector. With 3 + 4,
the learner's real readout FIRE protects the diagnostic cell and no
feedback token reaches the selector. Both cases use the same router
and diagnostic clocks. The extra read pulse is outside the lesson count.
The selector experiment covers both fabrication boxes and output wire
delays in [0.3, 0.4]. Complete upward-crossing runs agree on the endpoint
and firing dates at the common horizon.

These local results provide the learner and diagnostic traces used in the
readout-driven serial experiment below.

## The 8 → 7 → 6 experiment with learner readouts

[`native_readout_eight_seven_six`](ReadoutSeries.lean) composes the
readout-driven updates in one complete upward-crossing execution of nine
R cells. The original seven-cell construction above uses calendar-fed
tests. In this version the learners that receive the actual trial
pulses supply the acceptance signals.

1. A fresh learner receives the full 3 + 4 trial. Its common read
   pulse sees the preparation gain acquired by that trial. The
   learner's FIRE writes the preparation credit, schedules the
   seven-pulse lesson and launches the full 2 + 4 trial.
2. The 2 + 4 learner receives all six trial pulses and its own read
   pulse. Its silent read leaves the diagnostic cell exposed. The
   diagnostic readout FIRE issues the feedback pulse to the selector.
3. The selector's common read pulse sees the gain written by feedback.
   Its FIRE launches the full 3 + 3 trial. That learner's own readout
   FIRE writes the practice credit and schedules the six-pulse lesson.

The deployed lessons are received by separate fresh cells. Their
delivery counts are 8, 7 and 6. Each completed lesson meets needs
(3, 3). In the control with the selector update wire cut, the same
initial snapshot yields the same first credit and seven-pulse lesson.
The selector stays silent at its readout, the practice trial is absent
and the practice credit stays zero.

The theorem holds in either fabrication box with independent fixed
parameters. At the common horizon all complete upward-crossing
executions agree on the terminal state and ordered firing dates.
Complete first-contact executions also agree on the multiset of
deliveries. The experiment uses fixed candidate shapes and clocks, a
one-shot selector, and one diagnostic cell. The other lesson block
already meets its requirement in each trial, so each acceptance reads
the block under test. Counts for deployed lessons exclude trial inputs,
read pulses, diagnostic inputs and credit writes.

## A credit that requires two learner reports

[The four-cell theorem](LearnerConjunction.lean#L255) uses the same router
for all four combinations of passing and failing trials. Two cells
receive and read their own lessons. The preparation trial varies between
2 + 4 and 3 + 4 pulses. The practice trial varies between 3 + 2 and 3 + 3.
Each learner needs three pulses of each kind. A learner reports a pass
by firing on its read pulse.

The router sends each report to the same counter at its own reserved
time. The counter starts at log-gain −0.6 and gains 0.6 per report.
Its common read pulse fires only after both reports. That FIRE sends
one pulse to the credit cell, which records exactly one dose of 0.6.
The initial queue contains the trial and read pulses. The reports and
the credit pulse are generated by the network during the execution.

The counter proof works for any positive number of reserved slots. With
at most one dose per slot, at least eight time units between delivered
doses, and a common read after the dose cycles, its read fires exactly
when the number of doses equals the configured arity. The four-cell
network uses two slots and a single read. It covers independent fixed
parameters in either fabrication box. All complete upward-crossing
executions from each initial queue agree on terminal observations and
firing dates at the stated horizon.

## Any finite number of learner reports

[`native_learner_fan_in`](LearnerFanIn.lean) extends the conjunction to
any positive number of independently fabricated learners. Each learner
receives its trial and read pulse. Its actual readout FIRE, when present,
sends a dose to its reserved counter slot. The router and the probe time
depend on the number of learners and their clock, while the trial queues
determine which learners report. The counter issues one credit if every
trial passes. All complete upward-crossing executions agree on the
terminal observations and the ordered firing dates.

[`compose_scheduled_receiver`](LearnerFanIn.lean) joins an arbitrary
sender network to one receiver. The receiver's local execution must
admit exactly its external inputs and the strictly causal tokens
issued by the sender. The composed initial queue contains the external
inputs. The fan-in theorem uses this operation to connect the learners
to the counter and the counter to the credit cell.

## Connecting report gates

[`ScheduledGates.lean`](ScheduledGates.lean) defines a report as zero or
one FIRE in a declared time window. A cell's local contract includes its
actual input deliveries and can specify a terminal effect. The NOT
cell's optional trigger can produce an earlier preparation FIRE. The
router forwards only FIREs in the report window.

The composition theorems attach an AND with any positive number of
inputs, or a NOT with one input, to an existing execution. The wires
schedule tokens at declared dates, and the original cells retain their
firing dates. A wire can forward a list of tokens, and multiple wires
can read the same report. The [NAND construction](ScheduledGates.lean)
connects an AND and a NOT in series in one native execution.

## Compiling finite report circuits

[`ReportCircuit.run_with_learners`](ScheduledCircuit.lean) lays out any
finite acyclic circuit of AND and NOT gates over physical learner
reports. The circuit fixes the wiring and the absolute clocks. The
delivered trials determine the input bits. Each compiled gate
implements its Boolean output through native R dynamics. Complete
upward-crossing executions agree on the endpoint and firing dates.

[`threshold_report_network`](ReportFormula.lean) constructs an output
that fires exactly when at least k inputs pass, including OR at k = 1.
It composes Boolean gates so that excess reports have their intended
effect. The formula expands into separate gates and can grow rapidly.

[`ReportCircuit.run_guarded_branch`](ScheduledCommit.lean) attaches a
credit cell and a fresh lesson receiver to a decision output. A true
report issues one credit dose and the declared lesson. A false report
delivers zero tokens to both action cells. Tests inside the circuit
can still receive inputs. The branch theorem also compares the
delivery multiset of every complete upward-crossing execution.

[`compile_finite_teaching_program`](ScheduledProgram.lean) composes a
report circuit with any finite plan of guarded credit and lesson
actions. Each action has fresh receivers. The theorem records the exact
credit and lesson delivery counts for every action and the resulting
credit log-gains. All complete upward-crossing runs agree on the terminal
observations, ordered firing dates and the multiset of actual deliveries.
[`finite_teaching_program_fixed_wiring`](ScheduledProgram.lean) proves
that the router, report windows and horizon are shared across trial
outcomes.

The inputs are the declared learner trials. The actions deliver their
lessons to fresh receivers with at most four pulses per block. The
compiled circuit is feed-forward, with fixed clocks and one decision
round. An inactive action receives neither a credit nor a lesson.
Internal test cells can still receive partial input.

## Several adaptive rounds

[`compile_finite_adaptive_program`](AdaptiveRounds.lean) compiles a
finite sequence of logic, trial launches and guarded credit or lesson
actions. A later learner starts with an empty queue. An earlier report
routes both the lesson and the read pulse to that learner. Its own
readout can then feed a gate or launch another trial. In the
[two-trial example](AdaptiveRounds.lean), a first trial can receive its
full lesson, fail the readout, and leave the second trial with zero
deliveries.

The router and report windows are fixed across initial trial outcomes.
Each activated trial receives its full lesson and one read pulse.
Each skipped trial receives zero inputs. The credit and lesson counts
of guarded actions remain exact across later stages. Complete
upward-crossing executions from each initial state agree on the
terminal observations, ordered firing dates and delivery multiset.

The layout uses fresh cells for later trials and fixed absolute
clocks. Trial lessons have at most four pulses per block. A trial
declares a calibrated birth gain and proves that its physical readout
implements the corresponding retention test.

## Searching for an unknown need

[`blind_search_recovers_need`](BlindNeedSearch.lean) uses the same
router, clocks and initial pulse queue for all four combinations of
preparation and practice needs in {3, 4}. The hidden profile sets
birth gains on the ports that will be read. The practice test uses
two possible fresh receivers with the same hidden practice gain.

An eight-pulse reference lesson starts the search. The 3 + 4 probe
tests preparation. Its physical report determines whether the next
trial receives 3 + 3 or 4 + 3. The practice report selects the final
lesson. The selected receiver alone gets its lesson and the associated
credit cell writes exactly one dose. The theorem checks the learned
gains of the selected receiver and proves minimality under the declared
two-block retention criterion.

| Hidden preparation | Hidden practice | Selected lesson |
| --- | --- | --- |
| 3 | 3 | 3 + 3 |
| 3 | 4 | 3 + 4 |
| 4 | 3 | 4 + 3 |
| 4 | 4 | 4 + 4 |

## Compiling a calibrated decision tree

[`compile_calibrated_decision_tree`](CalibratedDecisionTree.lean)
compiles a finite tree over any declared family of birth profiles.
Each probe has one lesson and one read port across all profiles.
Its calibration certifies the report for each profile. The compiler
fixes one router, one schedule and one initial pulse queue. A
positive report launches the yes branch. Silence launches the no
branch only if the probe was activated.

Only the reached leaf receives its lesson and one credit pulse.
The theorem checks the learned gains at the leaf and the actual
delivery counts on every leaf. All complete upward-crossing runs for
each profile and fixed fabrication agree on terminal observations,
firing dates and deliveries. The four-profile search above also
instantiates this tree interface.

The binary-search construction bisects the declared interval and
selects the action indexed by the hidden need. Its hypotheses require
calibrated physical comparisons at the pivots. The existing fixed
log-gain encoding certifies some comparisons, including the
three-versus-four example. Other pivot comparisons require their own
calibration proof.

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
`SelectorRead`, `SelectorPrecharge`, `TeacherReopen`, `TeacherStableClock`,
`CappedWorkRun`, `TeacherCappedCycle`, `CappedDispatch`, `NativeLesson`,
`NativeAcceptance`, `AcceptanceDispatch`, `SerialAcceptance`,
`LearnerReadout`, `ReadoutSeries`, `LearnerConjunction`, `LearnerFanIn` and
`ScheduledGates`, `ScheduledCircuit`, `ReportFormula`, `ScheduledCommit` and
`ScheduledProgram`, `AdaptiveRounds`, `CalibratedDecisionTree` and
`BlindNeedSearch`, and run
[the axiom audit](NativeAudit.lean), which checks all imported declarations
under `RecursiveLearning`, including private ones.
Unexpected axioms and admitted proofs fail the build. The underlying R imports
and Mathlib pins come from the existing proof package.
