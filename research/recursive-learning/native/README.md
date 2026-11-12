# Native R memory for the adaptive teaching loop

The [discrete example](../README.md) has two teaching credits and a selector.
Here each is encoded in the log-gain of a separate port of one actual R cell.
One full exposed ERROR section adds `3/5` to its port, which represents one
credit or sets the selector. The encoding is relative to that port's starting
log-gain.

> **Start here.** Training that stops by itself, networks of trained
> cells and searches built with them are summarized in the
> [map of the stop-learning results](#map-of-the-stop-learning-results),
> which names the strongest statement at each level. The
> [v0.4.0 release notes](../../../docs/RELEASE_V0_4_0.md) give the short
> version, and [STOP_LEARNING_SPEC.md](STOP_LEARNING_SPEC.md) states the
> regime. The sections below this one describe the earlier native memory
> of the teaching loop.

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

[`compile_native_binary_need_search`](CalibratedDecisionTree.lean)
bisects the interval from 1 to K for any positive K. Each pivot
uses the native threshold probe, with the same hidden need encoded
in the birth gains of all its probe cells. The router, source queue
and windows are fixed across needs. The action indexed by the
hidden need receives its lesson and credit, and every other leaf
receives zero inputs. Leaf lessons retain the four-pulse limit per
block.

## A threshold probe with excess pulses

[`threshold_count_probe_crossing`](ThresholdProbe.lean) proves a
physical comparison for any positive hidden need and any tested pulse
count. For a hidden need of m, the initial log-gain is `−0.6(m − 1)`. Training pulses and the
common read are spaced by 24 time units. Before the threshold, each
training pulse adds one dose. Once the gain reaches 0.6, later pulses
can cause FIREs and complete their recovery while preserving both
gain and recovery rate. Those FIREs precede the report window.

The common read reports exactly when the tested count meets or
exceeds the hidden need. Its queue and report window depend on the
tested count. All complete upward-crossing executions for each fixed
setup agree on the endpoint, firing dates and deliveries. In a compiled
decision tree, an upstream report sends the entire threshold packet. Only the final read window feeds the next decision.

## Reusing a learned choice in two rounds

[PolicyReuse.lean](PolicyReuse.lean) compares two possible first edits
to the same two-by-two lesson. The two declared profiles need either
two preparation and one practice pulse, or one preparation and two
practice pulses. Each profile has exactly one successful single-pulse
reduction.

A physical calibration probe tests the preparation reduction. Its
silence enables a diagnostic FIRE, which routes three separated pulses
to one policy cell. Those doses take the cell's log-gain from -1.2 to
0.6. Each of two later read windows on that same cell chooses the
practice reduction if the cell fires, and the preparation reduction
if it stays silent. The second window follows the first trial window.
Each round delivers one three-pulse lesson and its read pulse to the
selected learner. The other candidate receives zero deliveries.

| Profile | Feedback | First choices accepted in the two rounds |
| --- | --- | --- |
| Needs two preparation pulses | Enabled | 2 of 2 |
| Needs two preparation pulses | Cut | 0 of 2 |
| Needs one preparation pulse | Either | 2 of 2 |

The router and birth pulse queue are fixed across profiles for each
feedback setting. The comparison counts rejected first choices on the
two evaluation rounds separately from calibration traffic. The
theorem constructs a complete upward-crossing execution for either
fabrication box. All complete executions with the same setup agree
on endpoint observations, firing times and delivery multiplicities.

The experiment uses fresh, identically calibrated learners, a fixed
schedule and one policy update. At the high gain, both reads leave the
learned gain intact. At the low gain, both reads are silent and each
writes a dose. The two-read guarantee therefore uses the declared
initial low gain and its two remaining silent read slots.

## A two-port readout with a tolerant FIRE threshold

[ThresholdTolerance.lean](ThresholdTolerance.lean) proves a one-shot
task for a single R cell. Starting just after admission of one canonical
pulse, the cell reports which of two ports received it. On port 0, a
gain at most 1.2 gives silence through time 0.9. On port 1, a gain in
[2, 2.4] gives a transverse FIRE between times 0.3 and 0.9. Times are
relative to admission. The two gains are fixed for the cell and may
vary independently within those bounds. The unused third port has
gain at most 3.6, which keeps the starting state within the physical
gain caps for either fabrication box.

The actual main FIRE threshold is a parameter in [0.95, 1.05].
Fabrication parameters can independently take any values in either
declared fabrication box. The prefix uses the original sensor MARK
and SILENT events. The final READY flow satisfies the original
integral field in every coordinate, with the main guard set to the
chosen threshold. The FIRE applies the usual READY-to-FAST update.
At threshold 1 the complete decision prefix embeds into an ordinary
kernel execution. The stop time is unique among decision certificates
with the same realized parameters, gains and threshold.

The certificate ends at the first FIRE or the read deadline. The
initial state and gain bounds are part of the task. Sensor thresholds,
actuation factors and recovery guards retain their original values.
Post-decision recovery and the training of these gains are outside
the one-shot specification.

## Error dose with inexact sensor endpoints

[TolerantErrorDose.lean](TolerantErrorDose.lean) derives the dose from
the original integral field for an exposed ERROR segment. If its
realized entry and exit charges are `u` and `l`, the log-gain changes
by exactly `8 * (u - l)`. The cap and energy gates must stay open
and the main cell must stay READY. The sensor's decay rate cancels.

With absolute charge errors `δhi` and `δlo` at the two endpoints, the
dose is within `8 * (δhi + δlo)` of 0.6. After `k` segments with
matching end and start log-gains, the worst-case error is at most
`k * 8 * (δhi + δlo)`. If the two extremal gains lie in the reader's
high band, a prepared read on that port fires.

For a concrete one-dose memory test, the initial gain can be anywhere
in [7/6, 1.2]. Independent relative errors of up to 5% in the nominal
0.1 and 0.025 sensor endpoints put the dose in [0.55, 0.65]. The read
of the initial gain is silent, and the read of the resulting gain on
the same port fires. The high band is [2, 2.4] with the same 0.3 to 0.9
firing window. Both reads tolerate a fixed main threshold in
[0.95, 1.05] and either fabrication box.

The dose and readout bounds above also apply to separately prepared
states. The experiment below joins them in one trajectory.

## Train and read the same port

[ErrorReadHandoff.lean](ErrorReadHandoff.lean) starts with a READY cell
whose selected sensor is already in ERROR, with no live input current.
The sensor discharges from its realized upper charge to its realized
lower charge under the original R equations. Both charges may differ
from their nominal values by up to 5%. The gain and energy gates stay
open, so the dose lies in [0.55, 0.65].

At the lower charge, the sensor switches to READY. Its charge and every
other continuous coordinate carry over. The cell waits under the native
quiet flow and admits the single queued pulse on the same port at a
scheduled time at least twelve units after ERROR entry. Both the main
charge and the sensor reach the readout's starting bands by decay.
Starting at the actual delivery state, the trained port produces a
transverse first FIRE 0.3 to 0.9 time units
after arrival, for every fixed FIRE threshold in [0.95, 1.05] and either
fabrication box. At the nominal ERROR exit and FIRE levels the whole
joined trajectory is an execution of the original kernel.

The supplied ERROR state has main charge in [0.1, 0.94], other sensors at
rest, and energy in [50, 100].

## A complete training pulse followed by a read

[TrainingRead.lean](TrainingRead.lean) starts before the first input,
with one READY cell at rest and two canonical pulses queued on the same
port, sixteen time units apart. The initial gain of that port is in
[7/6, 1.2]. The first pulse drives the sensor
through MARK and SILENT while the cell stays below its FIRE threshold.
The sensor enters ERROR at its realized upper threshold, which can be
before, at, or after expiry of the training pulse. If ERROR starts while
the pulse is live, [LiveErrorExpiry.lean](LiveErrorExpiry.lean) proves
that the current overlaps ERROR for at most 0.04 time units, the main
charge stays below 0.94, and the sensor cannot reach its exit threshold
before expiry. Expiry removes the raw tag and carries the charge, gain
and energy into the rest of the ERROR phase.

The net log-gain increment from training is exactly
`8 * (upper - lower)`. The second pulse produces a transverse first FIRE
0.3 to 0.9 units after delivery. The two ERROR thresholds and the FIRE
threshold each tolerate 5% error. All three nominal levels give a
native R execution from before the first delivery through the read FIRE.

Both full fabrication boxes are covered, ±0.3% and ±10%, with every
parameter fixed independently in its declared interval. The construction
covers one training pulse and one read through the first FIRE.

## Thresholds in the parameters

[HybridParameterExecution.lean](../../../proof/lean/KernelR/HybridParameterExecution.lean)
uses the fixed charge guards stored in each cell's `Parameters`. The
continuous equations, pulse origin and queue rules are shared with the
nominal kernel. Flows and completion check the same realized guards as
jumps.

[ParameterTraining.lean](ParameterTraining.lean) places the two-pulse
experiment in this semantics. Lean constructs a complete run through
the read FIRE for every admissible choice in either full fabrication
box, with the three tolerances above. The other charge guards are
nominal. The experiment covers one training pulse and one read.

[HybridParameterUniversalExecution.lean](../../../proof/lean/KernelR/HybridParameterUniversalExecution.lean)
proves uniqueness for every complete finite run under the declared
threshold and physical bounds, for any fixed finite network and router.
Runs from the same state and with the same realized parameters agree
at a common horizon on their physical endpoint and ordered per-cell
FIRE dates. The pending list is compared up to permutation.

For this two-pulse protocol, `training_read_every_complete` gives a
complete run and the same outcome in every complete run through its
read horizon. The recorded FIRE list contains just that read firing,
and the final log-gain increment is exactly `8 * (upper - lower)`.
The proof uses the first-contact operational semantics. The constructed
read FIRE is transverse.

## Training with an ERROR exit near 0.01

[ParameterTraining.lean](ParameterTraining.lean) proves
`training_read_exit_001_every_complete` for an ERROR exit in
`[0.00875, 0.01125]`. The ERROR entry remains in `[0.095, 0.105]`,
the FIRE threshold in `[0.95, 1.05]`, and the trained port's birth gain
in `[7/6, 1.2]`. The other guards are nominal. Both fabrication boxes
are covered.

A pulse trains the port at birth. A second pulse reads the same port
18 time units later, allowing the sensor to settle into its original
rest band. A complete run exists through the first FIRE. Every run
complete through that horizon agrees on the endpoint and has exactly
one FIRE, between 0.3 and 0.9 units after the read arrives. The final
log-gain increment is `8 * (entry - exit)`, between 0.67 and 0.77.

The same proof takes a variable exit and read delay through
`training_read_every_complete_in_band`. The original 16-unit schedule
and its theorem remain available. These theorems concern the single-cell
task in the parameterized first-contact semantics. The two-cell
coincidence benchmark uses a separate schedule and receiver contract.

## Coincidence timing with an ERROR exit near 0.01

[CoincidenceTiming.lean](CoincidenceTiming.lean) brackets the actual read
FIRE using the charge at read, the learned gain, and the FIRE threshold.
The lower time uses the largest charge and gain and the smallest
threshold. The upper time uses the opposite bounds. The exponential
estimates are proved over the reals in Lean.

`training_read_exit_001_benchmark` fixes the trained port's birth gain
exactly at `exp (gains p) = 6/5`. This satisfies the earlier birth band
`[7/6, 1.2]`. The timing certificate uses the exact value. With a
read at least 16.65 units after training, it gives one FIRE between
0.3485 and 0.398 units after the read in every run complete through
the first FIRE. Both fabrication boxes are covered. With radii `e`
and `f`, the entry and exit tolerances are `0.1e` and `0.025e`
around 0.1 and 0.01 respectively, and the FIRE tolerance is `f`
around 1. All other guards are nominal.

| Maximum ERROR radius `e` | Maximum FIRE radius `f` |
| ---: | ---: |
| 1% | 3% |
| 2% | 2% |
| 3% | 1% |

Lean counts 22 of the 36 registered grid points in these sufficient
rectangles. At 100 microseconds per unit and nominal exit 0.01, these
are exactly the same 22 ERROR/FIRE pairs that passed in the
[recorded sweep](https://github.com/HevisNico/kernel-R/blob/8ff0540cab31f55831ffd3698b36bd2940c872d1/research/recursive-learning/coincidence/results/exit-tradeoff.csv.xz)
at each of its three fabrication settings. The Lean count gives
coverage on this grid. A full characterization of the passing region
would also require proving where the timing contract fails.

`coincidence_of_trained_latency` is an arithmetic lemma with two
latency intervals as hypotheses. At 100 microseconds per unit,
with a common wire delay and independent jitter of up to 5
microseconds, the skew is at most 14.95 microseconds at zero
offset and at least 15.05 microseconds at offsets of −30 or +30
microseconds. These bounds give a certified margin of 0.05
microseconds around the 15 microsecond aperture. The certificate
uses the declared uncertainties only.

The execution theorem is for a single trained-port read through its
first FIRE. A joint two-cell execution, wrong-port trials, the rest
of the observation horizon, and a native receiver have separate
proof obligations. The comparison below addresses the reduced timing contract.

### Constant-current timing obstruction

[TimedCurrentSeparation.lean](TimedCurrentSeparation.lean) uses the
[registered constant-current rule](https://github.com/HevisNico/kernel-R/blob/1f04221262694383b1505a8d064f62903a85a34a/research/recursive-learning/COINCIDENCE_BENCHMARK.md#comparators)
and the same `readyPulse` equation as the R latency theorem. In the
reduced runner, a shared current and duration give a common dose
`d = I * D`, scaled by each device's current multiplier and clipped at
its realized gain cap. The runner requires silent training and positive
reserve. The protocol requires the timer to finish by time 16.

At 100 microseconds per unit, use the wide fabrication box, 10%
current error, 3% FIRE error, ERROR entry 0.1 and exit 0.01. Put the
high-current, high-cap, low-FIRE corner on the early read and reverse
all three signs on the late read. The two reads are at 16.95 and
17.05 with zero offset. Lean proves that for **every shared dose**
this positive trial either lacks a report or has skew at least
15 microseconds. The proof includes capped writes. For doses up to
0.36 it rules out the slow report directly. Seven bounded dose
intervals and one unbounded interval cover the remaining doses.

The obstruction applies to the constant-current **reduced** timing
model with eligible writes, quiet relaxation after training, and a
frozen learned gain during the read pulse. Its training endpoint charge
lies in [0.1, 1.03]. The timed rule has no separate hybrid execution
construction here.

### Two-cell execution assembly

[ParameterExecutionProduct.lean](ParameterExecutionProduct.lean) weaves
two independent parameterized executions at a common clock. The joint
queue retains both cells' deliveries, and the two FIRE lists retain
their exact dates. Local completeness through the same horizon gives
joint completeness.

[CoincidenceReadTail.lean](CoincidenceReadTail.lean) proves that a
trained-port FIRE cannot be followed by another FIRE in any legal
finite continuation of the task. The read pulse ends before FAST can
end. After pulse expiry the cell has no drive and any return to READY
starts below FIRE.

[CoincidenceNetworkContract.lean](CoincidenceNetworkContract.lean)
derives the registered receiver decision at time 20 for every complete
joint run, given two local witnesses complete through that horizon
with the declared FIRE lists. The receiver uses the 0.35 wire delay
and 20.35 arrival deadline.

[CoincidenceLocalExecution.lean](CoincidenceLocalExecution.lean)
constructs a complete wrong-port trial through time 20 with an empty
FIRE list. It retains the actual training trajectory, retargets only
the queued read and bounds the charge during the live-pulse overlap
with ERROR. The wrong port uses its nominal auxiliary guards. The
birth-gain, fabrication and threshold hypotheses of the 0.01 timing
certificate cover the registered read dates from 16.65 to 17.35.

[CoincidenceProtectedTail.lean](CoincidenceProtectedTail.lean) advances
a trained-port run to time 20 after its FIRE. The construction processes
pulse expiry, FAST exit and sensor contacts in time order, including
ties. SLOW remains above its reopening threshold through the horizon.

[CoincidenceSeparation.lean](CoincidenceSeparation.lean) proves
`coincidence_exit_001_full_contract` for two independent cells. A
complete run exists for every admissible pair of read dates and ports.
In every complete run each trained-port read gives exactly one report
and each other read gives none. The receiver accepts exactly when both
ports match the training and the offset is zero. The 0.35 delays and
the coincidence test are applied to the emitted dates by the receiver
contract.

The combined theorem `coincidence_exit_001_separation` uses 100 µs per
model unit, ±10% fabrication and ±3% FIRE threshold error. On each
trained port, the ERROR entry can vary by up to 0.001 around 0.1 and
the exit by up to 0.00025 around 0.01 (radius `e ≤ 0.01` in Lean).
The other ports keep their nominal auxiliary thresholds. Native R
satisfies the full receiver contract throughout this box.

For the reduced constant-current rule with ±10% current variation, one
positive trial with nominal ERROR endpoints excludes every common
current and duration, including settings that touch the gain cap.
Those endpoints belong to every admitted ERROR box. The proof uses
the exact trained birth gain 1.2. The receiver is an observation of
two native runs and the comparator uses the reduced READY equation.

## Map of the stop-learning results

The sections from here to [Verify](#verify) form one line of work:
training that stops by itself, from one pulse to networks and searches.
No gain and no FIRE level is set by hand in it. This map lists the
strongest statement at each level. The sections below follow the order
in which the theorems were proved, so some of them state an earlier and
weaker form.

| Level | Statement | Theorem | File |
|---|---|---|---|
| one pulse | a silent pulse writes one dose, a firing pulse writes nothing and its date is known | `silent_step_exists`, `firing_step_dated` | `SilentStep`, `FiringStep` |
| one port | training stops by itself for every start gain | `stop_training_exists` | `TrainingLoop` |
| one port | the need of a port, and its tolerance to fabrication | `self_calibrated_probe_exists`, `needIs_of_tolerance` | `SelfCalibratedProbe`, `NeedTolerance` |
| one cell | two trained ports read in either order: the FIRE comes later than 0.239 units after the first pulse and no later than 0.256 after the second | `OpenCell.read` | `FreeRead` |
| one cell | one read pulse fires late, two fire early | `OpenCell.read_one` | `SearchCells` |
| composition | cells joined by wires, from one-cell runs | `routed_execution` | `RoutedProduct` |
| composition | forward wires: complete run, unique FIRE dates and final values | `acyclic_network_states` | `AcyclicNetwork` |
| composition | report windows and pulses at fixed dates | `signal_network_states` | `SignalNetwork` |
| network | any number of trained cells joined by wires | `trained_wired_network` | `WiredNetwork` |
| network | the coincidence decision with a settling lag in each cell | `trained_network_lag` | `ReadLag` |
| search | a forest of questions, with final gains and pulses sent | `trained_search` | `TrainedSearch` |
| search | a lesson after the last answer | `search_action_witness` | `SearchActions` |
| search | `k` questions asked out of `2 ^ k - 1` | `bisection_search` | `BisectionSearch` |
| search | `2 k + 1` cells for `2 ^ k` needs, with the learner | `successive_search` | `SuccessiveSearch` |

Earlier forms that the table replaces:

- `TrainedCell` and `trained_read_exists` hold the read pulses in the
  queue of the cell, in a fixed order. `OpenCell` and `OpenCell.read`
  take them from anywhere, in either order. `TrainedCell` is still used
  by the two-cell and `n`-cell contracts without wires
  (`trained_coincidence_network`, `trained_network`).
- `acyclic_network` and `signal_network` are the two composition
  theorems without the final states. They are corollaries.

The regime, common to every statement of the table:

| Quantity | Hypothesis |
|---|---|
| FIRE level | in `[0.95, 1.05]`, one value per cell |
| ERROR entry threshold | in `[0.07, 0.08]`, one value per port |
| ERROR exit threshold | at least `0.005`, below the entry |
| dose `8 * (entry - exit)` | positive; at most `1/20` for the read windows |
| recovery rate at the start | in `[0.07, 0.1]` |
| pulses on one cell | at least 22 units apart |
| other parameters | anywhere in the fabrication box, 0.3% or 10% |
| wires | positive delay, or fixed dates after the window of the sender |

Every network statement gives a complete run and proves that every
complete run has the same FIRE dates.

## Read latency after training that stops at the first FIRE

[StopLearningLatency.lean](StopLearningLatency.lean) studies the READY
read equation of a rested cell. It does not build a hybrid execution.

A training pulse of relative amplitude `c` acts on the main charge as a
canonical pulse at gain `c * gain`. In R, a training pulse that makes
the cell fire writes nothing, because the cell is protected during the
sensor's ERROR phase. Training by weakened pulses therefore stops at the
first FIRE. `StoppedTraining gain c fire d` describes that state: the
current gain fires on a weakened pulse, and the gain before the last
increment, of at most `d` in log-gain, did not.

`stopped_read_response` gives the response level `h(t)` reached at the
FIRE of a later full-amplitude read:

```text
c * exp(-d) * h(1)  <  h(t)  ≤  c * h(1)
```

The gain and the FIRE threshold do not appear. The increments may be
unequal and inexact, as long as each is positive and at most `d`.
`stopped_read_latency` turns the two levels into a latency window, and
`stopped_read_skew` bounds the latency difference of two cells by the
width of that window, whatever their gains and FIRE thresholds.
`stopped_read_exists` shows that a cell which fires on a weakened pulse
fires on a full one.

For `c = 2/3` and `d = 1/20`, `stopped_read_latency_two_thirds` gives a
read FIRE between 0.355 and 0.385 model units after the pulse, and
`stopped_read_skew_two_thirds` a difference below 0.03 units between two
cells. The coincidence theorem uses a window of 0.0495 units and needs
an exact birth gain and a FIRE threshold within ±3%.

The stopping rule is the stop-learning principle of Brader et al.,
which Noack et al. implement in switched capacitors. These theorems
state its consequence for the R read equation.

**The ratio from two ports.** The kernel adds the currents of the ports,
so the amplitude ratio need not come from the pulses. Train two ports
separately with canonical pulses until each makes the cell fire, then
read with one pulse on each port at the same time. `stopped_pair` shows
that the pair is in the stopped state at relative amplitude one half.
The ratio is exact because it counts ports. With increments of at most
`1/20`, `stopped_pair_read_latency` gives a read FIRE between 0.239 and
0.256 model units, and `stopped_pair_read_skew` a difference below 0.017
units between two cells, whatever their four gains and two FIRE
thresholds.

**Training ends.** `training_stops` takes any sequence of log-gain
increments between a positive lower bound and `d`, starting from a gain
whose pulse is silent. Some pulse is the first to fire, every earlier
pulse was silent, and the cell is then in the stopped state.

**A rest charge that is only close to nominal.** Between pulses the main
charge relaxes toward 0.1 without reaching it.
`stopped_read_response_residual` takes rest charges within `δ` above
0.1, at the firing pulse, at the last silent pulse and at the read. The
window keeps its form, with the two levels multiplied by factors that
tend to one with `δ`. The gain and the charges do not appear in it.

What they assume and do not prove:

- The cell is at its rest charge 0.1 before each training pulse and
  before the read.
- For a ratio taken from the pulses, `c` is exact and the same for every
  cell. For two ports, the two read pulses arrive at the same instant.
- The sequence of gains is given. No hybrid execution is constructed in
  which a silent pulse writes an increment and a firing pulse writes none.
- The pulse shape is canonical.

## Native training that stops at the first FIRE

[NativeStopLearning.lean](NativeStopLearning.lean) constructs the
stopping rule as an execution of the kernel, at nominal thresholds. It
reuses the existing weak-pulse and learned-FIRE constructions and adds no
definition to the kernel.

- `silent_slot_exists`: a pulse on a port whose gain is at most `7/6`
  leaves the cell silent and writes the full dose `3/5` on that port.
- `firing_slot_exists`: a pulse on a port whose gain lies in
  `[9/5, 11/5]` makes the cell fire once, between the pulse and one unit
  later. No gain changes and the recovery rate stays at `2/25`.

In both cases the cell is READY again 23 units after the pulse.

`native_stop_training_of_target` chains these over a train of pulses at
least 24 units apart. Suppose `n` doses bring the gain of the port into
`[9/5, 21/10]`. Then for any train of at least `n` pulses, the first `n`
are silent, every later one makes the cell fire, and the final log-gain
is the start value plus `3/5 * n`. The other gains and the recovery rate
are unchanged, and the number of FIREs is the number of pulses minus `n`.

The number `n` is not fixed by the protocol. It depends on the start
gain, and two cells that need different numbers of doses end in the same
band `[9/5, 21/10]` after the same pulse train.

Scope:

- **Covered start gains.** A start gain `g` is covered when `g * exp(3n/5)`
  lies in `[9/5, 21/10]` for some `n`. That is a band of width about 0.15
  in log-gain out of each period of 0.6. The other start gains pass
  through gains between `7/6` and `9/5`, where no existing construction
  applies. The firing limit, about 1.61, lies in that gap.
- **Nominal thresholds and the nominal dose.** The FIRE threshold is 1.
  Small doses and inexact thresholds are not covered.
- **One port.** The joint read of two trained ports is proved for the
  read equation only, in `StopLearningLatency.lean`.

The [specification](STOP_LEARNING_SPEC.md) states the regime and the
theorems that remain for every start gain to be covered with small doses.

### A silent training step for any gain

[SilentStep.lean](SilentStep.lean) proves the first of those theorems,
`silent_step_exists`, in the parameterized semantics. The ERROR entry
threshold of the trained port lies between 7/100 and 2/25. SILENT then
lasts longer than the pulse for every cell of either fabrication box
(`low_entry_silent_duration`), so the write starts with no input current
left.

The start state is any `RestState`: main charge within `10⁻⁴` above 0.1,
sensors in their rest band, gains under their caps, any admissible
recovery rate and energy reserve. The hypotheses on the pulse are:

- the main charge stays below the realized FIRE level, between 19/20 and
  21/20, for the whole pulse;
- the gain after one dose stays at most 7/2.

No gain band is assumed. The conclusion is an execution that ends in a
`RestState` at any chosen date at least 22 units after the pulse. The
log-gain of the pulsed port has moved by exactly `8 × (entry − exit)`.
The other gains and the recovery rate are unchanged.

The main charge may exceed 1 during the pulse when the realized FIRE
level is above 1. The flows are therefore built directly with realized
guards (`silent_leg_of_margin`, `quietDynamics`) and do not go through
the nominal kernel.

The agreement of every complete run with the construction is stated
once, for the whole training, in `TrainingLoop.lean`.

### The refractory period for any order of events

[Refractory.lean](Refractory.lean) treats the cell after a FIRE. While
the main cell is in FAST or SLOW and no sensor is in MARK, the main
charge and each sensor evolve on their own: the input current reaches
neither, no gain is written and the recovery rate is constant.
`refractoryDynamics` is the explicit flow of that regime, for any number
of busy sensors.

`refractory_run_exists` turns it into an execution of the parameterized
semantics. From a refractory state it runs to the reopening of the main
cell. The pending events are the end of FAST, the ERROR entry and exit
of each busy sensor and the end of each live pulse. They are taken in
their time order by induction on their number, so no order and no tie
between them is assumed. The hypotheses are:

- each threshold is positive and below the one that precedes it;
- every busy sensor is READY again, and every pulse has ended, before
  the main cell reopens;
- a pulse ends before its sensor reopens.

The conclusion gives the reopening date, the main charge at its reopen
threshold, every sensor READY on an explicit relaxation, and unchanged
gains, recovery rate and queue.

The theorem is the common tail of the firing training step and of a read
on several ports.

### A firing training step

[FiringStep.lean](FiringStep.lean) proves `firing_step_exists`, in the
same regime and from the same `RestState` as the silent step. The
hypothesis is the negation of the silent one: at some time of the pulse
the main charge of the rested cell reaches the realized FIRE level. The
recovery rate lies between 7/100 and 1/10.

The construction takes the first contact with the FIRE level, which
happens while the pulsed sensor is SILENT, fires there, and hands the
state to `refractory_run_exists`. The ERROR phase of the sensor then
falls inside the refractory period, whatever its order with the end of
FAST. The conclusion is an execution that ends in a `RestState` at any
chosen date at least 22 units after the pulse, with every gain and the
recovery rate unchanged and the main charge exactly at 1/10.

Together the two steps cover every pulse on a rested cell: it either
stays below the FIRE level and writes one dose, or reaches it and writes
nothing. Neither theorem assumes a gain band.

The run has exactly one FIRE event. The silent step and the refractory
period have none. Each construction carries its count (`Runs`).

### The training loop, for every start gain

[TrainingLoop.lean](TrainingLoop.lean) chains the two steps over a train
of pulses on one port, at least 22 units apart.

- `training_step_exists` joins the two steps. No hypothesis on the gain
  remains: a silent pulse always leaves room for one more dose under the
  cap (`silent_room`).
- `training_loop_exists` builds the execution through the whole train.
  Its conclusion is a `Trained` record: for each pulse, whether it was
  silent and wrote one dose, or fired and wrote nothing.
- `stop_training_exists` is the stopping rule. If `r` doses bring the
  start gain to a value that always fires, and the train has at least
  `2 r + 2` pulses, then the final gain fires from the exact rest charge
  1/10, and it equals the start gain times `exp(k × dose)` for some `k`
  at most the number of pulses. Unless no dose was written, the gain one
  dose below the final one was silent from a rest charge within `10⁻⁴`
  above 1/10.

The factor 2 has a physical cause. A pulse may fire only thanks to the
residual rest charge left by the previous silent pulse. The next pulse
starts from the exact rest charge and may then be silent once more.
After a FIRE from the exact rest charge, every later pulse fires
(`Trained.stable`).

Every run agrees with the constructed one. `rest_run_unique` applies
the uniqueness theorem of the parameterized semantics: any run from the
same rested start that is complete through the horizon ends in the same
state, with the same number of FIRE events. `stop_training_exists`
includes that statement, and each pulse is either one of its `k` doses
or one of its `f` FIRE events.

### Two ports of one cell

The thresholds are no longer required to equal a single-port
configuration. `PortConfig θ p upper lower level` states what a pulse on
port `p` needs: nominal main, MARK and SILENT levels, the realized FIRE
level, and the two ERROR levels of port `p`. The other ports keep any
ordered ERROR levels, so one cell satisfies it for several ports, each
with its own dose. `PortConfig.of_training` recovers the single-port
configuration of the earlier modules.

`two_port_training_exists` trains two ports one after the other in one
execution. The second train waits in the queue during the first. Both
final gains fire from the exact rest charge, each is at most one dose
above a silent gain unless no dose was written on it, and every complete
run agrees with the constructed one.

### The driven period before a FIRE

[Driven.lean](Driven.lean) is the counterpart of `Refractory.lean` for
the time before a FIRE. While the main cell is READY and no sensor is in
ERROR, no gain is written. The main charge follows the sum of the live
pulses weighted by their gains, and each sensor follows its own pulse or
its own decay. `drivenDynamics` is that explicit flow for any number of
live pulses.

A `Plan` states what holds up to a horizon: the main charge stays below
the FIRE level, the live pulses last, no delivery is due, and a SILENT
sensor stays above its ERROR entry threshold. Two theorems run it.

- `driven_until_exists` runs to a date at which sensors may still be on
  their way. The plan holds again there, so a new pulse can be admitted.
- `driven_run_exists` runs to a horizon by which every busy sensor is
  SILENT.

In both, the MARK and SILENT entries of the sensors are taken in their
time order by induction. Two pulses on two ports need no assumption on
which sensor moves first.

### The read of two ports, and training and read in one execution

[JointRead.lean](JointRead.lean) reads two ports. The second read pulse
arrives up to a quarter of a unit after the first, or at the same
instant.

- `fire_rest_exists` is the FIRE and the return to rest with any number
  of SILENT sensors. It uses `refractory_run_exists`.
- `staggered_read_exists`: if the first pulse alone stays below the FIRE
  level until the second arrives, and the two together reach it later,
  the cell fires exactly once, at the first contact, and returns to rest
  with every gain unchanged. The date of the FIRE is part of the
  statement (`Emits`).
- `stopped_staggered_read`: when each gain fires alone from the exact
  rest charge and was silent one dose below, with doses of at most 1/20,
  the FIRE comes later than 0.239 units after the first read pulse and
  no later than 0.256 units after the second. Every complete run fires
  at that same date.
- `trained_read_exists` is the whole experiment in one execution. Two
  ports start from gains that do not fire. Each is trained by its own
  train of pulses until it stops by itself, then one pulse on each port
  reads the cell. The read FIRE lies in the same window, whatever the
  start gains and the FIRE level between 19/20 and 21/20. Every complete
  run has the same FIRE dates and the same end state.

### The coincidence decision of two trained cells

[TrainedCoincidence.lean](TrainedCoincidence.lean) restates the network
contract of `CoincidenceNetworkContract` with trained cells.

- `TrainedCell` gathers the hypotheses on one cell: its parameters in
  the fabrication box, its thresholds, its rested start, its two pulse
  trains and its two read pulses.
- `trained_coincidence_network`: two such cells form a two-cell network.
  Each has its own parameters, its own start gains and its own FIRE
  level. The right cell is read 0.3 units before, at the same date as, or
  0.3 units after the left one, and within each cell the second read
  pulse is at most 1/10 after the first. In every complete run of the
  network, each cell's last FIRE is its read FIRE, and the two dates are
  closer than 3/20 exactly when the two cells are read at the same date.
- `trainedCell_witness` and `trained_coincidence_witness`: an explicit
  cell and an explicit schedule satisfy every hypothesis. The cell is
  nominal with ERROR thresholds 2/25 and 59/800, start gains 6/5 and two
  trains of 22 pulses. The contract is therefore not vacuous.

This replaces the two hand-set hypotheses of the earlier coincidence
result, an exact birth gain and a FIRE level within 3%, by a training
rule that absorbs both. The earlier result also showed that no setting
of a constant-current timer meets the same receiver contract at its
registered corner. That comparison is not redone here.

Limits of these statements:

- **Order of the read pulses.** In each cell the pulse on the first
  trained port arrives no later than the pulse on the second, by at most
  a quarter of a unit, and by at most 1/10 for the network decision.
- **Doses of at most 1/20 for the window.** The training theorems hold
  for any dose up to 3/5. The window constants are for doses up to 1/20.
- **Recovery rate between 7/100 and 1/10**, sensors within `10⁻⁵` of
  their rest charge, pulses at least 22 units apart.
- **Two independent cells.** The network has no wire between the cells.
  The receiver that compares the two FIRE dates is outside the model.
- **Circuit quantities.** Gain mismatch and FIRE level are covered. The
  pulse amplitude, the unit response and the thresholds other than FIRE
  and the two ERROR levels are those of the model.
### A count probe that calibrates itself

[SelfCalibratedProbe.lean](SelfCalibratedProbe.lean) links the training
loop to the count probe of the search results.

In `threshold_count_probe_crossing` a hidden need `m` is encoded in an
exact birth log-gain, `−0.6 (m − 1)`, with the nominal dose 0.6. Here
the need is a property of the cell. `NeedIs level dose z₀ m` says that
the port needs `m` doses before a pulse makes the cell fire: below `m`
doses no pulse fires, from `m` doses on every pulse fires, for any rest
charge within `10⁻⁴` above 1/10. `needIs_of_peaks` derives it from two
inequalities on the gain ladder. The start gains it excludes are those
within `10⁻⁴` of a firing boundary.

- `Trained.counts`: with a known need, a train of `n` pulses writes
  exactly `min n m` doses, and every other pulse fires.
- `self_calibrated_probe_exists`: a port receives `n` training pulses
  and then one read pulse. The read pulse makes the cell fire exactly
  when `m ≤ n`. The start gain is any real number with that need, the
  dose is the one its two ERROR thresholds give, and the FIRE level lies
  between 19/20 and 21/20. Every complete run has the same end state and
  the same number of FIRE events.

This is the comparison that each pivot of the binary search performs,
without a birth gain on a lattice. It is proved for one cell with no
outgoing wire, in the parameterized semantics. The compiled decision
tree of `CalibratedDecisionTree.lean` is a routed network in the nominal
semantics, and it still uses the earlier probe. Replacing its probe needs
the training steps with a router and a routed composition in the
parameterized semantics. Neither exists yet.
### Networks of any number of trained cells

[FamilyProduct.lean](FamilyProduct.lean) removes the limit of two cells.

The earlier product, `ParameterExecution.independentPair`, weaves two
one-cell executions. Here `Snapshot.family` is the state of a network of
`n` cells, each with its own parameters, and `family_execution` weaves
`n` one-cell executions with common start and end dates into one
execution of that network. Each cell keeps its ordered FIRE dates. The
proof takes the next jump of any cell when there is one, and otherwise
cuts every flow at the earliest flow end. `family_jump` lifts each of the
nine kinds of jump to the network.

- `trained_network`: for any positive `n`, `n` trained cells with their
  own parameters, start gains, FIRE levels, pulse trains and read dates.
  In every complete run of the network, the last FIRE of each cell is
  its read FIRE, later than 0.239 units after its first read pulse and
  no later than 0.256 units after its second. For any two cells read
  with an offset of −0.3, 0 or +0.3 units, the two dates are closer than
  3/20 exactly when the offset is zero.
- `trained_network_witness`: for any positive `n`, `n` copies of the
  explicit cell satisfy the hypotheses. Every cell fires its read in its
  window and any two cells are accepted together.

In this module the cells are independent: no cell sends a pulse to
another. The next modules add wires.

### Wires between cells

[RoutedProduct.lean](RoutedProduct.lean) composes cells joined by wires,
in the parameterized semantics.

Each cell keeps a one-cell run with an empty router. In that run its
queue already holds the pulses that other cells will send it. In the
network a pulse enters the queue only at the FIRE that sends it.
`routed_execution` weaves the one-cell runs into one run of the routed
network. Its hypotheses are:

- every wire has a strictly positive delay;
- the queues balance at the start: the queues of the cells are the queue
  of the network plus what the FIRE dates of the cells will send.

The proof keeps that balance as a multiset equation through every move.
A FIRE moves its deliveries from the promised side to the queue. An
arrival finds its delivery in the queue, because every delivery still
promised is due later. Each cell keeps its ordered FIRE dates. The one-
cell theorems of the earlier modules are used unchanged.

### Read pulses in either order

[FreeRead.lean](FreeRead.lean) separates the training of a cell from its
read.

- `rest_wait`: a cell at rest stays at rest for as long as no pulse
  arrives. No gain moves.
- `OpenCell`: a trained cell without its read pulses. Its hypotheses are
  those of `TrainedCell` without the read dates. After `horizon` the
  cell is trained and at rest.
- `OpenCell.read`: two read pulses arrive after `horizon`, one on each
  trained port, at most a quarter of a unit apart, **in either order**.
  The cell fires its read later than 0.239 units after the first pulse
  and no later than 0.256 units after the second. Every FIRE of training
  comes before `horizon`, which is a fixed date.

### Composition along forward wires

[AcyclicNetwork.lean](AcyclicNetwork.lean) proves one composition theorem
for every network whose wires go from a cell to a cell of higher index.

`acyclic_network` takes, for each cell, a description of its FIRE dates
that may mention the FIRE dates of the cells before it. Its hypothesis is
local: a cell fed by cells that follow their descriptions has a run to
rest that follows its own. The pulses it receives are computed from the
router by `incoming`. The conclusion is global: the network has a
complete run, every cell follows its description, and the FIRE dates are
the same in every complete run. The cells are treated one after the
other, in index order, and `routed_execution` weaves their runs.

### Networks of trained cells of any depth

[WiredNetwork.lean](WiredNetwork.lean) applies the composition theorem to
trained cells.

- `ReadInput`: each of the two read pulses of a cell comes from a source
  at a fixed date, or from the read FIRE of an earlier cell through a
  wire with a positive delay.
- `trained_wired_network`: any number of cells, any wiring of that kind.
  The hypothesis `admissible` says that, whenever the earlier cells fire
  their reads in their windows, the two read pulses of a cell arrive
  after its training and at most a quarter of a unit apart. Their order
  is free. In every complete run, each cell fires its read later than
  0.239 units after its first read pulse and no later than 0.256 units
  after its second, after the FIRE events of its own training.
- `trained_chain_witness`: for every `n`, a chain of `n` copies of the
  explicit cell. A source reads the first cell at date 968. The read
  FIRE of each cell reads the two ports of the next one, one unit later.
  In every complete run, each cell fires its read between 1.239 and
  1.256 units after the cell before it.

Limits:

- **Width of the windows.** The theorem bounds each read FIRE inside a
  window of 0.017 units plus the distance between the two arrivals. On a
  path where the two ports of a cell are fed by different cells, the
  windows widen with the depth, and the hypothesis `admissible` needs
  them to stay within a quarter of a unit. In the chain both ports of a
  cell are fed by the same FIRE, so the depth is free.
- **Gates.** Each wire carries the FIRE events after a fixed date only.
  That date is the end of the training of the sending cell.
- **Every read pulse arrives.** A cell that may or may not receive a
  read pulse is not covered by `trained_wired_network`. The next modules
  cover it.

### Report windows in the parameterized semantics

[SignalNetwork.lean](SignalNetwork.lean) is the parameterized counterpart
of the report windows of the scheduled circuits.

Each cell has a window `(lo, hi]`. A FIRE in the window is a signal. A
signal sends pulses at fixed dates to later cells, as a `ReportWire`
does in the nominal circuits. `Signal lo hi l b` says that the FIRE dates
`l` carry the bit `b`: for a true bit the last FIRE is in the window and
the others are before it, for a false bit every FIRE is before the
window.

`signal_network` takes a bit for each cell. Its hypothesis is local: a
cell that receives the pulses of the wires whose senders have a true bit
has a run to rest that carries its own bit. The conclusion is a complete
run of the network in which every cell carries its bit, with the same
FIRE dates in every complete run. A cell may receive all, some or none
of its pulses.

### The two cells of a search

[SearchCells.lean](SearchCells.lean) describes two cells alone.

- `ProbeCell.asked`: a probe cell receives a train of pulses and a read
  pulse. It fires on the read pulse exactly when its hidden need is at
  most the number of training pulses. That FIRE comes within one unit
  after the read pulse, and every FIRE of training comes more than one
  unit before it. `ProbeCell.idle`: a probe that receives nothing never
  fires.
- `OpenCell.read_one`: a trained cell read by one pulse fires later than
  0.355 units after it. Read by two pulses it fires before 0.256 units
  (`OpenCell.read`). The date of the FIRE therefore tells whether the
  second pulse was there. This is how the silence of a probe becomes a
  FIRE: the gate cell is read by a clock pulse, and by the report of the
  probe when there is one. Its late FIRE means that the probe was
  silent.

Two earlier theorems are refined for this. `firing_step_dated` in
[FiringStep.lean](FiringStep.lean) gives the date of the FIRE of a firing
step: the first date at which the pulse response reaches the FIRE level.
`window_alone` in [StopLearningLatency.lean](StopLearningLatency.lean)
bounds the response at 0.355 units below `exp(-1/20)` times its peak.

### A search by questions with trained cells

[TrainedSearch.lean](TrainedSearch.lean) builds a decision tree on the
composition theorem, with trained cells only.

Each node asks one question: is the hidden need `m` at most the number
of training pulses of this node? A node has a probe cell and a gate
cell. A `SearchLayout` gives the parent of each node with the answer
that leads to it, the dates of each question and the order of the
cells. The questions of the roots are started by sources. A yes is a
FIRE of the probe in its report window. A no is a late FIRE of the gate.
Each answer sends the pulses of the questions it leads to.

- `trained_search`: any number of nodes, any forest. Every probe has
  its own need, parameters, start gain, dose and FIRE level. Every gate
  is trained by its own pulse trains before its clock pulse. The network
  has a complete run, and in every complete run:
  - the probe of a node fires in its report window exactly when the
    node is reached and its need is at most its count;
  - the gate of a node fires late exactly when the node is reached and
    its need is larger than its count;
  - the probe of a node that is not reached never fires;
  - the gain of a probe ends one dose higher for each pulse of its
    question, up to its need, when its node is reached, and unchanged
    otherwise;
  - the pulses sent to the probe of a child are its question when the
    child is reached, and none otherwise.

  The FIRE dates and the final values are the same in every complete
  run. A search for one hidden need `m` is the case where every probe
  has the need `m`.
- `searchWitness`: a layout with three questions over the needs 1 to
  4. The root asks `m ≤ 2`. After a yes, node 1 asks `m ≤ 1`. After a
  no, node 2 asks `m ≤ 3`. The two answers separate 1, 2, 3 and 4 or
  more. Its explicit cells are in `NeedTolerance` below.

No gain and no FIRE level is set by hand in this search. The need is the
number of doses that each probe's own gain, dose and FIRE level require
(`NeedIs`). The gates are trained by stop-learning.

Limits:

- **Fixed dates.** A signal releases pulses at preset dates, as the
  report wires of the nominal circuits do. A FIRE date is read only
  through its window. A delay line that would keep the jitter of the
  FIRE is not used.
- **One need for all probes.** Each probe is a separate cell. The
  hypothesis gives them the same need `m`. The next module derives it
  from fabrication tolerances.
- **The gates are trained in advance,** whatever the need. Only the
  probes are trained on demand: a probe that is not reached receives no
  pulse.
- **Lessons at the leaves** are treated in `SearchActions` below. The
  credit of the nominal decision tree of `CalibratedDecisionTree` is not
  rebuilt.
- **The witness has two levels.** `trained_search` covers any depth.
  `BisectionSearch` below builds a layout of every depth.

### The need of a probe, from fabrication tolerances

[NeedTolerance.lean](NeedTolerance.lean) replaces the hypothesis of a
common need by a tolerance on each probe.

A nominal design has a FIRE level `level₀` and a dose `d₀`. The start
gains that need exactly `m` doses form a band, one dose wide.
`needCentre level₀ d₀ m` is its centre.

- `needIs_of_tolerance`: a real probe has its start log-gain within `a`
  of that centre, its dose within `b` of `d₀` and its FIRE level within
  `ℓ` of `level₀`. If

  ```text
  a + m * b + 20/17 * ℓ + 1/8000 < d₀ / 2
  ```

  then the probe needs exactly `m` doses. Probes that satisfy this for
  the same `m` have the same need, whatever their own gains, doses and
  FIRE levels.
- `trained_search_band_witness`: the layout `searchWitness`, with
  each of the three probes at its own start gain, anywhere within 3/125
  of the centre of the band. The dose is 1/20, so the band is used on
  96% of its width.

The error on the dose is multiplied by `m`: each dose adds its own
error before the read. With a perfect start gain and FIRE level, needs
up to `M` are separated when `M * b + 1/8000 < d₀ / 2`. For a dose of
1/20 known to 1%, that is needs up to 49. The term `1/8000` covers the
residual rest charge.

Limits:

- **A sufficient condition.** The inequality is not shown to be
  necessary.
- **The same error at every dose.** The dose of a probe is one number.
  A dose that drifts from pulse to pulse is not covered.
- **The witness varies the start gains only.** Its doses and FIRE
  levels are those of the explicit cell.

### A search that ends by a lesson

[SearchActions.lean](SearchActions.lean) adds an action to the binary
search. The composition theorems now also give the final state of each
cell (`acyclic_network_states`, `signal_network_states`) and the pulses
that the FIRE events of a run send to each cell.

A lesson is a node like the others: its probe is the learner, and its
question is the lesson. `actionSearch` has seven nodes and fourteen
cells. Nodes 0 to 2 are the three questions. Node `m + 2` is reached
exactly when the need is `m`, and its lesson has `m + 1` pulses.

`search_action_witness`: every probe has its own start gain, anywhere
within 3/125 of the centre of the band of need `m`. For every need `m`
from 1 to 4, in every complete run:

- the learner of node `m + 2` receives `m + 1` pulses. Its gain ends
  exactly `m` doses higher, which is its firing gain, and its last pulse
  makes it fire in its report window;
- the three other learners receive no pulse from the network, keep their
  gain and never fire.

The search therefore spends on the learners only the lesson of the need
it found.

Limits:

- **Pulses are counted per learner.** The pulses of the sources, of the
  questions and of the training of the gates are not added into one
  cost.
- **One pulse more than the need.** The last pulse of the lesson writes
  nothing and fires. A lesson of exactly `m` pulses would leave the
  learner at its firing gain without a FIRE.
- **Each lesson node has a gate** that is trained and not used.
- **Four needs.** The witness has three questions and four lessons.
  The search of every depth below has no lesson at its leaves.

### A binary search of every depth

[BisectionSearch.lean](BisectionSearch.lean) builds, for every `k ≥ 1`,
a complete tree of `2 ^ k - 1` questions that separates the needs 1 to
`2 ^ k`, with `2 (2 ^ k - 1)` cells.

- `heapSearch`: the nodes are numbered as in a heap. The children of
  node `i` are `2 i + 1` after a yes and `2 i + 2` after a no. Cell
  `2 ν` is the probe of node `ν` and cell `2 ν + 1` is its gate.
  `heapSearch_sound` reduces the soundness of the layout to its dates.
- `exOf`, `loOf`, `midOf`: node `i` has the interval of needs
  `(loOf k i, loOf k i + 2 ^ exOf k i]`. Its question counts `midOf k i`
  pulses, the middle of the interval. A yes keeps the lower half and a
  no keeps the upper half (`bisect_child`).
- `bisectPlan`: the nodes of one depth share their dates. A depth lasts
  `22 * 2 ^ k + 26` units, enough for the longest question.
- `bisection_search`: every probe has the need `m`, between 1 and
  `2 ^ k`, with its own parameters. In every complete run the probe of a
  node fires in its report window exactly when `m` lies in the lower
  half of its interval, and its gate fires late exactly when `m` lies in
  the upper half. A probe outside the path `bisectPath k m` receives no
  question: it never fires and its gain does not move.
- `bisect_reached_iff`: the nodes whose interval holds `m` are the `k`
  nodes of the path, one at each depth. The run therefore asks `k`
  questions out of `2 ^ k - 1`.
- `bisect_last`: the node asked at depth `k - 1` has an interval of two
  needs. Its probe answers yes exactly for the first and its gate
  answers no exactly for the second. The last answer gives `m`.
- `bisection_search_witness`: explicit cells for every `k`, each probe
  at its own start gain inside the band of need `m`.

This tree has one probe and one gate for each node, and its run lasts
`k (22 * 2 ^ k + 26)` units. The next module keeps the same questions
with one probe and one gate for each depth.

### A binary search by successive approximation

[SuccessiveSearch.lean](SuccessiveSearch.lean) builds the search of
depth `k` with `2 k + 1` cells: a probe and a gate for each depth below
`k`, and the learner.

The weight of depth `t` is `2 ^ (k - 1 - t)`. The probe of depth `t` has
its own block of that many pulses, from sources. Each earlier gate that
answered no sends a block of its own weight. The count of the question
of depth `t` is therefore the middle of the interval that remains
(`probeDates_count`), and the probe answers yes exactly when the need is
at most that count. No question has to be selected: only its count
changes.

A block sent by a gate goes to all the later probes at the same dates,
and the own blocks of all the probes are sent together at the start.
`probeDates_spaced` shows that the pulses of each probe stay 22 units
apart, whatever the answers.

- `successive_search`: every probe has the need `m`, with its own
  parameters, start gain, dose and FIRE level. Every gate is trained
  before the date 1000. In every complete run the probe of depth `t`
  fires in its report window exactly when `m` is at most its count, the
  gate of depth `t` fires late exactly when `m` is above it, and the
  gain of each probe ends one dose higher for each pulse of its
  question, up to its need.
- `successive_digits`: for `1 ≤ m ≤ 2 ^ k`, the weights of the gates
  that fire late add up to `m - 1`. The gates give the binary digits of
  `m - 1`.
- `approx_learner`: the last stage has the weight 1. Its question counts
  exactly `m` training pulses. It is the learner: its gain ends exactly
  `m` doses higher and its read pulse makes it fire.
- `approx_cost`: the counts of the `k` questions add up to at most
  `k (m - 1) + 2 ^ k - 1`.
- `approx_duration`: the run ends at the date `1003 + 33 * 2 ^ k + 25 k`.
- `successive_search_witness`: explicit cells for every `k ≥ 1`. Each
  probe has its own start gain, within 1/100 of the centre of the band
  of need `m`, and its own ERROR thresholds, hence its own dose, within
  `1 / (100 * 2 ^ k)` of 1/20. The dose error allowed shrinks as
  `2 ^ -k`, as `needIs_of_tolerance` requires.

Compared with the tree of the previous section, for the same `2 ^ k`
needs:

```text
                    tree of BisectionSearch     successive approximation
cells               2 (2^k - 1)                 2 k + 1
end of the run      1000 + k (22 * 2^k + 26)    1003 + 33 * 2^k + 25 k
lesson              none                        the last stage
```

Limits:

- **Duration.** One question of count `c` takes `22 c` units, and the
  first question has `2 ^ (k - 1)` pulses. The run cannot be shorter
  than `22 * 2 ^ (k - 1)` units with these probes. It lasts about three
  times that.
- **Wires.** A gate of weight `w` has `w` wires to each later probe. The
  network has few cells and many wires.
- **Every probe is asked.** No pulse is saved by the answers: each
  question is sent, with a count that depends on them.
- **The gates are trained in advance.** There are `k` of them.
- **Dose precision.** Separating `2 ^ k` needs asks for a dose error
  below about `d₀ / 2 ^ (k + 1)`. This is a property of the probes, not
  of the network.

### A lag between a pulse and its effect

[ReadLag.lean](ReadLag.lean) treats one departure of a circuit from the
model. The element that applies a gain takes a short time to settle, so
a pulse acts on the main charge a little after it arrives. A lag that is
the same for every pulse of a cell shifts every FIRE date of that cell
by that lag, and changes nothing else.

- `trained_dates_decide_lag`: the two read FIRE dates of the coincidence
  decision are observed later than the model gives them, each by the lag
  of its cell. If the two lags differ by at most 3/100 of a unit, the
  observed dates are closer than 3/20 exactly when the two cells are
  read at the same date.
- `trained_network_lag`: the same for any number of trained cells, each
  with its own lag, in every complete run.

In the wired networks and the searches a common lag adds to the delay of
each wire, which those theorems already leave free.

Limits:

- **One lag per cell.** A lag that depends on the pulse, on the port or
  on the slope of the charge is not covered.
- **A statement on dates.** The lag is applied to the FIRE dates of the
  model. A semantics in which a pulse acts late is not constructed.

## Common threshold offset and reaction delay

[OffsetAndDelay.lean](OffsetAndDelay.lean) refines the one-pulse training
theorem in two ways. Both use the parameterized first-contact semantics
and the sixteen-unit schedule. The FIRE threshold lies in `[0.95, 1.05]`,
the trained port's birth gain in `[7/6, 1.2]`, the other guards are
nominal, and both fabrication boxes are covered.

**A common shift cancels.** Write the realized ERROR entry as
`0.1 + δ + a` and the exit as `0.025 + δ + b`. With `|δ| ≤ 0.004` and
`|a|, |b| ≤ 0.001`, `training_read_common_offset` gives a complete run,
and in every complete run the log-gain increment is `0.6 + 8 * (a - b)`.
The common shift `δ` does not appear. It may reach 4% of the entry level
and 16% of the exit level. With `a = b = 0`,
`training_read_pure_common_offset` gives exactly `0.6` for `|δ| ≤ 0.005`.

The earlier theorems bound each endpoint separately. This one separates
the part of the error that the two endpoints share from the part they do
not. Only the second part changes the dose. A cell that detects both
endpoints with one comparator has mostly shared error.

**A reaction delay bounds the dose.** Suppose the cell reacts a fixed
time `d` after each ERROR endpoint crossing. The sensor keeps decaying
during that time, at the SILENT rate `ls` before the entry and at the
ERROR rate `le` before the exit. The realized endpoints are then
`0.1 * exp(-ls * d)` and `0.025 * exp(-le * d)`. For `0 ≤ d ≤ 0.01`,
`training_read_reaction_delay` gives a complete run, and in every
complete run the increment `Δz` satisfies

```text
-0.8 * ls * d  ≤  Δz - 0.6  ≤  0.2 * le * d        and        |Δz - 0.6| ≤ 2.4 * d
```

The exact increment is `8 * (0.1 * exp(-ls * d) - 0.025 * exp(-le * d))`.
With a reaction delay the dose depends on the discharge rates, and the
dependence vanishes linearly with `d`. The nominal ERROR phase lasts 0.15
model units, so `d = 0.01` is about 7% of it.

The delay is represented through the realized thresholds.
`delayedLevel_of_decay` shows that an exponential decay which meets a
level reaches `level * exp(-rate * d)` after a further time `d`. The
semantics still jumps at guard equality. A semantics with delayed jumps
is not constructed, and the delay is the same at both endpoints and
fixed in time.

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
`BlindNeedSearch`, `ThresholdProbe`, the coincidence modules
through `CoincidenceSeparation`, `StopLearningLatency`,
`NativeStopLearning`, `SilentStep`, `Refractory`, `FiringStep`,
`TrainingLoop`, `Driven`, `JointRead`, `TrainedCoincidence`,
`OffsetAndDelay`, `SelfCalibratedProbe`, `FamilyProduct`, `RoutedProduct`,
`FreeRead`, `AcyclicNetwork`, `WiredNetwork`, `SignalNetwork`,
`SearchCells`, `TrainedSearch`, `NeedTolerance`, `SearchActions`,
`BisectionSearch`, `SuccessiveSearch` and `ReadLag`. The default targets
also run
[the axiom audit](NativeAudit.lean), which checks all imported declarations
under `RecursiveLearning`, including private ones.
Unexpected axioms and admitted proofs fail the build. The underlying R imports
and Mathlib pins come from the existing proof package.
