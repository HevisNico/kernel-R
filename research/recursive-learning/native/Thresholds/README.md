# Realized thresholds and adaptive rounds

[Back to the native package](../README.md)

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

[HybridParameterExecution.lean](../../../../proof/lean/KernelR/HybridParameterExecution.lean)
uses the fixed charge guards stored in each cell's `Parameters`. The
continuous equations, pulse origin and queue rules are shared with the
nominal kernel. Flows and completion check the same realized guards as
jumps.

[ParameterTraining.lean](ParameterTraining.lean) places the two-pulse
experiment in this semantics. Lean constructs a complete run through
the read FIRE for every admissible choice in either full fabrication
box, with the three tolerances above. The other charge guards are
nominal. The experiment covers one training pulse and one read.

[HybridParameterUniversalExecution.lean](../../../../proof/lean/KernelR/HybridParameterUniversalExecution.lean)
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
