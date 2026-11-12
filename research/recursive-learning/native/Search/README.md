# Searches with trained cells

[Back to the native package](../README.md)

## A count probe that calibrates itself

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

## The two cells of a search

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
[FiringStep.lean](../Training/FiringStep.lean) gives the date of the FIRE of a firing
step: the first date at which the pulse response reaches the FIRE level.
`window_alone` in [StopLearningLatency.lean](../Training/StopLearningLatency.lean)
bounds the response at 0.355 units below `exp(-1/20)` times its peak.

## A search by questions with trained cells

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

## The need of a probe, from fabrication tolerances

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
- **Fixed dose in the execution constructors.** The original theorem and
  compiled search use one dose per probe. The variable-dose scalar contract
  below does not yet generalize those executions.
- **The witness varies the start gains only.** Its doses and FIRE
  levels are those of the explicit cell.

## Variable doses at successive writes

[VariableNeedTolerance.lean](VariableNeedTolerance.lean) proves
`needAlong_of_variable_doses`: the same tolerance inequality guarantees
need `m` when each nonnegative dose independently lies in `[d0-b,d0+b]`.
`NeedAlong` uses the cumulative gain sequence; on a constant-dose ladder
it is exactly `NeedIs`. `needAlong_of_step_tolerance` takes actual gain
increments and requires their budgets to include inter-window drift.

The circuit corollaries in [CircuitNeed.lean](../../../circuit/lean/CircuitNeed.lean)
use `b = k * eta` for a charge-residual bound `eta`, with exact calibration
and state linkage, or `b = k * eta + e` for an additional linkage error `e`.
These are scalar read contracts; variable-dose hybrid execution and network
composition remain separate obligations.

## A search that ends by a lesson

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

## A binary search of every depth

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

## A binary search by successive approximation

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
