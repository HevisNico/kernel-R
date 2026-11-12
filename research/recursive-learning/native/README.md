# Native R cells: training, networks and searches

This package proves results in actual R cells, with the kernel definitions
of [`proof/lean`](../../../proof/lean/README.md) unchanged. It started as a
native memory for the [discrete teaching loop](../README.md) and now holds
training that stops by itself, the two-cell coincidence decision, networks
of trained cells and searches built from them.

> **Start here.** The [map of the stop-learning results](#map-of-the-stop-learning-results)
> names the strongest statement at each level. The
> [v0.4.0 release notes](../../../docs/RELEASE_V0_4_0.md) give the short
> version, and [STOP_LEARNING_SPEC.md](STOP_LEARNING_SPEC.md) states the
> regime.

## Layout

One Lean library, `Native`, with one folder per line of work. Each folder
has a README with the statements of its modules.

| Folder | Content | Modules |
|---|---|---|
| [`Teaching/`](Teaching/README.md) | credits and reusable selector reads in port gains, lessons, acceptance tests, report circuits | 36 |
| [`Thresholds/`](Thresholds/README.md) | adaptive rounds, decision trees, realized FIRE and ERROR thresholds, training then read of one port | 12 |
| [`Coincidence/`](Coincidence/README.md) | the v0.3.0 coincidence separation, the constant-current comparison, offset and delay | 9 |
| [`Training/`](Training/README.md) | the stop-learning regime: silent and firing steps, the training loop, the joint read, trained coincidence, lag | 10 |
| [`Network/`](Network/README.md) | products of cells, wires, forward composition, networks of any depth, report windows | 6 |
| [`Search/`](Search/README.md) | fixed and variable-dose need bounds, probe and gate cells, trees of questions, successive approximation | 8 |

These counts cover 81 Lean modules, including the three focused selector
audits in `Teaching`. [`NativeAudit.lean`](NativeAudit.lean) imports every
module, directly or transitively, and runs the axiom audit. Its current scope
is 83 modules including the two parent `RecursiveLearning` modules:
6,306 declarations, of which 3,882 are theorems.

The modules are named by folder: `import Training.SilentStep`.

## Selector reuse and variable doses

These additions have their own hypotheses; they do not extend the compiled
search networks or the stop-learning regime below automatically.

| Result | Main theorem | Scope |
|---|---|---|
| reusable selector read | [`calendar_rounds_exists`](Teaching/SelectorRounds.lean) | fixed period 32, every finite round count and admissible delay function; preserved gains and recovery, exactly `3n` deliveries |
| first read plus reusable rounds | [`delivered_calendar_program_exists`](Teaching/SelectorRoundBootstrap.lean) | first read is an actual charged delivery: `3n+1` deliveries and `2n+1` FIREs; every complete run has the same final state and FIRE dates |
| variable-dose scalar need | [`needAlong_of_variable_doses`](Search/VariableNeedTolerance.lean) | nonnegative, independently varying doses with a per-step error budget |
| cumulative scalar need | [`needAlong_of_cumulative_tolerance`](Search/VariableNeedTolerance.lean) | a cumulative gain budget through the target count, with gain bounded below by its target-count value afterwards |

The [Teaching map](Teaching/README.md#reusing-the-selector-with-a-fixed-calendar)
states the prepared resources and external-calendar limit. The
[Search map](Search/README.md#variable-doses-and-cumulative-gain-error) states
the scalar tolerance budget and its separation from native execution proofs.

## Map of the stop-learning results

The [Training](Training/README.md), [Network](Network/README.md) and
[Search](Search/README.md) pages form one line of work: training that
stops by itself, from one pulse to networks and searches. No gain and no
FIRE level is set by hand in it. This map lists the strongest statement
at each level. Those pages follow the order in which the theorems were
proved, so some of their sections state an earlier and weaker form.

| Level | Statement | Theorem | File |
|---|---|---|---|
| one pulse | a silent pulse writes one dose, a firing pulse writes nothing and its date is known | `silent_step_exists`, `firing_step_dated` | [`SilentStep`](Training/SilentStep.lean), [`FiringStep`](Training/FiringStep.lean) |
| one port | training stops by itself for every start gain | `stop_training_exists` | [`TrainingLoop`](Training/TrainingLoop.lean) |
| one port | the need of a port, and its tolerance to fabrication | `self_calibrated_probe_exists`, `needIs_of_tolerance` | [`SelfCalibratedProbe`](Search/SelfCalibratedProbe.lean), [`NeedTolerance`](Search/NeedTolerance.lean) |
| one cell | two trained ports read in either order: the FIRE comes later than 0.239 units after the first pulse and no later than 0.256 after the second | `OpenCell.read` | [`FreeRead`](Network/FreeRead.lean) |
| one cell | one read pulse fires late, two fire early | `OpenCell.read_one` | [`SearchCells`](Search/SearchCells.lean) |
| composition | cells joined by wires, from one-cell runs | `routed_execution` | [`RoutedProduct`](Network/RoutedProduct.lean) |
| composition | forward wires: complete run, unique FIRE dates and final values | `acyclic_network_states` | [`AcyclicNetwork`](Network/AcyclicNetwork.lean) |
| composition | report windows and pulses at fixed dates | `signal_network_states` | [`SignalNetwork`](Network/SignalNetwork.lean) |
| network | any number of trained cells joined by wires | `trained_wired_network` | [`WiredNetwork`](Network/WiredNetwork.lean) |
| network | the coincidence decision with a settling lag in each cell | `trained_network_lag` | [`ReadLag`](Training/ReadLag.lean) |
| search | a forest of questions, with final gains and pulses sent | `trained_search` | [`TrainedSearch`](Search/TrainedSearch.lean) |
| search | a lesson after the last answer | `search_action_witness` | [`SearchActions`](Search/SearchActions.lean) |
| search | `k` questions asked out of `2 ^ k - 1` | `bisection_search` | [`BisectionSearch`](Search/BisectionSearch.lean) |
| search | `2 k + 1` cells for `2 ^ k` needs, with the learner | `successive_search` | [`SuccessiveSearch`](Search/SuccessiveSearch.lean) |

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

## Verify

Run from the repository root with Lean 4.35.0 available:

```sh
cd research/recursive-learning/native
lake exe cache get
lake build
```

The [dedicated CI workflow](../../../.github/workflows/recursive-learning.yml)
builds this package with the pinned dependencies. The default targets are
the `Native` library, which compiles every module of the six folders, and
[the axiom audit](NativeAudit.lean). The audit checks every declaration
added by a module of this package or of the parent `RecursiveLearning`
package, whatever its namespace, private and generated declarations
included, and fails if a declaration of the `RecursiveLearning` namespace
comes from any other module. Unexpected axioms and admitted proofs fail the
build. The underlying R imports and Mathlib pins come from the existing
proof package.
