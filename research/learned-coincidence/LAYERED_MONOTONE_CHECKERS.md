# Kernel checkers for layered monotone cascades

The input is a finite cascade, one training trace, and one read trace per external mask.
Use the rational dates and integer scores of `ReadObservation`. Keep rational comparisons
exact and use a common integer scale for the scores, thresholds, and error budgets.

| Checker | Property with exact acceptance | Finite domain |
| --- | --- | --- |
| `checkLayeredValid` | `Cascade.Valid` | Layers, cells, both ports, active groups, write counts below each computed stop, four masks, and the gate's listed anchors |
| `checkLayeredSeparation` | `TrainingSeparation` | Ordered pairs of training batches and each training batch against each external test window |
| `checkLayeredTrainingCalibration` | `TrainingCalibration` | Layers, cells, active groups, and rounds through `maxWrites`, including each lesson's earlier-layer replay |
| `checkLayeredReadCalibration` | `∀ x, ReadCalibration c train x (test x)` | The full external Boolean cube, layer replays, cells, and four possible local submasks |

## Tables and executable comparisons

Reuse `PremiseCheck.patterns`, `maskIndex`, and the sized tables from the two-layer
checkers for the external masks and the two-port reference scores. Size the
training tables by the layer's nodes and their active groups and rounds. Size each
test table by the external cube and layer widths. Keep the complete list of dated
emissions in every read. A layer with zero cells or a gate with no lessons uses an
empty table in the corresponding dimension.

For validity, compute `stop` with the frozen bounded search. Check the training margins,
rails, port wiring, delay, and exact reachability of each prescribed teaching mask
under the lower-layer predictor. Compare masks pointwise over the two ports.

For separation, use `trainingBatches` in its declared order. First implement the
unrestricted pairwise comparison of all windows, including external pulse dates.
Any later use of batch extrema needs an equivalence proof that handles empty batches.

For calibration, reuse the dated decoder checks from #178. Reconstruct each write count
from the observed arrivals and silences, then compare the fixed-delay routed arrivals.
Use the symmetric residual during writing and for a predicted-silent test. For a
predicted-active test, check the observed score against each contained submask that
reaches threshold and check the lower bound on each contained anchor. This checks
the recorded reference scores and the actual observed mask at the same checkpoint.

## Proof and campaign integration

Freeze forward and reverse targets for each row in the table before proving them.
Prove local equivalences for the finite loops and atomic checks, then use induction
on the cascade. Use completeness of external mask enumeration for soundness and
the membership bounds of the finite loops for completeness. Prove the calendar
loop equivalent to `List.Pairwise BatchBefore`. Require every named soundness and
completeness theorem in the exact-type and axiom audit.

Exercise the checkers with kernel reduction on a cascade of at least three trained
layers. Include a saturated pair that passes, a routing or calendar error, a silent
read outside its residual budget, a firing anchor below its bound, and a firing
submask that scores above the observed mask. Check agreement with the independent
predictor on both accepted and rejected fixtures.

For larger instances, share computed predictors and write-count prefixes only after
proving equivalence to the direct checker. Fan-in two bounds the local submask loop
by four masks; the complete external test loop still has `2^M` rows. Measure kernel
reduction separately from loading the fixture. A campaign's gate should require a
kernel proof that each checker returns `true` before running the network.

## Measured kernel time

These are medians of three successful `decide +kernel` runs per cell of the tables.
Each run checked one closed theorem in Lean 4.35.0 on an AMD EPYC 9V74 with
`LEAN_NUM_THREADS=1`. Times are from Lean's type-checking profiler and exclude
import loading. The calibration and calendar columns exercise the complete
acceptance path.

`CheckerBench.depth` starts with the saturated AND–copy–OR trace and adds one
trained copy per layer. All cases enumerate the same 16 external masks.

| Layers | Validity | Separation | Training calibration | Test calibration | Batch order alone | External calendar alone |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 25 ms | 1.80 s | 173 ms | 262 ms | 409 ms | 1.53 s |
| 5 | 29 ms | 4.85 s | 375 ms | 382 ms | 1.11 s | 3.28 s |
| 7 | 32 ms | 8.66 s | 646 ms | 550 ms | 2.49 s | 6.39 s |

`CheckerBench.width` keeps three trained copy cells and adds unconnected
external inputs. This measures the two checks that traverse all `2^M` masks
without changing the number of trained cells. Each calendar time in this table
calls `Checker.externalSeparation` directly.

| External bits | Masks | Test calibration | External calendar |
| ---: | ---: | ---: | ---: |
| 4 | 16 | 171 ms | 351 ms |
| 6 | 64 | 803 ms | 1.66 s |
| 8 | 256 | 3.67 s | 7.48 s |

After compiling the benchmark module, the following profiles one full external
calibration check. Change the fixture or checked expression to reproduce a
different column. Calendar subchecks were timed independently of the full check.

```lean
import LayeredMonotoneCheckerBench

open LearnedCoincidence.Layered LearnedCoincidence.Layered.CheckerBench

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 0

theorem measured : let f := width 7; checkLayeredReadCalibration f.circuit f.train f.test = true :=
  by decide +kernel
```
