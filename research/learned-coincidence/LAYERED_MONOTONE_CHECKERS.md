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
