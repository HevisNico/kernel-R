# Notes for PREDICTION.md: the either cell's two arrivals (addition F, 2026-11-24)

**Draft, nothing frozen.** CAMPAIGN_PLAN_DRAFT.md and PLAN_NOTES_3.md are pushed and not modified.

## The difference

- **In stage D** (stage_d4.py / stage_d5.py), a cell's mask read of (1, 2) gives both ports their pulse at the same
  date: offset 0 (stage_d.StageDNetwork.drive).
- **In the network**, the two inputs of a layer-2 either cell come from two layer-1 cells. These emit at their own
  latencies after the read start, so the two arrivals at the either cell can differ.
  - **Design bound:** up to the layer's skew, w + dmax_design = 0.2 + 1.2 = 1.4 tu (config.json `timing`,
    spec.timing).
  - **Figure given by the coordinator's review:** about 0.7 tu. It is not checked here.
  - **Measured:** 0.14 tu. This is the one network read of an either cell with both inputs in the development records:
    ANDOR3 9805 (dev/dryrun_b, N0, pattern 111). NOT1 and XOR3 never present both inputs to an either cell.

## What it touches

- **Only the either cell's two-input read** is affected: the FiringSlot read of (1, 2), checked in stage D for
  monotonicity and for its single-port anchors.
- The single-port reads, which give the anchors, the budgets and the words, have one arrival each.
- **The model** (scores.score) gives a score that does not depend on the arrival offset inside the read window.
- **That this holds** for offsets up to the skew is part of the open premise "the routed walk" (plan §9). It is
  assumed, not proved.

## Stated in advance

- If a run refutes on a pattern that presents both inputs to an either cell, the arrival offset is the second suspect,
  after the two-port read itself (PLAN_NOTES_3.md (b)).
- The report gives the measured offset of every such read.
- It changes no verdict: a refutation refutes.
- An offset scan of the either cell's (1, 2) read in stage D, at the measured network offsets as the
  both-cell scans do, is possible. It is not part of the frozen stage D unless the owner adds it before the freeze.
