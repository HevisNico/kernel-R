# Research packages

Standalone Lean packages and numerical studies built on the Kernel R model.
Each has its own `lakefile.toml` and README.

## Recursive learning and trained cells

[`recursive-learning/`](recursive-learning/README.md) holds the adaptive
teaching loop, a discrete Lean model of feedback that changes both a lesson
and the next edit it proposes.

Its [`native/`](recursive-learning/native/README.md) package carries the
results of the latest releases, in actual R cells:

- training that stops by itself, and the joint read of two trained ports;
- the two-cell coincidence decision, with and without a lag in each cell;
- networks of trained cells of any depth, joined by forward wires;
- searches built from trained cells: the need of a port, a tree of
  questions and successive approximation.

Start with the
[map of the stop-learning results](recursive-learning/native/README.md#map-of-the-stop-learning-results)
and the [v0.4.0 release notes](../docs/RELEASE_V0_4_0.md).

## Robust slow chain

[`robust/`](robust/) contains the tested Python sources, certificates,
written arguments and summary reports for preparation from birth and
noise-dependent latency. The compressed raw traces are not included; run
`validate.py`, `periodic/validate.py`, `birth/validate.py` and
`latency/validate.py` from `robust/` to generate new campaigns. For the Lean
proofs and their scope, see
[robust coverage](../proof/lean/ROBUST_COVERAGE.md).

[`robust/ranges/`](robust/ranges/README.md) extends the eight point
certificates to closed ranges of the noise bound and the amplitude
deviation, without modifying the pinned sources.

## Reset window

[`reset-window/`](reset-window/README.md) is a standalone Lean model of
terminal saturation under compressed protection or residual coupling.

## Circuit simulation

[`circuit/`](circuit/README.md) is a transistor-level simulation of one cell
in an open 130 nm process. It is not a proof and not a hardware measurement.
