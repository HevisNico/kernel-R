# Kernel R v0.3.0: threshold-tolerant learning and verified coincidence

**Historical record of the published v0.3.0 release.** Released on
2026-11-10 from commit [`5195497`](https://github.com/HevisNico/kernel-R/commit/51954970d1c26690f69d0e7cabd201528f10cbef),
tag [`v0.3.0`](https://github.com/HevisNico/kernel-R/releases/tag/v0.3.0).
This file was added after publication so that every release has notes in
`docs/`. The text below is the published release text, with its links
pinned to the release commit. Later releases build on it; see
[v0.4.0](RELEASE_V0_4_0.md).

## Release text

This release adds Lean proofs for learning with realized thresholds and a
two-cell coincidence task. After training, the receiver accepts exactly
when both cells are tested on their trained ports and the programmed
offset is zero.

At 100 µs per model time unit, a complete native R run exists for every
admissible trial, and every complete run gives the expected decision. The
guarantee covers independent fixed fabrication variation of ±10%, FIRE
threshold error of ±3%, and absolute ERROR threshold variation of up to
0.001 at entry and 0.00025 at exit on each trained port. The trained port
starts at an exact gain of 1.2.
[Lean theorem `coincidence_exit_001_separation`](https://github.com/HevisNico/kernel-R/blob/51954970d1c26690f69d0e7cabd201528f10cbef/research/recursive-learning/native/CoincidenceSeparation.lean)

For the reduced constant-current comparator, Lean proves that one
admissible positive trial with nominal ERROR thresholds and ±10% current
variation rules out every shared current and duration, including settings
that reach the gain cap. The comparison concerns the declared mathematical
models and timing contract.

The release includes the registered benchmark, simulation scripts, and
numerical sweeps of the trade-off between timing tolerance and the number
of gain levels below the cap.
[Benchmark protocol](https://github.com/HevisNico/kernel-R/blob/51954970d1c26690f69d0e7cabd201528f10cbef/research/recursive-learning/COINCIDENCE_BENCHMARK.md) ·
[Sweep results](https://github.com/HevisNico/kernel-R/blob/51954970d1c26690f69d0e7cabd201528f10cbef/research/recursive-learning/coincidence/EXIT_TRADEOFF_RESULTS.md)
