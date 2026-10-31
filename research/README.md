# Robust slow-chain snapshot

`robust/` contains the tested Python sources, certificates, written arguments and
summary reports for preparation from birth and noise-dependent latency. Existing
source manifests are preserved. The compressed raw traces are not included;
run `validate.py`, `periodic/validate.py`, `birth/validate.py` and
`latency/validate.py` from `robust/` to generate new campaigns. Record verification
requires those corresponding traces and the recorded numerical runtime.

The historical notes describe the package before its integration into GitHub.
For the new Lean proofs and their exact scope, see
[robust coverage](../proof/lean/ROBUST_COVERAGE.md).

[`robust/ranges/`](robust/ranges/README.md) extends the eight point certificates to closed
ranges of the noise bound and the amplitude deviation (for example every ν in [0, 0.002]),
without modifying the pinned sources.
