# Amendment 3: scope of the reported certificate and trace inventory

This is a reporting clarification, not a new experimental rule. It was
prepared against public commit `f774fc63824d158de0698e4e2be5baa9702881b2`
on 2026-11-12. That snapshot contains the completed calibration and 48
stage-2 ramps, with no stage-3 results. This inventory does not establish
whether another machine has already started an unpublished run.

`PREDICTION.md`, amendments 1 and 2, the manifest, the extraction script,
the calibration constants, all numerical budgets and all port status
rules remain as registered. The report generator and the generated
calibration note now state the following limitations explicitly.

## The threshold offset is an empirical calibration envelope

`h_mu` is the worst case on six cells (five calibration cells and the
nominal cell), not a bound established for each test cell. Applying
`level0 = Ls + mu` and this envelope to the 100 test cells assumes that
their dynamic threshold offsets are covered. Measuring `Ls` and noise
on each test cell does not establish that assumption.

The suggested 20 additional noiseless leak scans have **not** been run
as part of this amendment. The audit workspace does not have the pinned
ngspice executable and PDK required by the manifest. No replacement
simulator, invented result, or retrospectively registered scan is used.
The fallback is the explicit limitation in both the calibration note
and the final report summary.

If that diagnostic is added later, freeze its cell selection, extraction
and pass/fail rule before its results are inspected, retain failures and
missing scans, and report its relation to stage 3 honestly. Keep the
existing `mu`, `h_mu` and predictions unchanged for the original analysis.
Even 20 successful test-cell scans would provide additional empirical
support, not a bound for the other 80 cells or every port.

## Peak-to-gain correspondence remains a model assumption

The certificate is conditional on the scalar model's peak-to-gain
correspondence. The extracted gain is not an independent measurement
that establishes the circuit's main-charge dynamics. The previously
reported current-dependent slope variation remains relevant; a positive
budget alone does not close that circuit-to-model gap.

The generated summary therefore says **conditionally certified under
the registered rule**, rather than asserting that every hypothesis is
bounded on the port's own run. The original status labels and E4/E5
calculations are preserved so that this clarification cannot silently
change the registered result. An agreement is evidence under those
assumptions; a contradiction must still be retained and investigated.

## Calibration traces: present, not reported as lost or replayed

The Git tree of private repository `HevisNico/kernel-R-circuit`, branch
`sim/core-loop`, at `128d2d81eea498c4bb1c4db740f4f3dc745b7c57`
contains all 45 expected calibration `.npz` files under
`07-certification-traces/calibration/`: 20 ramps, 20 trainings and five
leak scans. It also contains the five preflight traces, including the
nominal leak scan. Every corresponding public metadata file carries a
`trace_sha256`.

This corroborates amendment 2's statement that stage-1 traces were still
on the machine and were retained. No missing trace or replay was found
in this inventory. **Presence is verified; binary integrity and
re-extraction are not claimed here.** The connected reader exposes the
tree but rejects the binary `.npz` contents, and authenticated binary
Git access was unavailable in the audit workspace. A reader with a
checkout of the private repository can compare each trace's SHA-256
with the public metadata before re-extraction.

The compact traces are not the full solver output. Replaying a noiseless
deck is not a substitute for checking the hash of the originally
retained artifact; byte-for-byte replay of this cohort was not tested
in this audit.
