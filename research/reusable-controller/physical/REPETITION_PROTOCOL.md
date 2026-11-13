# Fixed-cohort noisy repetition protocol

**Status: NOT_STARTED.** This document and its planning code do not launch a
simulator. The local environment lacks the pinned ngspice executable and PDK.
Reproducible external noise injection and the per-run physical residual
extractor are **UNIMPLEMENTED**; the noise preflight has **NOT_RUN**. Publication
of these rules must precede the first campaign run. This file alone does not
establish an external publication date or authorize an unrecorded protocol change.

## Frozen cohort and sample size

The sole selection input is `campaign-validation.json`, SHA-256
`01a28a9149bc1f8caa0f4bba1690dde47ccacfb87b727f41f8caac9741f56419`, for #109
commit `7ded279f103dab5beb6c1c671f1acbdf4cff18c0`. Its original 37 status-3 ports
are frozen. Their grouping contains 35 cells. No newly eligible port under an
asymmetric or subsequently relaxed rule may enter this campaign. In particular,
`t6004` port 1 remains excluded. The original selection was retrospective;
these new repetitions will be a separate validation set.

Use **K = 100 complete, freshly initialized trains per cell**: 3,500 simulator
runs and 3,700 eligible-port observations. Each train retains the original
21-pulse schedule: ten port-1 pulses, ten port-2 pulses, then the joint pulse.
For a cell with only one eligible port, simulate and retain both ports but
include only the frozen eligible port in the primary statistical ledger.

`repetition_plan.py` derives all trial identifiers and grouping from the frozen
report. It distinguishes `mismatch_seed` (the cell identifier), `repeat_id`,
and a unique proposed `noise_seed`. **Existing ngspice wrappers do not implement
that noise seed.** Merely adding this field to a manifest does not seed trnoise.
No run is replaced, discarded or repeated until success. Record failures with
their reasons; no optional stopping or sample-size change follows test outcomes.

## Runtime and input model

Use the #109 ngspice 42 binary, SHA-256
`820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`, and SKY130
PDK commit `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, with the original
compatibility/start files, solver tolerances, temperature 27 °C, and
**maximum solver step 200 ns**. Noise sampling remains 400 ns. A separate
integration-step study must not be silently mixed into these repetitions.

Keep the original noise amplitudes, spectra and shared-channel correlations
from the pinned netlist and `research/circuit/noise.json`. A replacement
external waveform generator must specify its algorithm, finite-window flicker
construction, interpolation, seed expansion and channel sharing before use.
Its preflight must establish replay of identical waveforms and check the
declared amplitudes/spectra/correlations. A new injection implementation is
not automatically identical in law to the original trnoise sources.

Before any run, record a reviewed implementation amendment with the generator,
extractor and runtime hashes. Independent noise streams between repeats remain
an explicit statistical assumption; unique integer seeds alone do not prove it.
Do not reuse a waveform across different repeats. Ports within a cell retain
the prescribed shared noise and are not assumed independent.

Log all 17 original signals plus the two xmout drain currents used by #109.
Preserve exact timestamps, realized noise waveforms and solver points through
each pulse, including 0.75 and 1 time-unit integral endpoints. Retain compact
traces and hash them; record netlist, runtime, PDK, source, extractor and noise
identities. Keep FIRE times, charge before each read, steering/latch flags,
current integrals, and the full gain/threshold residual accounting.

## Calibration and endpoints

Freeze the original per-port `D` and `DE`, `kappa`, `d0`, predicted need `m`,
threshold budget `ell3`, status-3 limits and selection before the repeats.
Do not fit offsets or enlarge residual budgets from the test repeats. Original
noiseless and noisy calibration evidence remains distinguished by run identity.

Record two separate Boolean endpoints per eligible port and complete train:

1. **Count agreement:** the first FIRE index agrees with the frozen predicted
   need. Missing FIRE, an invalid extraction or a guard failure cannot pass.
2. **Measured-residual success:** the audited extractor finds that every
   declared residual/guard obligation holds on this actual noisy train using
   the frozen reference constants. It must check both independent current-based
   residuals and the applicable threshold/rest/steering guards. A matching count
   alone never supplies this endpoint.

The full executable endpoint specification is a readiness blocker. It must
retain the distinction between logarithmic `eps3`, corrected amplitudes and
scalar gain, and explicitly retain the post-0.75 FIRE reconstruction via
`kappa`. It must not label that unmeasured continuation as independently measured.
Failures to evaluate an obligation count as endpoint failures, not exclusions.
Before implementation, only synthetic endpoint flags may exercise the analyzer;
no physical validation claim can be made from them.

The **primary event** is joint success of both endpoints on one eligible port.
For a simulator failure, both endpoints fail for every eligible port of that
run. Missing records block analysis entirely. A completed run supplies the
exact planned identities, runtime and evidence hashes, and one outcome for
each planned eligible port. The analyzer rejects missing/duplicate/unplanned
trials, altered cohort/plan hashes and incomplete endpoint records.

## Statistical analysis

For each fixed eligible port, use its 100 independent repeat outcomes.
The one-sided 95% Clopper–Pearson lower success bound is the solution `pL` of
`P[Binomial(100,pL) >= successes] = 0.05`; it is zero for zero successes.
The implementation inverts that binomial tail by bisection without SciPy.
The interval construction follows the [NIST exact-binomial definition](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/exacbino.htm).
“Exact” refers to the binomial interval construction; evaluation uses ordinary
floating-point arithmetic and is not a Lean-certified numerical enclosure.

Also compute simultaneous bounds using `alpha = 0.05/37` per port. Bonferroni
does not require independence between the 37 ports, but each per-port
binomial bound requires independent, identically distributed repeats.
The unweighted mean of these 37 simultaneous lower bounds is a lower bound
for the mean success probability of this **fixed cohort**, on the same
simultaneous coverage event. Do not pool the 3,700 observations as iid trials.

The primary simultaneous 95% claim concerns the joint-success family.
Report count and residual families separately with their own bounds; these
three families together do not acquire 95% simultaneous coverage merely by
each using `0.05/37`. No population claim over other mismatch cells, temperatures,
future reset sequences or alternative lessons follows from this fixed cohort.

Even 100 successes out of 100 give a per-port lower bound below one
(`0.05^(1/100)`), and a smaller simultaneous bound (`(0.05/37)^(1/100)`).
The result is statistical evidence under the noise model, not deterministic
certification. Report both failures and successful runs, without changing the
frozen eligibility rule after seeing them.

## Prepare and check

```sh
python -B repetition_plan.py
python -B -m unittest test_repetition_plan
# Optional artifact, still NOT_STARTED:
python -B repetition_plan.py --write-plan /path/to/repetition-manifest.json
# Only after a reviewed implementation and a complete actual ledger:
python -B repetition_plan.py --records /path/to/records.json --report /path/to/statistics.json
```

The records envelope contains the canonical plan SHA-256,
`endpoint_extractor_sha256`, and all run records. A successful record contains
the planned identity fields, `status: "done"`, the declared runtime,
`trace_sha256`, `noise_waveform_sha256`, and ordered `outcomes` with `port`,
`count_agreement`, and `measured_residual_success`. A failed record has
`status: "failed"`, a nonempty `reason`, and empty `outcomes`.
Hashes establish identities only when their source evidence is separately
verified. The statistical analyzer itself never authenticates physical truth;
its output explicitly says `RECORDS_ANALYSED_NOT_PHYSICALLY_VALIDATED`.
