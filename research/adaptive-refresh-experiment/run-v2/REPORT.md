# Adaptive refresh v2 — unedited generated report

One preregistered invocation; three fixed controller trajectories; no pilot or sweep.
Protocol: `c58ba5af913a5d129734aaa6d66a16fce99e27aa`.
V1 comparison uses its published result, not a rerun.

| Controller | Probes | Writes | Probe cost | Write cost | Total | Pre unsafe | Post unsafe | Undetected | Longest | Anchor reopenings | Ambiguous | Invalidations | Refusals | Final reserve |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| naive | 134 | 88 | 134 | 880 | 1014 | 839 | 808 | 739 | 34 | 0 | 0 | 0 | 0 | 0 |
| prudent | 1321 | 89 | 1321 | 890 | 2211 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 220 |
| adaptive | 435 | 89 | 435 | 890 | 1325 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 220 |

## Registered predictions

| ID | Verdict |
|---|---|
| A1 | PASS |
| A2 | PASS |
| A3 | PASS |
| A4 | PASS |
| A5 | PASS |
| A6 | PASS |
| A7 | PASS |
| A8 | PASS |

Adaptive/prudent cost: 1325/2211 = 0.599276.
Adaptive/v1 known-ceiling cost: 1325/1247 = 1.062550.
Observed adaptive ceilings before jump: [20, 21, 22]; after jump: [30, 31, 32].
Anchor reopenings at [662]; delay 1 periods.
Sampled true-rate variation 10; 5 × anchor reopenings = 5.

## Integrity and deviations

Trace audit issues: 0.

No protocol parameter or prediction was revised after publication. All verdicts are retained.
Each adaptive decision came from the Lean bridge. The separate trace audit checks
chronology, observations, prices, variable thresholds, carry propagation, lease coverage,
the distinction between ambiguous and proven violations, and local wait/write laws.
Lean proves the local ceiling, handoff and repair lemmas; the complete Python wrapper
is not asserted to have a new end-to-end formal proof.

## Limits

No absolute leakage ceiling was provided. The variation law B=10 over H=41 was provided,
not learned. This law covers the hidden jump and is indispensable to future safety.
A demonstrated violation would invalidate the old guarantee; a later repair cannot
make the past safe. Ambiguous sensor exceedances are counted separately from anchor changes.
This single deterministic model run is neither statistical confidence nor circuit validation.
The two-channel sensor and dose are assumed; prices are model units and sensing latency is absent.
The nominal 22-period R calibration still needs a waveform-based state/sensor/dose adapter.
The v1 comparison changes information and repair policies, not just observation expense.

Raw CSVs, metadata, stdout/stderr, exit status and hashes accompany this report.
