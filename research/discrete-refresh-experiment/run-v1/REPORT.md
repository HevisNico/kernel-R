# Discrete refresh v1 — unedited generated report

One registered invocation, three fixed controller trajectories. No parameter sweep.
Protocol: `ca8645502588339c43e836b7319c6348dbebcfd2`.
Dependency: frozen #111 at `ba978af1edaf51572aa0af9d1bfc83e309438d3d`.

| Controller | Probes | Writes | Probe cost | Write cost | Total | Pre unsafe | Post unsafe | Undetected | Longest undetected | Reopenings | Refusals | Final reserve |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| naive | 134 | 88 | 134 | 880 | 1014 | 860 | 829 | 759 | 36 | 0 | 0 | 0 |
| prudent | 1321 | 89 | 1321 | 890 | 2211 | 0 | 0 | 0 | 0 | 0 | 0 | 220 |
| contract | 357 | 89 | 357 | 890 | 1247 | 0 | 0 | 0 | 0 | 1 | 0 | 220 |

## Registered predictions

| ID | Verdict |
|---|---|
| P1 | PASS |
| P2 | PASS |
| P3 | PASS |
| P4 | PASS |
| P5 | PASS |
| P6 | PASS |
| P7 | PASS |

Contract/prudent cost ratio: 1247/2211 = 0.563998.
Contract reopening timestamps: [662]; first post-jump probe: 662; reopening delay: 1 periods.
Sampled true-rate variation: 10; 5 × reopenings = 5.

## Integrity and deviations

Trace audit issues: 0.

The audit checks chronology, all sensor reports, every paid probe and command,
baseline rules, interval memory, and each contract wait/write lower-bound law.
Contract actions were returned by the Lean process executing #111 definitions;
the independent numeric trace audit also checks their prescribed decision rule.
No protocol parameter or prediction was revised after publication. A failed
prediction is retained above; no run was repeated to improve its outcome.

## Limits

This is one deterministic model comparison, not statistical or transistor evidence.
The 22-period calibration does not prove a physical R adapter. The supervisor
uses a known hard ceiling covering the jump; its rate sensor only drives reopening
memory in this trial. It does not learn a tighter safe future bound.
The wrapper is not a newly proved end-to-end OfferFactory instance. Prices are
declared units, measurement latency is absent, and the two-channel sensor is assumed.
Unsafe exposure counts discrete pre-write samples, not a continuous-time integral.

Raw CSVs, metadata, stdout/stderr and SHA-256 hashes accompany this report.
