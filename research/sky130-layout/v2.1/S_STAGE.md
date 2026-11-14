# Layout 2.1: declaration of the nominal stage

Declared on 2026-11-14, **before any simulation of layout 2.1.**
[`PREDICTION.md`](PREDICTION.md) is not edited.

The owner read [`X_REPORT.md`](X_REPORT.md): X1 fails (0.043 fF between
`vq` and `vrefmn`, limit 0.03 fF), X3 fails (52.3 fF on `vq`, limit
45 fF), X2, X4, X5, X6 and X7 hold. **X1 and X3 are not amended. The
stage on the 8 cells stays blocked.** The owner gave the go for the
nominal stage S1 to S5 only, as preregistered.

## Runs

Those of the second layout ([`../v2/S_STAGE.md`](../v2/S_STAGE.md)),
made the same way: nominal cell, typical corner, no noise, no mismatch;
the runners of the campaigns unchanged, through the harness
`../phase1/p_run.py`, with the primary list of capacitances of
layout 2.1.

| Input | File | sha256 |
|---|---|---|
| Capacitances, primary list | `phase1/p_caps_primary.csv` | `89ba00a82227092740d523523a88d913ef5bd7b3444d895671db0d0cd133cba4`, the file of the extraction (`layout/SHA256SUMS_X`) |
| Source and drain areas | `phase1/p_areas.csv` | `19bd1f27e174c22c7b8b2eea9afb8d81fe4a744993539763ab46b819dd88542a`, the same file as for the first and second layouts |
| Constants of stage P | `phase1/constants_stage_p.json` | `6a453a3227503d9b6767424ded43c0c466c34bae65b980cd976365bc766c1306`, the same file as for the second layout |

**Eight runs**: `nom_cell`, `nom_ramp`, `nom_read`, `nom_leak`,
`nom_refresh` (100 pulses, 0.1 TΩ), `nom_cell125`, `nom_refresh125`,
`nom_train`.

One machine, this one, four runs at a time, by the launcher of stage P
(`../phase1/execute.py`): the attempt marker `phase1/RUN_ATTEMPT_S.json`
pushed before the first run, the name of each run pushed as started
before it begins, a run that started never made again. Primary list
only.

## How S1 to S5 are read

`phase1/s_stage.py`, committed with this file: a copy of the script of
the second layout with three changes, said in its first lines.

| | Read on | Rule |
|---|---|---|
| S1 | `nom_train` | As for the second layout: `c_pre` of every one of its 21 pulses between 0.1 and 0.1001 |
| S2 | `nom_cell` | As for the second layout: no step of a port at rest or of a firing pulse above 0.005 mV; for each port, its first silent step within 0.003 mV of each later one |
| S3 | `nom_ramp`, `nom_read` | As for the second layout: the gap by the formula of `cert_analyze.py predict` with the constants of stage P, against the schematic gap; both shifts between −0.002 and +0.010, within 0.0005 of each other |
| S4 | the eight runs | As for the second layout: L1, L2, L3, L5, L6, L7 and L13 |
| S5 | `nom_cell` | **Changed by [`PREDICTION.md`](PREDICTION.md)**: every step of a silent pulse of the pulsed port between 1.350 and 1.385 mV. The report also says whether it is in the range of the second layout, 1.340 to 1.365 mV |

A prediction whose run has no result is not evaluable. The column of
comparison of the report is the second layout, read by the same script
on its committed results (`../v2/phase1/results_s/`).

The analysis was tried on those results before this stage (no
simulation): it gives again 0.100000 to 0.100039 for the rest charge,
0.001 mV for the largest step, +0.00758 and +0.00756 for the shift,
1.309 mV for the silent step.

The report is written once, after the last run, and pushed as it comes.
Then the work stops.
