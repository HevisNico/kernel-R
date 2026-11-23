# Development lot 2 of inverter instances (cell C5): result

**Development work, not preregistered.**
- **Rule and code:** run under the rule of 5c0f06f (`DEV_LOT_RULE_2.md`), with the code identical to d25ee8e (C5: help
  mirror w 2, l 16, J0 4.0).
- **Run:** started 2026-11-23T11:09:04Z, ended 11:24:35Z.
- Every verdict is conditional on the open premises listed in `SUMMARY.json`:
  - the leak along the trajectory, a modelling step [I];
  - the measured real hypotheses, which are the simulation's claims;
  - the latch delay, measured rather than bounded.

## Verdict: **C5 holds**

| | k / n | Wilson 95 % |
|---|---|---|
| finished | 60 / 60 (no failure, no timeout) | |
| eligible (K0) | **60 / 60** | [0.940, 1.000] |
| with room (K3) | **60 / 60** | [0.940, 1.000] |

- **Target:** the min K3 silence margin is **0.1079 ≥ 0.05**, and room is **60/60 ≥ 57**. Both are met.
- **Early stop:** not triggered (20 of the first 20 had room).
- **Checks:** the kernel agreed with the mirror on 60/60, and the same sample held across the 5 runs on 60/60.

## Distributions (min, median, max over 60)

| Quantity | min | median | max |
|---|---|---|---|
| silence margin K0 | 0.1137 | 0.1707 | 0.2068 |
| silence margin K3 | 0.1079 | 0.1649 | 0.2010 |
| firing margin K0 | 0.2566 | 0.2934 | 0.3214 |
| firing margin K3 | 0.2522 | 0.2891 | 0.3170 |
| δ (1 unit = 500 mV) | 0.0001 | 0.0088 | 0.0277 (13.8 mV) |
| α | 0.0037 | 0.0041 | 0.0044 |
| X present (≤ H0·hl = 1.35) | 0.8160 | 0.8695 | 0.9034 |
| X absent (≤ 1.35) | 1.1941 | 1.2241 | 1.2552 |
| emission (tu) | 0.5033 | 0.5146 | 0.5245 |
| ηH | 0.0223 | 0.0362 | 0.0657 |
| Q | 0.8902 | 0.9485 | 0.9856 |
| latch delay (tu) | 0.00099 | 0.00101 | 0.00105 |
| headroom to vdd (V) | 0.098 | 0.115 | 0.142 |
| machine seconds per instance | 57.3 | 59.2 | 65.3 |

Every emission lies in the proved interval and in the campaign dates (0.40, 0.65]: `Timing` is part of each
instance's checked premises.

## Failures

None.

## Cost

- 61.1 machine-minutes of job time, against a ceiling of 90.
- 15.4 minutes of wall time on one 4-core machine, 4 jobs at a time.
- Traces kept locally (267 MB), not committed. `RESULT_SHA256SUMS` lists every MEASURE.json, GATE json and Lean file.
  `RESULT_ANALYSIS.txt` is the analysis output.
