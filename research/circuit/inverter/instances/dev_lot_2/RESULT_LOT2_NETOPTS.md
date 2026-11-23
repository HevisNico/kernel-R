# Lot 2 re-measured at the layered network's simulator directives: result

**Development work, not preregistered.**
- **Amendment and code:** run under `AMENDMENT_LOT2.md` (c5c06e0), with the code at 5a26a40 (`invinst/driver2.py`, at
  the directives of `config_netopts.json`: reltol 1e-5, …).
- **Design and seeds:** the same as lot 2: C5, seeds 9711-9770.
- **Run:** started 2026-11-23T14:33:59Z, ended 14:52:18Z.
- **Untouched:** `RESULT_2.md` (lot 2 at reltol 1e-4).
- **Files:** in `netopts/` (summary, analysis, per-instance table, checksums).
- Every verdict is conditional on the open premises listed in `netopts/SUMMARY.json`.

## Verdict: **C5 holds**

| | k / n | Wilson 95 % |
|---|---|---|
| finished | 60 / 60 (no failure, no timeout) | |
| eligible (K0) | **60 / 60** | [0.940, 1.000] |
| with room (K3) | **60 / 60** | [0.940, 1.000] |

- **Target:** the min K3 silence margin is **0.1065 ≥ 0.05**, and room is **60/60 ≥ 57**. Both are met.
- **Early stop:** not triggered.
- **Checks:** the kernel agreed with the mirror on 60/60, and the same sample held across the 5 runs on 60/60.

## Distributions (min, median, max over 60)

| Quantity | min | median | max |
|---|---|---|---|
| silence margin K0 | 0.1123 | 0.1613 | 0.1914 |
| silence margin K3 | 0.1065 | 0.1555 | 0.1856 |
| firing margin K0 | 0.2453 | 0.2771 | 0.3070 |
| firing margin K3 | 0.2410 | 0.2728 | 0.3026 |
| δ | 0.0001 | 0.0088 | 0.0277 (13.8 mV) |
| α | 0.0037 | 0.0041 | 0.0044 |
| X present (≤ 1.35) | 0.8160 | 0.8694 | 0.9034 |
| X absent (≤ 1.35) | 1.1941 | 1.2241 | 1.2552 |
| emission (tu) | 0.5033 | 0.5146 | 0.5245 |
| ηH | 0.0358 | 0.0457 | 0.0761 |
| Q | 0.8902 | 0.9485 | 0.9856 |
| latch delay (tu) | 0.00099 | 0.00101 | 0.00105 |
| headroom (V) | 0.098 | 0.115 | 0.142 |
| machine seconds per instance | 67.6 | 71.0 | 74.2 |

## Per instance, against lot 2 (reltol 1e-4)

- **Verdicts:** no change on any of the 60 seeds.
- **Changes, amended minus lot 2:**
  - silence margins: −0.022 to +0.002 (median −0.011);
  - firing margins: −0.034 to +0.000 (median −0.016);
  - ηH: −0.004 to +0.020 (median +0.011);
  - ηJ: −0.011 to +0.027 (median +0.007);
  - ηm: −0.001 to +0.004.
- **The node voltages are unchanged to about 10⁻⁶:** X, the emission date, δ and Q. Example, seed 9724: x max 1.2286499
  against 1.2286495, emission 0.5191689 against 0.5191691. The integrals of the currents change. These are
  the budgets ηH, ηJ and ηm, taken from the ammeters at the main capacitor, whose switching-edge spikes the tighter
  tolerance resolves differently [I]. The traces differ: seed 9724 R1 has 9,626 points, against 8,225.
- **The five lowest K3 silence margins** (amended, with lot 2 in brackets): 9724 0.1065 (0.1079), 9747 0.1145
  (0.1256), 9748 0.1176 (0.1188), 9731 0.1217 (0.1328), 9768 0.1245 (0.1345).
- The full table is in `netopts/PER_INSTANCE_DIFF.tsv`.

## Cost

- 72.4 machine-minutes against a ceiling of 90.
- 18.2 minutes of wall time on one 4-core machine.
- Traces kept locally, not committed.
