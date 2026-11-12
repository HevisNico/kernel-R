# Constants of stage 1

Written by `cert_analyze.py calibrate` from the calibration cohort, under `PREDICTION.md`.

Status: **evaluated**.

| Constant | Value | From |
|---|---|---|
| `kappa` | 0.07461 | 157 silent reads; largest distance to it 0.00038 |
| `d0` | 0.04209 | 157 pairs of successive reads; sigma 0.00021, from 0.04143 to 0.04259 |
| `s` | 31.316 per V | slope of the gain against the stored voltage, silent reads before the first FIRE |
| `mu` | 0.00039 | firing level minus static level, 6 of 6 leak scans |
| `h_mu` | 0.00151 | spread of `mu` between cells plus the largest half-width of a scan |

**Scope:** `h_mu` is the worst case on six cells (five calibration cells and the nominal cell), not a bound established for each test cell. Applying it to the 100 test cells assumes that the calibration covers their dynamic threshold offsets. The inferred gains also assume the scalar model's peak-to-gain correspondence; these simulations do not prove that correspondence.

| Leak scan | First FIRE | Silent read | Peak of the silent read | Peak of the read before | Static level | Midpoint minus static | Half-width |
|---|---|---|---|---|---|---|---|
| `nom_leak` | 4 | 9 | 0.99821 | 1.00006 | 0.99819 | +0.00094 | 0.00093 |
| `c5001_leak` | 3 | 14 | 0.99190 | 0.99349 | 0.99268 | +0.00001 | 0.00079 |
| `c5002_leak` | 5 | 25 | 1.01123 | 1.01300 | 1.01198 | +0.00014 | 0.00088 |
| `c5003_leak` | 5 | 15 | 1.01413 | 1.01604 | 1.01495 | +0.00014 | 0.00095 |
| `c5004_leak` | 4 | 14 | 1.00542 | 1.00728 | 1.00611 | +0.00024 | 0.00093 |
| `c5005_leak` | 4 | 10 | 0.96878 | 0.97070 | 0.96885 | +0.00089 | 0.00096 |
