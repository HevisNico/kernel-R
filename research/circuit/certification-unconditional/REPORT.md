# Certification with the level of each cell and an independent measure of the gain: report

Written by `uncond_analyze.py report` under [`PREDICTION.md`](PREDICTION.md). One row per cell: [`cells.csv`](cells.csv). One row per port: [`ports.csv`](ports.csv). The certification campaign is in [`../certification/`](../certification/REPORT.md); nothing of it is changed.

## Summary

1. **Level of each cell (condition 1):** the `mu` measured on the cell is inside the envelope of the six calibration cells for 100 of the 100 test cells (0 not evaluable); the whole bracket of the level is inside for 67. `mu_cell` goes from -0.00025 to +0.00155; the envelope is [-0.00112, +0.00191].
2. **Independent gain (condition 2):** the gain inferred from the peak and the gain measured on the current of the mirror differ, after one constant per port, by at most `eps_peak`: median 0.00393, largest 0.00603, over 200 ports and 819 silent reads and 1181 reads with a FIRE.
3. **New status:** with the level of its own cell and the independent gain, 0 ports of 200 are certified; the count is the predicted one on 0 of them. With the level of the cell alone (status 1): 58 ports.
4. **Against the certification campaign:** of its 59 ports certified under condition, 0 are certified by the new status and 59 are not (54: room is not positive; largest term B, 4: room is not positive; largest term a, 1: room is not positive; largest term (20/17)*ell); 0 ports that it did not certify are certified now.
5. **What the new status still rests on:** a simulation; the level of a cell is bracketed once, on port 1, and used for its two ports; `eps_peak` is measured without noise and applied to the noisy reads of the same port; `kappa`, `d0`, `eps_kappa` and the centre `mu` come from the certification campaign; the count of a port comes from one noisy run.

## Predictions

| | Prediction | Measured | Verdict |
|---|---|---|---|
| U1 | no run fails, and the 100 scans have a silent read after their first FIRE | 0 runs without a usable result; 100 of 100 scans with a silent read after their first FIRE | holds |
| U2 | the `mu` of every cell is inside the envelope of the six cells | 100 of 100 evaluable cells inside | holds |
| U3 | the bracket is inside the envelope for 65 to 95 cells | 67 of 100 evaluable cells | holds |
| U4 | status 1 certifies 52 to 68 ports | 58 of 200 | holds |
| U5 | the median `eps_peak` is between 0.0003 and 0.004 | 0.00393 over 200 ports | holds |
| U6 | status 2 certifies 15 to 58 ports | 0 of 200 | fails |
| U7 | no certified port has its count contradicted | 0 of 58 by status 1, 0 of 0 by status 2 | holds |

## Failures

- **F1, a certified port whose count is contradicted:** none.
- **F2, a cell whose `mu` is outside the envelope of the six cells:** none.
- **Runs or cells without a usable result:** none.

## Condition 1: the level of each cell

| | Certification campaign (six cells) | This campaign (each cell) |
|---|---|---|
| Midpoint of the bracket minus the static level | `mu` = +0.00039 | median +0.00058, from -0.00025 to +0.00155 |
| Half-width of the bracket | largest 0.00096 | median 0.00092, largest 0.00107 |
| Bound of the level around `level0` | `h_mu` = 0.00151 for every cell | `h1`: median 0.00130, largest 0.00217; `h2` (with `eps_scan`): median 0.00619, largest 0.00735 |

Cells whose bracket is not inside the envelope (`h1 > h_mu`): 33: `t6004` (0.00217), `t6005` (0.00157), `t6007` (0.00169), `t6008` (0.00176), `t6009` (0.00202), `t6010` (0.00164), `t6011` (0.00159), `t6012` (0.00166), `t6017` (0.00195), `t6021` (0.00183), `t6024` (0.00195), `t6026` (0.00174), `t6027` (0.00171), `t6030` (0.00200), `t6032` (0.00155), `t6038` (0.00164), `t6040` (0.00185), `t6041` (0.00179), `t6042` (0.00181), `t6044` (0.00198), `t6053` (0.00170), `t6055` (0.00181), `t6062` (0.00155), `t6065` (0.00199), `t6067` (0.00199), `t6073` (0.00168), `t6075` (0.00155), `t6079` (0.00151), `t6086` (0.00176), `t6088` (0.00156), `t6089` (0.00188), `t6097` (0.00180), `t6100` (0.00169).

## Condition 2: the gain measured on the current of the mirror

| | Value |
|---|---|
| `eps_peak` of a port (10 reads of its training without noise) | smallest 0.00032, median 0.00393, largest 0.00603 |
| Its part from the silent reads | median 0.00035, largest 0.00060 |
| Its part from the reads with a FIRE | median 0.00383, largest 0.00593, over 200 ports that have one |
| `eps_scan` of a cell (40 reads of its leak scan) | median 0.00550, largest 0.00626 |
| Constant `D` of a port | mean -0.02705, from -0.02754 to -0.02642 |
| Reads with a FIRE earlier than 0.76, left out | 0 in the trainings, 0 in the scans |
| Same-cell check, port 1 | 100 of 100 cells within 0.0002; largest difference 0.00000 |
| Same difference, port 2, reported | largest 0.00004 |
| Count of the training without noise equal to the predicted `m` | 198 of 200 ports |

## The budget, side by side

| Term | Certification campaign | Status 1: level of the cell | Status 2: level of the cell and independent gain |
|---|---|---|---|
| Start distance | `a`: median 0.01384 | the same | `a + eps_peak`: median 0.01742 |
| Cumulated gain | `B`: median 0.00651 | the same | `B + 2*eps_peak`: median 0.01416 |
| Threshold `ell` | median 0.00407 | median 0.00392 | median 0.00875 |
| Room | median -0.00410; positive on 61 ports | median -0.00370; positive on 60 | median -0.01905; positive on 0 |
| Certified | 59 | 58 | 0 |
| Certified with the count contradicted | 0 | 0 | 0 |

| Certification campaign | New status | Ports |
|---|---|---|
| outside | outside | 141 |
| certified | outside | 59 |

## The 59 ports certified under condition by the certification campaign

| Cell | Port | m | Count | Agrees | Certification campaign | Its room | `h1` | Room 1 | Status 1 | `eps_peak` | Room 2 | New status | Reason |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6002` | 1 | 2 | 2 | yes | certified | +0.01033 | 0.00136 | +0.01051 | certified | 0.00443 | -0.00924 | outside | room is not positive; largest term B |
| `t6003` | 1 | 5 | 5 | yes | certified | +0.00319 | 0.00132 | +0.00341 | certified | 0.00400 | -0.01376 | outside | room is not positive; largest term B |
| `t6004` | 1 | 6 | 6 | yes | certified | +0.00375 | 0.00217 | +0.00298 | certified | 0.00329 | -0.01252 | outside | room is not positive; largest term B |
| `t6004` | 2 | 4 | 4 | yes | certified | +0.00573 | 0.00217 | +0.00496 | certified | 0.00373 | -0.01187 | outside | room is not positive; largest term B |
| `t6005` | 1 | 2 | 2 | yes | certified | +0.00473 | 0.00157 | +0.00466 | certified | 0.00440 | -0.01449 | outside | room is not positive; largest term B |
| `t6008` | 1 | 3 | 3 | yes | certified | +0.00775 | 0.00176 | +0.00745 | certified | 0.00391 | -0.00998 | outside | room is not positive; largest term (20/17)*ell |
| `t6009` | 2 | 3 | 3 | yes | certified | +0.00680 | 0.00202 | +0.00620 | certified | 0.00384 | -0.01135 | outside | room is not positive; largest term B |
| `t6010` | 1 | 4 | 4 | yes | certified | +0.00416 | 0.00164 | +0.00400 | certified | 0.00478 | -0.01690 | outside | room is not positive; largest term B |
| `t6011` | 2 | 5 | 5 | yes | certified | +0.00516 | 0.00159 | +0.00507 | certified | 0.00359 | -0.01174 | outside | room is not positive; largest term B |
| `t6012` | 1 | 4 | 4 | yes | certified | +0.00895 | 0.00166 | +0.00878 | certified | 0.00365 | -0.00748 | outside | room is not positive; largest term B |
| `t6013` | 2 | 3 | 3 | yes | certified | +0.00592 | 0.00112 | +0.00638 | certified | 0.00405 | -0.01116 | outside | room is not positive; largest term B |
| `t6015` | 1 | 4 | 4 | yes | certified | +0.00464 | 0.00106 | +0.00517 | certified | 0.00445 | -0.01451 | outside | room is not positive; largest term B |
| `t6016` | 1 | 4 | 4 | yes | certified | +0.00129 | 0.00136 | +0.00147 | certified | 0.00399 | -0.01483 | outside | room is not positive; largest term B |
| `t6018` | 2 | 3 | 3 | yes | certified | +0.00548 | 0.00130 | +0.00573 | certified | 0.00453 | -0.01422 | outside | room is not positive; largest term B |
| `t6019` | 2 | 4 | 4 | yes | certified | +0.00132 | 0.00117 | +0.00171 | certified | 0.00334 | -0.01363 | outside | room is not positive; largest term B |
| `t6025` | 1 | 4 | 4 | yes | certified | +0.00008 | 0.00094 | +0.00075 | certified | 0.00347 | -0.01585 | outside | room is not positive; largest term B |
| `t6027` | 2 | 3 | 3 | yes | certified | +0.00021 | 0.00171 | -0.00003 | outside | 0.00404 | -0.01786 | outside | room is not positive; largest term B |
| `t6028` | 2 | 4 | 4 | yes | certified | +0.00523 | 0.00106 | +0.00575 | certified | 0.00445 | -0.01334 | outside | room is not positive; largest term B |
| `t6030` | 1 | 3 | 3 | yes | certified | +0.00345 | 0.00200 | +0.00287 | certified | 0.00365 | -0.01390 | outside | room is not positive; largest term B |
| `t6031` | 1 | 4 | 4 | yes | certified | +0.00247 | 0.00094 | +0.00315 | certified | 0.00439 | -0.01584 | outside | room is not positive; largest term B |
| `t6032` | 1 | 3 | 3 | yes | certified | +0.00566 | 0.00155 | +0.00562 | certified | 0.00356 | -0.01026 | outside | room is not positive; largest term B |
| `t6032` | 2 | 4 | 4 | yes | certified | +0.00562 | 0.00155 | +0.00558 | certified | 0.00397 | -0.01152 | outside | room is not positive; largest term B |
| `t6037` | 1 | 4 | 4 | yes | certified | +0.00115 | 0.00126 | +0.00145 | certified | 0.00283 | -0.01112 | outside | room is not positive; largest term B |
| `t6037` | 2 | 4 | 4 | yes | certified | +0.00122 | 0.00126 | +0.00151 | certified | 0.00447 | -0.01600 | outside | room is not positive; largest term a |
| `t6038` | 1 | 4 | 4 | yes | certified | +0.00019 | 0.00164 | +0.00004 | certified | 0.00432 | -0.01862 | outside | room is not positive; largest term B |
| `t6040` | 2 | 5 | 5 | yes | certified | +0.00319 | 0.00185 | +0.00279 | certified | 0.00325 | -0.01219 | outside | room is not positive; largest term B |
| `t6042` | 2 | 5 | 5 | yes | certified | +0.00341 | 0.00181 | +0.00306 | certified | 0.00453 | -0.01579 | outside | room is not positive; largest term B |
| `t6043` | 2 | 5 | 5 | yes | certified | +0.00597 | 0.00133 | +0.00618 | certified | 0.00360 | -0.00987 | outside | room is not positive; largest term B |
| `t6045` | 2 | 4 | 4 | yes | certified | +0.00075 | 0.00087 | +0.00150 | certified | 0.00397 | -0.01676 | outside | room is not positive; largest term B |
| `t6050` | 2 | 4 | 4 | yes | certified | +0.00392 | 0.00095 | +0.00459 | certified | 0.00294 | -0.01005 | outside | room is not positive; largest term B |
| `t6051` | 2 | 3 | 3 | yes | certified | +0.00887 | 0.00130 | +0.00911 | certified | 0.00377 | -0.00842 | outside | room is not positive; largest term B |
| `t6052` | 1 | 4 | 4 | yes | certified | +0.00218 | 0.00094 | +0.00285 | certified | 0.00372 | -0.01468 | outside | room is not positive; largest term B |
| `t6055` | 1 | 6 | 6 | yes | certified | +0.00156 | 0.00181 | +0.00121 | certified | 0.00393 | -0.01577 | outside | room is not positive; largest term a |
| `t6056` | 1 | 5 | 5 | yes | certified | +0.00127 | 0.00125 | +0.00158 | certified | 0.00487 | -0.01852 | outside | room is not positive; largest term B |
| `t6058` | 2 | 4 | 4 | yes | certified | +0.00370 | 0.00121 | +0.00405 | certified | 0.00358 | -0.01130 | outside | room is not positive; largest term B |
| `t6061` | 2 | 3 | 3 | yes | certified | +0.00343 | 0.00123 | +0.00376 | certified | 0.00418 | -0.01323 | outside | room is not positive; largest term B |
| `t6063` | 1 | 2 | 2 | yes | certified | +0.00746 | 0.00117 | +0.00786 | certified | 0.00392 | -0.01011 | outside | room is not positive; largest term B |
| `t6065` | 1 | 4 | 4 | yes | certified | +0.01277 | 0.00199 | +0.01222 | certified | 0.00374 | -0.00483 | outside | room is not positive; largest term B |
| `t6067` | 2 | 3 | 3 | yes | certified | +0.00518 | 0.00199 | +0.00461 | certified | 0.00425 | -0.01355 | outside | room is not positive; largest term B |
| `t6068` | 2 | 2 | 2 | yes | certified | +0.00448 | 0.00099 | +0.00510 | certified | 0.00471 | -0.01542 | outside | room is not positive; largest term B |
| `t6074` | 1 | 3 | 3 | yes | certified | +0.00907 | 0.00079 | +0.00992 | certified | 0.00463 | -0.01058 | outside | room is not positive; largest term B |
| `t6075` | 2 | 4 | 4 | yes | certified | +0.00789 | 0.00155 | +0.00783 | certified | 0.00400 | -0.01023 | outside | room is not positive; largest term B |
| `t6076` | 1 | 4 | 4 | yes | certified | +0.00199 | 0.00093 | +0.00267 | certified | 0.00369 | -0.01428 | outside | room is not positive; largest term B |
| `t6077` | 1 | 5 | 5 | yes | certified | +0.00441 | 0.00140 | +0.00455 | certified | 0.00336 | -0.01026 | outside | room is not positive; largest term B |
| `t6077` | 2 | 5 | 5 | yes | certified | +0.00605 | 0.00140 | +0.00619 | certified | 0.00420 | -0.01114 | outside | room is not positive; largest term B |
| `t6079` | 1 | 4 | 4 | yes | certified | +0.00722 | 0.00151 | +0.00721 | certified | 0.00432 | -0.01173 | outside | room is not positive; largest term B |
| `t6079` | 2 | 4 | 4 | yes | certified | +0.00048 | 0.00151 | +0.00048 | certified | 0.00355 | -0.01614 | outside | room is not positive; largest term B |
| `t6080` | 2 | 3 | 3 | yes | certified | +0.00075 | 0.00123 | +0.00108 | certified | 0.00333 | -0.01417 | outside | room is not positive; largest term B |
| `t6081` | 1 | 4 | 4 | yes | certified | +0.00069 | 0.00108 | +0.00120 | certified | 0.00440 | -0.01711 | outside | room is not positive; largest term B |
| `t6082` | 2 | 4 | 4 | yes | certified | +0.00280 | 0.00149 | +0.00282 | certified | 0.00374 | -0.01219 | outside | room is not positive; largest term B |
| `t6083` | 2 | 4 | 4 | yes | certified | +0.00020 | 0.00115 | +0.00062 | certified | 0.00339 | -0.01566 | outside | room is not positive; largest term a |
| `t6085` | 2 | 3 | 3 | yes | certified | +0.00269 | 0.00123 | +0.00302 | certified | 0.00441 | -0.01511 | outside | room is not positive; largest term B |
| `t6088` | 2 | 4 | 4 | yes | certified | +0.00524 | 0.00156 | +0.00518 | certified | 0.00481 | -0.01455 | outside | room is not positive; largest term B |
| `t6090` | 1 | 4 | 4 | yes | certified | +0.00285 | 0.00151 | +0.00286 | certified | 0.00387 | -0.01453 | outside | room is not positive; largest term B |
| `t6093` | 2 | 4 | 4 | yes | certified | +0.00159 | 0.00118 | +0.00198 | certified | 0.00328 | -0.01291 | outside | room is not positive; largest term B |
| `t6095` | 2 | 3 | 3 | yes | certified | +0.00253 | 0.00143 | +0.00262 | certified | 0.00371 | -0.01295 | outside | room is not positive; largest term a |
| `t6096` | 1 | 3 | 3 | yes | certified | +0.00674 | 0.00122 | +0.00708 | certified | 0.00350 | -0.00899 | outside | room is not positive; largest term B |
| `t6098` | 2 | 5 | 5 | yes | certified | +0.00676 | 0.00105 | +0.00731 | certified | 0.00350 | -0.00819 | outside | room is not positive; largest term B |
| `t6099` | 1 | 5 | 5 | yes | certified | +0.00108 | 0.00099 | +0.00169 | certified | 0.00322 | -0.01408 | outside | room is not positive; largest term B |

## The 200 ports

| Cell | Port | m | Count | Agrees | Certification campaign | Its room | `h1` | Room 1 | Status 1 | `eps_peak` | Room 2 | New status | Reason |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6001` | 1 | 5 | 5 | yes | outside | -0.00833 | 0.00094 | -0.00766 | outside | 0.00549 | -0.03034 | outside | room is not positive; largest term a |
| `t6001` | 2 | 5 | 5 | yes | outside | -0.00105 | 0.00094 | -0.00038 | outside | 0.00473 | -0.02079 | outside | room is not positive; largest term a |
| `t6002` | 1 | 2 | 2 | yes | certified | +0.01033 | 0.00136 | +0.01051 | certified | 0.00443 | -0.00924 | outside | room is not positive; largest term B |
| `t6002` | 2 | 4 | 4 | yes | outside | -0.00907 | 0.00136 | -0.00889 | outside | 0.00044 | -0.01666 | outside | room is not positive; largest term a |
| `t6003` | 1 | 5 | 5 | yes | certified | +0.00319 | 0.00132 | +0.00341 | certified | 0.00400 | -0.01376 | outside | room is not positive; largest term B |
| `t6003` | 2 | 5 | 5 | yes | outside | -0.01130 | 0.00132 | -0.01108 | outside | 0.00557 | -0.03296 | outside | room is not positive; largest term a |
| `t6004` | 1 | 6 | 6 | yes | certified | +0.00375 | 0.00217 | +0.00298 | certified | 0.00329 | -0.01252 | outside | room is not positive; largest term B |
| `t6004` | 2 | 4 | 4 | yes | certified | +0.00573 | 0.00217 | +0.00496 | certified | 0.00373 | -0.01187 | outside | room is not positive; largest term B |
| `t6005` | 1 | 2 | 2 | yes | certified | +0.00473 | 0.00157 | +0.00466 | certified | 0.00440 | -0.01449 | outside | room is not positive; largest term B |
| `t6005` | 2 | 5 | 5 | yes | outside | -0.00823 | 0.00157 | -0.00830 | outside | 0.00541 | -0.03049 | outside | room is not positive; largest term a |
| `t6006` | 1 | 4 | 4 | yes | outside | -0.00986 | 0.00122 | -0.00952 | outside | 0.00560 | -0.03109 | outside | room is not positive; largest term a |
| `t6006` | 2 | 4 | 4 | yes | outside | -0.00276 | 0.00122 | -0.00241 | outside | 0.00298 | -0.01611 | outside | room is not positive; largest term a |
| `t6007` | 1 | 5 | 4 | no | outside | -0.00903 | 0.00169 | -0.00924 | outside | 0.00551 | -0.03209 | outside | room is not positive; largest term a |
| `t6007` | 2 | 3 | 3 | yes | outside | -0.00589 | 0.00169 | -0.00610 | outside | 0.00250 | -0.01993 | outside | room is not positive; largest term a |
| `t6008` | 1 | 3 | 3 | yes | certified | +0.00775 | 0.00176 | +0.00745 | certified | 0.00391 | -0.00998 | outside | room is not positive; largest term (20/17)*ell |
| `t6008` | 2 | 4 | 4 | yes | outside | -0.01024 | 0.00176 | -0.01053 | outside | 0.00244 | -0.02354 | outside | room is not positive; largest term a |
| `t6009` | 1 | 3 | 3 | yes | outside | -0.00588 | 0.00202 | -0.00647 | outside | 0.00193 | -0.01832 | outside | room is not positive; largest term a |
| `t6009` | 2 | 3 | 3 | yes | certified | +0.00680 | 0.00202 | +0.00620 | certified | 0.00384 | -0.01135 | outside | room is not positive; largest term B |
| `t6010` | 1 | 4 | 4 | yes | certified | +0.00416 | 0.00164 | +0.00400 | certified | 0.00478 | -0.01690 | outside | room is not positive; largest term B |
| `t6010` | 2 | 6 | 6 | yes | outside | -0.00109 | 0.00164 | -0.00124 | outside | 0.00456 | -0.02149 | outside | room is not positive; largest term B |
| `t6011` | 1 | 4 | 4 | yes | outside | +0.00932 | 0.00159 | +0.00923 | outside | 0.00388 | -0.00843 | outside | a rest state is outside the band; room is not positive; largest term B |
| `t6011` | 2 | 5 | 5 | yes | certified | +0.00516 | 0.00159 | +0.00507 | certified | 0.00359 | -0.01174 | outside | room is not positive; largest term B |
| `t6012` | 1 | 4 | 4 | yes | certified | +0.00895 | 0.00166 | +0.00878 | certified | 0.00365 | -0.00748 | outside | room is not positive; largest term B |
| `t6012` | 2 | 5 | 5 | yes | outside | -0.00759 | 0.00166 | -0.00776 | outside | 0.00476 | -0.02735 | outside | room is not positive; largest term a |
| `t6013` | 1 | 4 | 4 | yes | outside | -0.00554 | 0.00112 | -0.00508 | outside | 0.00205 | -0.01660 | outside | room is not positive; largest term a |
| `t6013` | 2 | 3 | 3 | yes | certified | +0.00592 | 0.00112 | +0.00638 | certified | 0.00405 | -0.01116 | outside | room is not positive; largest term B |
| `t6014` | 1 | 3 | 3 | yes | outside | -0.01070 | 0.00130 | -0.01045 | outside | 0.00184 | -0.02111 | outside | room is not positive; largest term a |
| `t6014` | 2 | 5 | 5 | yes | outside | -0.00804 | 0.00130 | -0.00779 | outside | 0.00451 | -0.02644 | outside | room is not positive; largest term a |
| `t6015` | 1 | 4 | 4 | yes | certified | +0.00464 | 0.00106 | +0.00517 | certified | 0.00445 | -0.01451 | outside | room is not positive; largest term B |
| `t6015` | 2 | 5 | 5 | yes | outside | -0.00660 | 0.00106 | -0.00607 | outside | 0.00463 | -0.02628 | outside | room is not positive; largest term a |
| `t6016` | 1 | 4 | 4 | yes | certified | +0.00129 | 0.00136 | +0.00147 | certified | 0.00399 | -0.01483 | outside | room is not positive; largest term B |
| `t6016` | 2 | 5 | 5 | yes | outside | -0.00454 | 0.00136 | -0.00436 | outside | 0.00495 | -0.02356 | outside | room is not positive; largest term a |
| `t6017` | 1 | 4 | 4 | yes | outside | -0.00062 | 0.00195 | -0.00113 | outside | 0.00458 | -0.02104 | outside | room is not positive; largest term B |
| `t6017` | 2 | 3 | 3 | yes | outside | -0.00035 | 0.00195 | -0.00086 | outside | 0.00320 | -0.01661 | outside | room is not positive; largest term a |
| `t6018` | 1 | 4 | 4 | yes | outside | -0.00586 | 0.00130 | -0.00561 | outside | 0.00555 | -0.02861 | outside | room is not positive; largest term a |
| `t6018` | 2 | 3 | 3 | yes | certified | +0.00548 | 0.00130 | +0.00573 | certified | 0.00453 | -0.01422 | outside | room is not positive; largest term B |
| `t6019` | 1 | 4 | 4 | yes | outside | -0.01866 | 0.00117 | -0.01826 | outside | 0.00553 | -0.04017 | outside | room is not positive; largest term a |
| `t6019` | 2 | 4 | 4 | yes | certified | +0.00132 | 0.00117 | +0.00171 | certified | 0.00334 | -0.01363 | outside | room is not positive; largest term B |
| `t6020` | 1 | 4 | 4 | yes | outside | -0.01358 | 0.00087 | -0.01282 | outside | 0.00553 | -0.03538 | outside | room is not positive; largest term a |
| `t6020` | 2 | 4 | 4 | yes | outside | -0.00282 | 0.00087 | -0.00206 | outside | 0.00452 | -0.02158 | outside | room is not positive; largest term B |
| `t6021` | 1 | 5 | 6 | no | outside | -0.01965 | 0.00183 | -0.02003 | outside | 0.00056 | -0.02748 | outside | room is not positive; largest term a |
| `t6021` | 2 | 5 | 5 | yes | outside | -0.00274 | 0.00183 | -0.00312 | outside | 0.00505 | -0.02404 | outside | room is not positive; largest term a |
| `t6022` | 1 | 3 | 3 | yes | outside | -0.00755 | 0.00108 | -0.00704 | outside | 0.00167 | -0.01698 | outside | room is not positive; largest term a |
| `t6022` | 2 | 4 | 4 | yes | outside | -0.01437 | 0.00108 | -0.01386 | outside | 0.00225 | -0.02555 | outside | room is not positive; largest term a |
| `t6023` | 1 | 4 | 4 | yes | outside | -0.00674 | 0.00137 | -0.00657 | outside | 0.00435 | -0.02505 | outside | room is not positive; largest term a |
| `t6023` | 2 | 3 | 3 | yes | outside | -0.00655 | 0.00137 | -0.00637 | outside | 0.00117 | -0.01533 | outside | room is not positive; largest term a |
| `t6024` | 1 | 3 | 3 | yes | outside | -0.00771 | 0.00195 | -0.00822 | outside | 0.00208 | -0.02082 | outside | room is not positive; largest term a |
| `t6024` | 2 | 6 | 5 | no | outside | -0.01231 | 0.00195 | -0.01282 | outside | 0.00553 | -0.03577 | outside | room is not positive; largest term a |
| `t6025` | 1 | 4 | 4 | yes | certified | +0.00008 | 0.00094 | +0.00075 | certified | 0.00347 | -0.01585 | outside | room is not positive; largest term B |
| `t6025` | 2 | 4 | 4 | yes | outside | -0.00683 | 0.00094 | -0.00616 | outside | 0.00501 | -0.02740 | outside | room is not positive; largest term a |
| `t6026` | 1 | 4 | 4 | yes | outside | -0.00438 | 0.00174 | -0.00466 | outside | 0.00313 | -0.01976 | outside | room is not positive; largest term a |
| `t6026` | 2 | 4 | 4 | yes | outside | -0.00446 | 0.00174 | -0.00473 | outside | 0.00215 | -0.01692 | outside | room is not positive; largest term a |
| `t6027` | 1 | 5 | 5 | yes | outside | -0.00346 | 0.00171 | -0.00369 | outside | 0.00488 | -0.02403 | outside | room is not positive; largest term a |
| `t6027` | 2 | 3 | 3 | yes | certified | +0.00021 | 0.00171 | -0.00003 | outside | 0.00404 | -0.01786 | outside | room is not positive; largest term B |
| `t6028` | 1 | 5 | 5 | yes | outside | -0.00303 | 0.00106 | -0.00250 | outside | 0.00483 | -0.02276 | outside | room is not positive; largest term a |
| `t6028` | 2 | 4 | 4 | yes | certified | +0.00523 | 0.00106 | +0.00575 | certified | 0.00445 | -0.01334 | outside | room is not positive; largest term B |
| `t6029` | 1 | 4 | 4 | yes | outside | -0.00300 | 0.00087 | -0.00225 | outside | 0.00291 | -0.01664 | outside | room is not positive; largest term a |
| `t6029` | 2 | 5 | 5 | yes | outside | -0.00989 | 0.00087 | -0.00914 | outside | 0.00526 | -0.03056 | outside | room is not positive; largest term a |
| `t6030` | 1 | 3 | 3 | yes | certified | +0.00345 | 0.00200 | +0.00287 | certified | 0.00365 | -0.01390 | outside | room is not positive; largest term B |
| `t6030` | 2 | 4 | 5 | no | outside | -0.01378 | 0.00200 | -0.01436 | outside | 0.00106 | -0.02336 | outside | room is not positive; largest term a |
| `t6031` | 1 | 4 | 4 | yes | certified | +0.00247 | 0.00094 | +0.00315 | certified | 0.00439 | -0.01584 | outside | room is not positive; largest term B |
| `t6031` | 2 | 5 | 5 | yes | outside | -0.00545 | 0.00094 | -0.00477 | outside | 0.00241 | -0.01783 | outside | room is not positive; largest term a |
| `t6032` | 1 | 3 | 3 | yes | certified | +0.00566 | 0.00155 | +0.00562 | certified | 0.00356 | -0.01026 | outside | room is not positive; largest term B |
| `t6032` | 2 | 4 | 4 | yes | certified | +0.00562 | 0.00155 | +0.00558 | certified | 0.00397 | -0.01152 | outside | room is not positive; largest term B |
| `t6033` | 1 | 4 | 4 | yes | outside | -0.00728 | 0.00110 | -0.00680 | outside | 0.00217 | -0.01903 | outside | room is not positive; largest term a |
| `t6033` | 2 | 2 | 2 | yes | outside | -0.00206 | 0.00110 | -0.00158 | outside | 0.00278 | -0.01563 | outside | room is not positive; largest term a |
| `t6034` | 1 | 4 | 4 | yes | outside | -0.00473 | 0.00135 | -0.00454 | outside | 0.00270 | -0.01786 | outside | room is not positive; largest term a |
| `t6034` | 2 | 5 | 5 | yes | outside | -0.01212 | 0.00135 | -0.01193 | outside | 0.00547 | -0.03356 | outside | room is not positive; largest term a |
| `t6035` | 1 | 5 | 5 | yes | outside | -0.01363 | 0.00100 | -0.01302 | outside | 0.00545 | -0.03517 | outside | room is not positive; largest term a |
| `t6035` | 2 | 5 | 5 | yes | outside | -0.00530 | 0.00100 | -0.00469 | outside | 0.00545 | -0.02684 | outside | room is not positive; largest term a |
| `t6036` | 1 | 5 | 5 | yes | outside | -0.00999 | 0.00123 | -0.00966 | outside | 0.00545 | -0.03175 | outside | room is not positive; largest term a |
| `t6036` | 2 | 4 | 4 | yes | outside | -0.00720 | 0.00123 | -0.00687 | outside | 0.00538 | -0.02872 | outside | room is not positive; largest term B |
| `t6037` | 1 | 4 | 4 | yes | certified | +0.00115 | 0.00126 | +0.00145 | certified | 0.00283 | -0.01112 | outside | room is not positive; largest term B |
| `t6037` | 2 | 4 | 4 | yes | certified | +0.00122 | 0.00126 | +0.00151 | certified | 0.00447 | -0.01600 | outside | room is not positive; largest term a |
| `t6038` | 1 | 4 | 4 | yes | certified | +0.00019 | 0.00164 | +0.00004 | certified | 0.00432 | -0.01862 | outside | room is not positive; largest term B |
| `t6038` | 2 | 4 | 4 | yes | outside | -0.00532 | 0.00164 | -0.00547 | outside | 0.00252 | -0.01872 | outside | room is not positive; largest term a |
| `t6039` | 1 | 3 | 3 | yes | outside | -0.00095 | 0.00111 | -0.00048 | outside | 0.00326 | -0.01604 | outside | room is not positive; largest term a |
| `t6039` | 2 | 3 | 3 | yes | outside | -0.00068 | 0.00111 | -0.00021 | outside | 0.00256 | -0.01367 | outside | room is not positive; largest term a |
| `t6040` | 1 | 5 | 5 | yes | outside | -0.01664 | 0.00185 | -0.01704 | outside | 0.00479 | -0.03666 | outside | room is not positive; largest term a |
| `t6040` | 2 | 5 | 5 | yes | certified | +0.00319 | 0.00185 | +0.00279 | certified | 0.00325 | -0.01219 | outside | room is not positive; largest term B |
| `t6041` | 1 | 5 | 5 | yes | outside | -0.00304 | 0.00179 | -0.00337 | outside | 0.00418 | -0.02214 | outside | room is not positive; largest term B |
| `t6041` | 2 | 6 | 6 | yes | outside | -0.00701 | 0.00179 | -0.00734 | outside | 0.00506 | -0.02873 | outside | room is not positive; largest term a |
| `t6042` | 1 | 4 | 4 | yes | outside | -0.00852 | 0.00181 | -0.00887 | outside | 0.00122 | -0.01777 | outside | room is not positive; largest term a |
| `t6042` | 2 | 5 | 5 | yes | certified | +0.00341 | 0.00181 | +0.00306 | certified | 0.00453 | -0.01579 | outside | room is not positive; largest term B |
| `t6043` | 1 | 5 | 5 | yes | outside | -0.01251 | 0.00133 | -0.01230 | outside | 0.00502 | -0.03262 | outside | room is not positive; largest term a |
| `t6043` | 2 | 5 | 5 | yes | certified | +0.00597 | 0.00133 | +0.00618 | certified | 0.00360 | -0.00987 | outside | room is not positive; largest term B |
| `t6044` | 1 | 2 | 2 | yes | outside | -0.01618 | 0.00198 | -0.01673 | outside | 0.00050 | -0.02397 | outside | room is not positive; largest term a |
| `t6044` | 2 | 3 | 3 | yes | outside | -0.00078 | 0.00198 | -0.00133 | outside | 0.00268 | -0.01511 | outside | room is not positive; largest term a |
| `t6045` | 1 | 4 | 4 | yes | outside | -0.00208 | 0.00087 | -0.00133 | outside | 0.00517 | -0.02317 | outside | room is not positive; largest term a |
| `t6045` | 2 | 4 | 4 | yes | certified | +0.00075 | 0.00087 | +0.00150 | certified | 0.00397 | -0.01676 | outside | room is not positive; largest term B |
| `t6046` | 1 | 3 | 3 | yes | outside | -0.00712 | 0.00108 | -0.00660 | outside | 0.00184 | -0.01815 | outside | room is not positive; largest term a |
| `t6046` | 2 | 4 | 4 | yes | outside | -0.01307 | 0.00108 | -0.01256 | outside | 0.00112 | -0.02194 | outside | room is not positive; largest term a |
| `t6047` | 1 | 4 | 4 | yes | outside | -0.00217 | 0.00122 | -0.00183 | outside | 0.00290 | -0.01572 | outside | room is not positive; largest term a |
| `t6047` | 2 | 5 | 5 | yes | outside | -0.00630 | 0.00122 | -0.00595 | outside | 0.00498 | -0.02608 | outside | room is not positive; largest term a |
| `t6048` | 1 | 5 | 5 | yes | outside | -0.01163 | 0.00123 | -0.01130 | outside | 0.00588 | -0.03434 | outside | room is not positive; largest term a |
| `t6048` | 2 | 4 | 4 | yes | outside | -0.00685 | 0.00123 | -0.00652 | outside | 0.00281 | -0.02036 | outside | room is not positive; largest term a |
| `t6049` | 1 | 4 | 4 | yes | outside | -0.01387 | 0.00126 | -0.01358 | outside | 0.00548 | -0.03581 | outside | room is not positive; largest term a |
| `t6049` | 2 | 4 | 4 | yes | outside | -0.00062 | 0.00126 | -0.00032 | outside | 0.00436 | -0.01920 | outside | room is not positive; largest term B |
| `t6050` | 1 | 3 | 3 | yes | outside | -0.01381 | 0.00095 | -0.01314 | outside | 0.00069 | -0.02102 | outside | room is not positive; largest term a |
| `t6050` | 2 | 4 | 4 | yes | certified | +0.00392 | 0.00095 | +0.00459 | certified | 0.00294 | -0.01005 | outside | room is not positive; largest term B |
| `t6051` | 1 | 4 | 4 | yes | outside | +0.00119 | 0.00130 | +0.00143 | outside | 0.00304 | -0.01390 | outside | a rest state is outside the band; room is not positive; largest term a |
| `t6051` | 2 | 3 | 3 | yes | certified | +0.00887 | 0.00130 | +0.00911 | certified | 0.00377 | -0.00842 | outside | room is not positive; largest term B |
| `t6052` | 1 | 4 | 4 | yes | certified | +0.00218 | 0.00094 | +0.00285 | certified | 0.00372 | -0.01468 | outside | room is not positive; largest term B |
| `t6052` | 2 | 4 | 4 | yes | outside | -0.00716 | 0.00094 | -0.00649 | outside | 0.00302 | -0.02191 | outside | room is not positive; largest term a |
| `t6053` | 1 | 3 | 3 | yes | outside | -0.00969 | 0.00170 | -0.00992 | outside | 0.00483 | -0.03001 | outside | room is not positive; largest term B |
| `t6053` | 2 | 4 | 4 | yes | outside | -0.00253 | 0.00170 | -0.00276 | outside | 0.00184 | -0.01388 | outside | room is not positive; largest term a |
| `t6054` | 1 | 4 | 4 | yes | outside | -0.00348 | 0.00098 | -0.00285 | outside | 0.00293 | -0.01768 | outside | room is not positive; largest term a |
| `t6054` | 2 | 4 | 4 | yes | outside | -0.01247 | 0.00098 | -0.01184 | outside | 0.00521 | -0.03350 | outside | room is not positive; largest term a |
| `t6055` | 1 | 6 | 6 | yes | certified | +0.00156 | 0.00181 | +0.00121 | certified | 0.00393 | -0.01577 | outside | room is not positive; largest term a |
| `t6055` | 2 | 5 | 5 | yes | outside | -0.01222 | 0.00181 | -0.01258 | outside | 0.00084 | -0.02030 | outside | room is not positive; largest term a |
| `t6056` | 1 | 5 | 5 | yes | certified | +0.00127 | 0.00125 | +0.00158 | certified | 0.00487 | -0.01852 | outside | room is not positive; largest term B |
| `t6056` | 2 | 3 | 3 | yes | outside | -0.01173 | 0.00125 | -0.01142 | outside | 0.00544 | -0.03325 | outside | room is not positive; largest term a |
| `t6057` | 1 | 6 | 6 | yes | outside | -0.01342 | 0.00103 | -0.01285 | outside | 0.00557 | -0.03501 | outside | room is not positive; largest term a |
| `t6057` | 2 | 5 | 5 | yes | outside | -0.00325 | 0.00103 | -0.00268 | outside | 0.00341 | -0.01836 | outside | room is not positive; largest term B |
| `t6058` | 1 | 4 | 4 | yes | outside | -0.01282 | 0.00121 | -0.01247 | outside | 0.00522 | -0.03275 | outside | room is not positive; largest term a |
| `t6058` | 2 | 4 | 4 | yes | certified | +0.00370 | 0.00121 | +0.00405 | certified | 0.00358 | -0.01130 | outside | room is not positive; largest term B |
| `t6059` | 1 | 4 | 4 | yes | outside | -0.00395 | 0.00105 | -0.00341 | outside | 0.00275 | -0.01806 | outside | room is not positive; largest term a |
| `t6059` | 2 | 5 | 5 | yes | outside | -0.00540 | 0.00105 | -0.00486 | outside | 0.00247 | -0.01867 | outside | room is not positive; largest term a |
| `t6060` | 1 | 5 | 5 | yes | outside | -0.00997 | 0.00105 | -0.00943 | outside | 0.00119 | -0.01893 | outside | room is not positive; largest term a |
| `t6060` | 2 | 4 | 4 | yes | outside | -0.00425 | 0.00105 | -0.00371 | outside | 0.00454 | -0.02326 | outside | room is not positive; largest term a |
| `t6061` | 1 | 4 | 4 | yes | outside | -0.00891 | 0.00123 | -0.00859 | outside | 0.00164 | -0.01795 | outside | room is not positive; largest term a |
| `t6061` | 2 | 3 | 3 | yes | certified | +0.00343 | 0.00123 | +0.00376 | certified | 0.00418 | -0.01323 | outside | room is not positive; largest term B |
| `t6062` | 1 | 4 | 4 | yes | outside | -0.00103 | 0.00155 | -0.00108 | outside | 0.00480 | -0.02136 | outside | room is not positive; largest term B |
| `t6062` | 2 | 3 | 3 | yes | outside | -0.01413 | 0.00155 | -0.01418 | outside | 0.00032 | -0.02101 | outside | room is not positive; largest term a |
| `t6063` | 1 | 2 | 2 | yes | certified | +0.00746 | 0.00117 | +0.00786 | certified | 0.00392 | -0.01011 | outside | room is not positive; largest term B |
| `t6063` | 2 | 4 | 3 | no | outside | -0.01285 | 0.00117 | -0.01245 | outside | 0.00603 | -0.03675 | outside | room is not positive; largest term a |
| `t6064` | 1 | 5 | 5 | yes | outside | -0.00624 | 0.00119 | -0.00586 | outside | 0.00085 | -0.01284 | outside | room is not positive; largest term a |
| `t6064` | 2 | 3 | 3 | yes | outside | -0.00870 | 0.00119 | -0.00832 | outside | 0.00216 | -0.01923 | outside | room is not positive; largest term a |
| `t6065` | 1 | 4 | 4 | yes | certified | +0.01277 | 0.00199 | +0.01222 | certified | 0.00374 | -0.00483 | outside | room is not positive; largest term B |
| `t6065` | 2 | 3 | 3 | yes | outside | -0.00718 | 0.00199 | -0.00774 | outside | 0.00548 | -0.03001 | outside | room is not positive; largest term a |
| `t6066` | 1 | 5 | 5 | yes | outside | -0.00667 | 0.00126 | -0.00637 | outside | 0.00526 | -0.02716 | outside | room is not positive; largest term a |
| `t6066` | 2 | 4 | 4 | yes | outside | -0.00761 | 0.00126 | -0.00731 | outside | 0.00546 | -0.02871 | outside | room is not positive; largest term a |
| `t6067` | 1 | 4 | 4 | yes | outside | -0.00859 | 0.00199 | -0.00916 | outside | 0.00150 | -0.01906 | outside | room is not positive; largest term a |
| `t6067` | 2 | 3 | 3 | yes | certified | +0.00518 | 0.00199 | +0.00461 | certified | 0.00425 | -0.01355 | outside | room is not positive; largest term B |
| `t6068` | 1 | 4 | 4 | yes | outside | -0.00318 | 0.00099 | -0.00256 | outside | 0.00532 | -0.02489 | outside | room is not positive; largest term a |
| `t6068` | 2 | 2 | 2 | yes | certified | +0.00448 | 0.00099 | +0.00510 | certified | 0.00471 | -0.01542 | outside | room is not positive; largest term B |
| `t6069` | 1 | 5 | 5 | yes | outside | -0.01591 | 0.00139 | -0.01577 | outside | 0.00057 | -0.02352 | outside | room is not positive; largest term a |
| `t6069` | 2 | 4 | 5 | no | outside | -0.01204 | 0.00139 | -0.01190 | outside | 0.00045 | -0.01929 | outside | room is not positive; largest term a |
| `t6070` | 1 | 5 | 5 | yes | outside | -0.01466 | 0.00141 | -0.01455 | outside | 0.00524 | -0.03592 | outside | room is not positive; largest term a |
| `t6070` | 2 | 4 | 4 | yes | outside | -0.00633 | 0.00141 | -0.00622 | outside | 0.00242 | -0.01911 | outside | room is not positive; largest term a |
| `t6071` | 1 | 2 | 2 | yes | outside | -0.00282 | 0.00085 | -0.00204 | outside | 0.00386 | -0.02025 | outside | room is not positive; largest term B |
| `t6071` | 2 | 5 | 5 | yes | outside | -0.00583 | 0.00085 | -0.00504 | outside | 0.00485 | -0.02621 | outside | room is not positive; largest term a |
| `t6072` | 1 | 3 | 4 | no | outside | -0.02138 | 0.00138 | -0.02122 | outside | 0.00050 | -0.02762 | outside | room is not positive; largest term a |
| `t6072` | 2 | 4 | 4 | yes | outside | -0.00471 | 0.00138 | -0.00455 | outside | 0.00448 | -0.02291 | outside | room is not positive; largest term a |
| `t6073` | 1 | 4 | 4 | yes | outside | -0.01029 | 0.00168 | -0.01049 | outside | 0.00179 | -0.02124 | outside | room is not positive; largest term a |
| `t6073` | 2 | 5 | 5 | yes | outside | -0.01172 | 0.00168 | -0.01191 | outside | 0.00054 | -0.01891 | outside | room is not positive; largest term a |
| `t6074` | 1 | 3 | 3 | yes | certified | +0.00907 | 0.00079 | +0.00992 | certified | 0.00463 | -0.01058 | outside | room is not positive; largest term B |
| `t6074` | 2 | 2 | 3 | no | outside | -0.00926 | 0.00079 | -0.00841 | outside | 0.00488 | -0.02966 | outside | room is not positive; largest term a |
| `t6075` | 1 | 3 | 3 | yes | outside | -0.00228 | 0.00155 | -0.00233 | outside | 0.00366 | -0.01937 | outside | room is not positive; largest term B |
| `t6075` | 2 | 4 | 4 | yes | certified | +0.00789 | 0.00155 | +0.00783 | certified | 0.00400 | -0.01023 | outside | room is not positive; largest term B |
| `t6076` | 1 | 4 | 4 | yes | certified | +0.00199 | 0.00093 | +0.00267 | certified | 0.00369 | -0.01428 | outside | room is not positive; largest term B |
| `t6076` | 2 | 4 | 4 | yes | outside | -0.00272 | 0.00093 | -0.00204 | outside | 0.00315 | -0.01739 | outside | room is not positive; largest term a |
| `t6077` | 1 | 5 | 5 | yes | certified | +0.00441 | 0.00140 | +0.00455 | certified | 0.00336 | -0.01026 | outside | room is not positive; largest term B |
| `t6077` | 2 | 5 | 5 | yes | certified | +0.00605 | 0.00140 | +0.00619 | certified | 0.00420 | -0.01114 | outside | room is not positive; largest term B |
| `t6078` | 1 | 4 | 4 | yes | outside | -0.00906 | 0.00145 | -0.00899 | outside | 0.00212 | -0.01953 | outside | room is not positive; largest term a |
| `t6078` | 2 | 5 | 5 | yes | outside | -0.00570 | 0.00145 | -0.00564 | outside | 0.00496 | -0.02469 | outside | room is not positive; largest term B |
| `t6079` | 1 | 4 | 4 | yes | certified | +0.00722 | 0.00151 | +0.00721 | certified | 0.00432 | -0.01173 | outside | room is not positive; largest term B |
| `t6079` | 2 | 4 | 4 | yes | certified | +0.00048 | 0.00151 | +0.00048 | certified | 0.00355 | -0.01614 | outside | room is not positive; largest term B |
| `t6080` | 1 | 4 | 4 | yes | outside | -0.00380 | 0.00123 | -0.00346 | outside | 0.00512 | -0.02408 | outside | room is not positive; largest term a |
| `t6080` | 2 | 3 | 3 | yes | certified | +0.00075 | 0.00123 | +0.00108 | certified | 0.00333 | -0.01417 | outside | room is not positive; largest term B |
| `t6081` | 1 | 4 | 4 | yes | certified | +0.00069 | 0.00108 | +0.00120 | certified | 0.00440 | -0.01711 | outside | room is not positive; largest term B |
| `t6081` | 2 | 4 | 4 | yes | outside | -0.00111 | 0.00108 | -0.00060 | outside | 0.00359 | -0.01647 | outside | room is not positive; largest term a |
| `t6082` | 1 | 5 | 5 | yes | outside | -0.00695 | 0.00149 | -0.00693 | outside | 0.00454 | -0.02434 | outside | room is not positive; largest term a |
| `t6082` | 2 | 4 | 4 | yes | certified | +0.00280 | 0.00149 | +0.00282 | certified | 0.00374 | -0.01219 | outside | room is not positive; largest term B |
| `t6083` | 1 | 4 | 4 | yes | outside | -0.00926 | 0.00115 | -0.00883 | outside | 0.00150 | -0.01946 | outside | room is not positive; largest term a |
| `t6083` | 2 | 4 | 4 | yes | certified | +0.00020 | 0.00115 | +0.00062 | certified | 0.00339 | -0.01566 | outside | room is not positive; largest term a |
| `t6084` | 1 | 4 | 4 | yes | outside | -0.00305 | 0.00112 | -0.00260 | outside | 0.00278 | -0.01554 | outside | room is not positive; largest term a |
| `t6084` | 2 | 4 | 4 | yes | outside | -0.01440 | 0.00112 | -0.01394 | outside | 0.00578 | -0.03589 | outside | room is not positive; largest term a |
| `t6085` | 1 | 4 | 4 | yes | outside | -0.00186 | 0.00123 | -0.00153 | outside | 0.00451 | -0.01996 | outside | room is not positive; largest term a |
| `t6085` | 2 | 3 | 3 | yes | certified | +0.00269 | 0.00123 | +0.00302 | certified | 0.00441 | -0.01511 | outside | room is not positive; largest term B |
| `t6086` | 1 | 5 | 5 | yes | outside | -0.00064 | 0.00176 | -0.00093 | outside | 0.00299 | -0.01574 | outside | room is not positive; largest term a |
| `t6086` | 2 | 4 | 4 | yes | outside | -0.01165 | 0.00176 | -0.01194 | outside | 0.00051 | -0.01934 | outside | room is not positive; largest term a |
| `t6087` | 1 | 4 | 5 | no | outside | -0.01078 | 0.00105 | -0.01024 | outside | 0.00086 | -0.01826 | outside | room is not positive; largest term a |
| `t6087` | 2 | 4 | 4 | yes | outside | -0.00509 | 0.00105 | -0.00454 | outside | 0.00522 | -0.02564 | outside | room is not positive; largest term a |
| `t6088` | 1 | 5 | 5 | yes | outside | -0.00220 | 0.00156 | -0.00226 | outside | 0.00445 | -0.02089 | outside | room is not positive; largest term a |
| `t6088` | 2 | 4 | 4 | yes | certified | +0.00524 | 0.00156 | +0.00518 | certified | 0.00481 | -0.01455 | outside | room is not positive; largest term B |
| `t6089` | 1 | 5 | 5 | yes | outside | -0.01218 | 0.00188 | -0.01262 | outside | 0.00540 | -0.03473 | outside | room is not positive; largest term a |
| `t6089` | 2 | 4 | 3 | no | outside | -0.01151 | 0.00188 | -0.01195 | outside | 0.00472 | -0.03203 | outside | room is not positive; largest term a |
| `t6090` | 1 | 4 | 4 | yes | certified | +0.00285 | 0.00151 | +0.00286 | certified | 0.00387 | -0.01453 | outside | room is not positive; largest term B |
| `t6090` | 2 | 4 | 4 | yes | outside | -0.00259 | 0.00151 | -0.00259 | outside | 0.00486 | -0.02296 | outside | room is not positive; largest term a |
| `t6091` | 1 | 6 | 6 | yes | outside | -0.00660 | 0.00121 | -0.00625 | outside | 0.00453 | -0.02561 | outside | room is not positive; largest term a |
| `t6091` | 2 | 5 | 5 | yes | outside | -0.00637 | 0.00121 | -0.00602 | outside | 0.00449 | -0.02529 | outside | room is not positive; largest term a |
| `t6092` | 1 | 3 | 3 | yes | outside | -0.00965 | 0.00138 | -0.00949 | outside | 0.00541 | -0.03013 | outside | room is not positive; largest term a |
| `t6092` | 2 | 3 | 3 | yes | outside | -0.00120 | 0.00138 | -0.00104 | outside | 0.00271 | -0.01358 | outside | room is not positive; largest term a |
| `t6093` | 1 | 4 | 4 | yes | outside | -0.01438 | 0.00118 | -0.01399 | outside | 0.00052 | -0.02059 | outside | room is not positive; largest term a |
| `t6093` | 2 | 4 | 4 | yes | certified | +0.00159 | 0.00118 | +0.00198 | certified | 0.00328 | -0.01291 | outside | room is not positive; largest term B |
| `t6094` | 1 | 4 | 4 | yes | outside | -0.00217 | 0.00140 | -0.00204 | outside | 0.00472 | -0.02204 | outside | room is not positive; largest term a |
| `t6094` | 2 | 5 | 5 | yes | outside | -0.01072 | 0.00140 | -0.01059 | outside | 0.00475 | -0.03066 | outside | room is not positive; largest term a |
| `t6095` | 1 | 3 | 3 | yes | outside | -0.00373 | 0.00143 | -0.00364 | outside | 0.00321 | -0.01773 | outside | room is not positive; largest term a |
| `t6095` | 2 | 3 | 3 | yes | certified | +0.00253 | 0.00143 | +0.00262 | certified | 0.00371 | -0.01295 | outside | room is not positive; largest term a |
| `t6096` | 1 | 3 | 3 | yes | certified | +0.00674 | 0.00122 | +0.00708 | certified | 0.00350 | -0.00899 | outside | room is not positive; largest term B |
| `t6096` | 2 | 5 | 5 | yes | outside | -0.01059 | 0.00122 | -0.01025 | outside | 0.00508 | -0.03107 | outside | room is not positive; largest term a |
| `t6097` | 1 | 3 | 4 | no | outside | -0.00902 | 0.00180 | -0.00936 | outside | 0.00034 | -0.01621 | outside | room is not positive; largest term a |
| `t6097` | 2 | 5 | 5 | yes | outside | -0.00098 | 0.00180 | -0.00133 | outside | 0.00477 | -0.02149 | outside | room is not positive; largest term B |
| `t6098` | 1 | 3 | 3 | yes | outside | -0.00642 | 0.00105 | -0.00587 | outside | 0.00179 | -0.01625 | outside | room is not positive; largest term a |
| `t6098` | 2 | 5 | 5 | yes | certified | +0.00676 | 0.00105 | +0.00731 | certified | 0.00350 | -0.00819 | outside | room is not positive; largest term B |
| `t6099` | 1 | 5 | 5 | yes | certified | +0.00108 | 0.00099 | +0.00169 | certified | 0.00322 | -0.01408 | outside | room is not positive; largest term B |
| `t6099` | 2 | 6 | 6 | yes | outside | -0.00800 | 0.00099 | -0.00739 | outside | 0.00502 | -0.02856 | outside | room is not positive; largest term a |
| `t6100` | 1 | 6 | 6 | yes | outside | -0.00805 | 0.00169 | -0.00827 | outside | 0.00437 | -0.02683 | outside | room is not positive; largest term a |
| `t6100` | 2 | 5 | 5 | yes | outside | -0.00062 | 0.00169 | -0.00083 | outside | 0.00266 | -0.01427 | outside | room is not positive; largest term a |

## Traces

- **Extraction.** The rows and the compact trace of a run are made by `../certification/cert_run.py`, SHA-256 `e389e8fddb1dee43a1e9e0c26730a52da6ed9c85c2c36ebaf99e005076be5c43`: the value of `manifest.json`, checked at each run. The charge of each mirror is measured by `uncond_run.py` on the compact trace.
- **Traces.** The compact traces are in the private repository `HevisNico/kernel-R-circuit`, folder `08-certification-unconditional-traces/`; 202 of the 202 runs with a result have the SHA-256 of their trace in their public metadata.
- **Reproduction.** Every run of this campaign is without noise and made once.
