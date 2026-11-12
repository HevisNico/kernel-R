# Status 3 of amendment 1: report

Written by `uncond_amend1.py report` under [`AMENDMENT_1.md`](AMENDMENT_1.md), after [`REPORT.md`](REPORT.md), which gives statuses 1 and 2 as registered in [`PREDICTION.md`](PREDICTION.md). One row per port: [`ports_amendment1.csv`](ports_amendment1.csv). The certification campaign is in [`../certification/`](../certification/REPORT.md); nothing of it is changed.

## Summary

1. **Level of each cell (condition 1):** measured on each of the 100 test cells by its own leak scan (100 evaluable). Its `mu` is inside the envelope of the six calibration cells for 100 cells; its whole bracket is inside for 67. With the level of its own cell alone (status 1), 58 ports are certified.
2. **Independent gain (condition 2):** on silent reads, the gain inferred from the peak agrees with the charge that the mirror delivers over the whole pulse; on reads with a FIRE, the early gain agrees with the charge delivered up to 0.75 unit. After one constant per port the largest distance is `eps3`: median 0.00075, largest 0.00110. The registered measure, over the whole pulse for every read, gives `eps_peak`: median 0.00393, largest 0.00603, because the current of the mirror changes after a FIRE.
3. **Certified with both measures (status 3):** 37 ports of 200; the count is the predicted one on 37 of them. By the registered status 2: 0 ports.
4. **Against the certification campaign:** of its 59 ports certified under condition, 37 are certified by status 3 and 22 are not (14: room is not positive; largest term a, 8: room is not positive; largest term B); 0 ports that it did not certify are certified by status 3.
5. **What stays conditional:** it is a simulation; the level of a cell is bracketed once, on port 1, and used for its two ports; `eps3` is measured without noise and applied to the noisy reads of the same port; the gain of a read with a FIRE is checked by the current up to 0.75 unit only, and from there to the end of the pulse it rests on `kappa` and `eps_kappa`; `kappa`, `d0`, `eps_kappa` and the centre `mu` come from the certification campaign; the count of a port comes from one noisy run.

## Predictions of amendment 1

| | Prediction | Measured | Verdict |
|---|---|---|---|
| U8 | the median `eps3` is between 0.0004 and 0.002 | 0.00075 over 200 ports | holds |
| U9 | status 3 certifies 35 to 58 ports | 37 of 200 | holds |
| U10 | no port certified by status 3 has its count contradicted | 0 of 37 | holds |

**F1, a port certified by status 3 whose count is contradicted:** none.

## The two measures of the gain

| | Registered (`eps_peak`, status 2) | Amendment 1 (`eps3`, status 3) |
|---|---|---|
| Bound of a port | median 0.00393, largest 0.00603 | smallest 0.00048, median 0.00075, largest 0.00110 |
| Silent reads, whole pulse | median 0.00035 | the same: median 0.00035 |
| Reads with a FIRE | whole pulse: median 0.00383, largest 0.00593 | up to 0.75 unit: median 0.00065, largest 0.00100 |
| Silent reads, up to 0.75 unit | — | median 0.00036, largest 0.00065 |
| Bound of a cell in its leak scan | `eps_scan`: median 0.00550 | `eps3_scan`: median 0.00076, largest 0.00096 |
| Reads with a FIRE earlier than 0.76, left out | 0 | 0 |

## The four statuses, side by side

| | Certification campaign | Status 1: level of the cell | Status 2: and gain, as registered | Status 3: and gain, amendment 1 |
|---|---|---|---|---|
| Room, median | -0.00410 | -0.00370 | -0.01905 | -0.00688 |
| Certified | 59 | 58 | 0 | 37 |
| Certified with the count contradicted | 0 | 0 | 0 | 0 |

| Certification campaign | Status 3 | Ports |
|---|---|---|
| outside | outside | 141 |
| certified | certified | 37 |
| certified | outside | 22 |

## The 59 ports certified under condition by the certification campaign

| Cell | Port | m | Count | Agrees | Certification campaign | Its room | Status 1 | Room 1 | Status 2 | Room 2 | `eps3` | Room 3 | Status 3 | Reason |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6002` | 1 | 2 | 2 | yes | certified | +0.01033 | certified | +0.01051 | outside | -0.00924 | 0.00052 | +0.00841 | certified | — |
| `t6003` | 1 | 5 | 5 | yes | certified | +0.00319 | certified | +0.00341 | outside | -0.01376 | 0.00096 | +0.00043 | certified | — |
| `t6004` | 1 | 6 | 6 | yes | certified | +0.00375 | certified | +0.00298 | outside | -0.01252 | 0.00094 | -0.00085 | outside | room is not positive; largest term B |
| `t6004` | 2 | 4 | 4 | yes | certified | +0.00573 | certified | +0.00496 | outside | -0.01187 | 0.00076 | +0.00167 | certified | — |
| `t6005` | 1 | 2 | 2 | yes | certified | +0.00473 | certified | +0.00466 | outside | -0.01449 | 0.00051 | +0.00259 | certified | — |
| `t6008` | 1 | 3 | 3 | yes | certified | +0.00775 | certified | +0.00745 | outside | -0.00998 | 0.00061 | +0.00500 | certified | — |
| `t6009` | 2 | 3 | 3 | yes | certified | +0.00680 | certified | +0.00620 | outside | -0.01135 | 0.00063 | +0.00359 | certified | — |
| `t6010` | 1 | 4 | 4 | yes | certified | +0.00416 | certified | +0.00400 | outside | -0.01690 | 0.00080 | +0.00078 | certified | — |
| `t6011` | 2 | 5 | 5 | yes | certified | +0.00516 | certified | +0.00507 | outside | -0.01174 | 0.00087 | +0.00164 | certified | — |
| `t6012` | 1 | 4 | 4 | yes | certified | +0.00895 | certified | +0.00878 | outside | -0.00748 | 0.00073 | +0.00586 | certified | — |
| `t6013` | 2 | 3 | 3 | yes | certified | +0.00592 | certified | +0.00638 | outside | -0.01116 | 0.00066 | +0.00359 | certified | — |
| `t6015` | 1 | 4 | 4 | yes | certified | +0.00464 | certified | +0.00517 | outside | -0.01451 | 0.00083 | +0.00183 | certified | — |
| `t6016` | 1 | 4 | 4 | yes | certified | +0.00129 | certified | +0.00147 | outside | -0.01483 | 0.00072 | -0.00071 | outside | room is not positive; largest term a |
| `t6018` | 2 | 3 | 3 | yes | certified | +0.00548 | certified | +0.00573 | outside | -0.01422 | 0.00068 | +0.00287 | certified | — |
| `t6019` | 2 | 4 | 4 | yes | certified | +0.00132 | certified | +0.00171 | outside | -0.01363 | 0.00072 | -0.00079 | outside | room is not positive; largest term a |
| `t6025` | 1 | 4 | 4 | yes | certified | +0.00008 | certified | +0.00075 | outside | -0.01585 | 0.00076 | -0.00230 | outside | room is not positive; largest term a |
| `t6027` | 2 | 3 | 3 | yes | certified | +0.00021 | outside | -0.00003 | outside | -0.01786 | 0.00060 | -0.00264 | outside | room is not positive; largest term a |
| `t6028` | 2 | 4 | 4 | yes | certified | +0.00523 | certified | +0.00575 | outside | -0.01334 | 0.00073 | +0.00315 | certified | — |
| `t6030` | 1 | 3 | 3 | yes | certified | +0.00345 | certified | +0.00287 | outside | -0.01390 | 0.00063 | +0.00030 | certified | — |
| `t6031` | 1 | 4 | 4 | yes | certified | +0.00247 | certified | +0.00315 | outside | -0.01584 | 0.00070 | +0.00036 | certified | — |
| `t6032` | 1 | 3 | 3 | yes | certified | +0.00566 | certified | +0.00562 | outside | -0.01026 | 0.00059 | +0.00323 | certified | — |
| `t6032` | 2 | 4 | 4 | yes | certified | +0.00562 | certified | +0.00558 | outside | -0.01152 | 0.00070 | +0.00289 | certified | — |
| `t6037` | 1 | 4 | 4 | yes | certified | +0.00115 | certified | +0.00145 | outside | -0.01112 | 0.00071 | -0.00067 | outside | room is not positive; largest term B |
| `t6037` | 2 | 4 | 4 | yes | certified | +0.00122 | certified | +0.00151 | outside | -0.01600 | 0.00074 | -0.00072 | outside | room is not positive; largest term a |
| `t6038` | 1 | 4 | 4 | yes | certified | +0.00019 | certified | +0.00004 | outside | -0.01862 | 0.00078 | -0.00308 | outside | room is not positive; largest term a |
| `t6040` | 2 | 5 | 5 | yes | certified | +0.00319 | certified | +0.00279 | outside | -0.01219 | 0.00084 | -0.00062 | outside | room is not positive; largest term B |
| `t6042` | 2 | 5 | 5 | yes | certified | +0.00341 | certified | +0.00306 | outside | -0.01579 | 0.00088 | -0.00042 | outside | room is not positive; largest term a |
| `t6043` | 2 | 5 | 5 | yes | certified | +0.00597 | certified | +0.00618 | outside | -0.00987 | 0.00086 | +0.00263 | certified | — |
| `t6045` | 2 | 4 | 4 | yes | certified | +0.00075 | certified | +0.00150 | outside | -0.01676 | 0.00075 | -0.00150 | outside | room is not positive; largest term B |
| `t6050` | 2 | 4 | 4 | yes | certified | +0.00392 | certified | +0.00459 | outside | -0.01005 | 0.00068 | +0.00208 | certified | — |
| `t6051` | 2 | 3 | 3 | yes | certified | +0.00887 | certified | +0.00911 | outside | -0.00842 | 0.00063 | +0.00640 | certified | — |
| `t6052` | 1 | 4 | 4 | yes | certified | +0.00218 | certified | +0.00285 | outside | -0.01468 | 0.00074 | -0.00016 | outside | room is not positive; largest term a |
| `t6055` | 1 | 6 | 6 | yes | certified | +0.00156 | certified | +0.00121 | outside | -0.01577 | 0.00089 | -0.00236 | outside | room is not positive; largest term a |
| `t6056` | 1 | 5 | 5 | yes | certified | +0.00127 | certified | +0.00158 | outside | -0.01852 | 0.00091 | -0.00118 | outside | room is not positive; largest term a |
| `t6058` | 2 | 4 | 4 | yes | certified | +0.00370 | certified | +0.00405 | outside | -0.01130 | 0.00070 | +0.00195 | certified | — |
| `t6061` | 2 | 3 | 3 | yes | certified | +0.00343 | certified | +0.00376 | outside | -0.01323 | 0.00063 | +0.00182 | certified | — |
| `t6063` | 1 | 2 | 2 | yes | certified | +0.00746 | certified | +0.00786 | outside | -0.01011 | 0.00052 | +0.00577 | certified | — |
| `t6065` | 1 | 4 | 4 | yes | certified | +0.01277 | certified | +0.01222 | outside | -0.00483 | 0.00074 | +0.00921 | certified | — |
| `t6067` | 2 | 3 | 3 | yes | certified | +0.00518 | certified | +0.00461 | outside | -0.01355 | 0.00062 | +0.00195 | certified | — |
| `t6068` | 2 | 2 | 2 | yes | certified | +0.00448 | certified | +0.00510 | outside | -0.01542 | 0.00051 | +0.00285 | certified | — |
| `t6074` | 1 | 3 | 3 | yes | certified | +0.00907 | certified | +0.00992 | outside | -0.01058 | 0.00066 | +0.00727 | certified | — |
| `t6075` | 2 | 4 | 4 | yes | certified | +0.00789 | certified | +0.00783 | outside | -0.01023 | 0.00074 | +0.00495 | certified | — |
| `t6076` | 1 | 4 | 4 | yes | certified | +0.00199 | certified | +0.00267 | outside | -0.01428 | 0.00076 | -0.00042 | outside | room is not positive; largest term B |
| `t6077` | 1 | 5 | 5 | yes | certified | +0.00441 | certified | +0.00455 | outside | -0.01026 | 0.00084 | +0.00204 | certified | — |
| `t6077` | 2 | 5 | 5 | yes | certified | +0.00605 | certified | +0.00619 | outside | -0.01114 | 0.00088 | +0.00354 | certified | — |
| `t6079` | 1 | 4 | 4 | yes | certified | +0.00722 | certified | +0.00721 | outside | -0.01173 | 0.00076 | +0.00415 | certified | — |
| `t6079` | 2 | 4 | 4 | yes | certified | +0.00048 | certified | +0.00048 | outside | -0.01614 | 0.00075 | -0.00256 | outside | room is not positive; largest term B |
| `t6080` | 2 | 3 | 3 | yes | certified | +0.00075 | certified | +0.00108 | outside | -0.01417 | 0.00064 | -0.00096 | outside | room is not positive; largest term B |
| `t6081` | 1 | 4 | 4 | yes | certified | +0.00069 | certified | +0.00120 | outside | -0.01711 | 0.00076 | -0.00135 | outside | room is not positive; largest term a |
| `t6082` | 2 | 4 | 4 | yes | certified | +0.00280 | certified | +0.00282 | outside | -0.01219 | 0.00078 | +0.00049 | certified | — |
| `t6083` | 2 | 4 | 4 | yes | certified | +0.00020 | certified | +0.00062 | outside | -0.01566 | 0.00072 | -0.00237 | outside | room is not positive; largest term a |
| `t6085` | 2 | 3 | 3 | yes | certified | +0.00269 | certified | +0.00302 | outside | -0.01511 | 0.00065 | +0.00106 | certified | — |
| `t6088` | 2 | 4 | 4 | yes | certified | +0.00524 | certified | +0.00518 | outside | -0.01455 | 0.00081 | +0.00181 | certified | — |
| `t6090` | 1 | 4 | 4 | yes | certified | +0.00285 | certified | +0.00286 | outside | -0.01453 | 0.00075 | -0.00019 | outside | room is not positive; largest term B |
| `t6093` | 2 | 4 | 4 | yes | certified | +0.00159 | certified | +0.00198 | outside | -0.01291 | 0.00075 | -0.00065 | outside | room is not positive; largest term a |
| `t6095` | 2 | 3 | 3 | yes | certified | +0.00253 | certified | +0.00262 | outside | -0.01295 | 0.00065 | +0.00066 | certified | — |
| `t6096` | 1 | 3 | 3 | yes | certified | +0.00674 | certified | +0.00708 | outside | -0.00899 | 0.00061 | +0.00459 | certified | — |
| `t6098` | 2 | 5 | 5 | yes | certified | +0.00676 | certified | +0.00731 | outside | -0.00819 | 0.00082 | +0.00438 | certified | — |
| `t6099` | 1 | 5 | 5 | yes | certified | +0.00108 | certified | +0.00169 | outside | -0.01408 | 0.00085 | -0.00180 | outside | room is not positive; largest term a |

## The 200 ports

| Cell | Port | m | Count | Agrees | Certification campaign | Its room | Status 1 | Room 1 | Status 2 | Room 2 | `eps3` | Room 3 | Status 3 | Reason |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6001` | 1 | 5 | 5 | yes | outside | -0.00833 | outside | -0.00766 | outside | -0.03034 | 0.00095 | -0.01147 | outside | room is not positive; largest term a |
| `t6001` | 2 | 5 | 5 | yes | outside | -0.00105 | outside | -0.00038 | outside | -0.02079 | 0.00093 | -0.00415 | outside | room is not positive; largest term a |
| `t6002` | 1 | 2 | 2 | yes | certified | +0.01033 | certified | +0.01051 | outside | -0.00924 | 0.00052 | +0.00841 | certified | — |
| `t6002` | 2 | 4 | 4 | yes | outside | -0.00907 | outside | -0.00889 | outside | -0.01666 | 0.00070 | -0.01153 | outside | room is not positive; largest term a |
| `t6003` | 1 | 5 | 5 | yes | certified | +0.00319 | certified | +0.00341 | outside | -0.01376 | 0.00096 | +0.00043 | certified | — |
| `t6003` | 2 | 5 | 5 | yes | outside | -0.01130 | outside | -0.01108 | outside | -0.03296 | 0.00100 | -0.01416 | outside | room is not positive; largest term a |
| `t6004` | 1 | 6 | 6 | yes | certified | +0.00375 | certified | +0.00298 | outside | -0.01252 | 0.00094 | -0.00085 | outside | room is not positive; largest term B |
| `t6004` | 2 | 4 | 4 | yes | certified | +0.00573 | certified | +0.00496 | outside | -0.01187 | 0.00076 | +0.00167 | certified | — |
| `t6005` | 1 | 2 | 2 | yes | certified | +0.00473 | certified | +0.00466 | outside | -0.01449 | 0.00051 | +0.00259 | certified | — |
| `t6005` | 2 | 5 | 5 | yes | outside | -0.00823 | outside | -0.00830 | outside | -0.03049 | 0.00085 | -0.01137 | outside | room is not positive; largest term a |
| `t6006` | 1 | 4 | 4 | yes | outside | -0.00986 | outside | -0.00952 | outside | -0.03109 | 0.00071 | -0.01165 | outside | room is not positive; largest term a |
| `t6006` | 2 | 4 | 4 | yes | outside | -0.00276 | outside | -0.00241 | outside | -0.01611 | 0.00067 | -0.00442 | outside | room is not positive; largest term a |
| `t6007` | 1 | 5 | 4 | no | outside | -0.00903 | outside | -0.00924 | outside | -0.03209 | 0.00087 | -0.01273 | outside | room is not positive; largest term a |
| `t6007` | 2 | 3 | 3 | yes | outside | -0.00589 | outside | -0.00610 | outside | -0.01993 | 0.00060 | -0.00878 | outside | room is not positive; largest term a |
| `t6008` | 1 | 3 | 3 | yes | certified | +0.00775 | certified | +0.00745 | outside | -0.00998 | 0.00061 | +0.00500 | certified | — |
| `t6008` | 2 | 4 | 4 | yes | outside | -0.01024 | outside | -0.01053 | outside | -0.02354 | 0.00070 | -0.01326 | outside | room is not positive; largest term a |
| `t6009` | 1 | 3 | 3 | yes | outside | -0.00588 | outside | -0.00647 | outside | -0.01832 | 0.00062 | -0.00906 | outside | room is not positive; largest term a |
| `t6009` | 2 | 3 | 3 | yes | certified | +0.00680 | certified | +0.00620 | outside | -0.01135 | 0.00063 | +0.00359 | certified | — |
| `t6010` | 1 | 4 | 4 | yes | certified | +0.00416 | certified | +0.00400 | outside | -0.01690 | 0.00080 | +0.00078 | certified | — |
| `t6010` | 2 | 6 | 6 | yes | outside | -0.00109 | outside | -0.00124 | outside | -0.02149 | 0.00101 | -0.00509 | outside | room is not positive; largest term a |
| `t6011` | 1 | 4 | 4 | yes | outside | +0.00932 | outside | +0.00923 | outside | -0.00843 | 0.00077 | +0.00611 | outside | a rest state is outside the band |
| `t6011` | 2 | 5 | 5 | yes | certified | +0.00516 | certified | +0.00507 | outside | -0.01174 | 0.00087 | +0.00164 | certified | — |
| `t6012` | 1 | 4 | 4 | yes | certified | +0.00895 | certified | +0.00878 | outside | -0.00748 | 0.00073 | +0.00586 | certified | — |
| `t6012` | 2 | 5 | 5 | yes | outside | -0.00759 | outside | -0.00776 | outside | -0.02735 | 0.00082 | -0.01094 | outside | room is not positive; largest term a |
| `t6013` | 1 | 4 | 4 | yes | outside | -0.00554 | outside | -0.00508 | outside | -0.01660 | 0.00074 | -0.00811 | outside | room is not positive; largest term a |
| `t6013` | 2 | 3 | 3 | yes | certified | +0.00592 | certified | +0.00638 | outside | -0.01116 | 0.00066 | +0.00359 | certified | — |
| `t6014` | 1 | 3 | 3 | yes | outside | -0.01070 | outside | -0.01045 | outside | -0.02111 | 0.00065 | -0.01238 | outside | room is not positive; largest term a |
| `t6014` | 2 | 5 | 5 | yes | outside | -0.00804 | outside | -0.00779 | outside | -0.02644 | 0.00090 | -0.01048 | outside | room is not positive; largest term a |
| `t6015` | 1 | 4 | 4 | yes | certified | +0.00464 | certified | +0.00517 | outside | -0.01451 | 0.00083 | +0.00183 | certified | — |
| `t6015` | 2 | 5 | 5 | yes | outside | -0.00660 | outside | -0.00607 | outside | -0.02628 | 0.00093 | -0.00971 | outside | room is not positive; largest term a |
| `t6016` | 1 | 4 | 4 | yes | certified | +0.00129 | certified | +0.00147 | outside | -0.01483 | 0.00072 | -0.00071 | outside | room is not positive; largest term a |
| `t6016` | 2 | 5 | 5 | yes | outside | -0.00454 | outside | -0.00436 | outside | -0.02356 | 0.00086 | -0.00694 | outside | room is not positive; largest term a |
| `t6017` | 1 | 4 | 4 | yes | outside | -0.00062 | outside | -0.00113 | outside | -0.02104 | 0.00080 | -0.00432 | outside | room is not positive; largest term a |
| `t6017` | 2 | 3 | 3 | yes | outside | -0.00035 | outside | -0.00086 | outside | -0.01661 | 0.00065 | -0.00362 | outside | room is not positive; largest term a |
| `t6018` | 1 | 4 | 4 | yes | outside | -0.00586 | outside | -0.00561 | outside | -0.02861 | 0.00080 | -0.00884 | outside | room is not positive; largest term a |
| `t6018` | 2 | 3 | 3 | yes | certified | +0.00548 | certified | +0.00573 | outside | -0.01422 | 0.00068 | +0.00287 | certified | — |
| `t6019` | 1 | 4 | 4 | yes | outside | -0.01866 | outside | -0.01826 | outside | -0.04017 | 0.00078 | -0.02095 | outside | room is not positive; largest term a |
| `t6019` | 2 | 4 | 4 | yes | certified | +0.00132 | certified | +0.00171 | outside | -0.01363 | 0.00072 | -0.00079 | outside | room is not positive; largest term a |
| `t6020` | 1 | 4 | 4 | yes | outside | -0.01358 | outside | -0.01282 | outside | -0.03538 | 0.00078 | -0.01591 | outside | room is not positive; largest term a |
| `t6020` | 2 | 4 | 4 | yes | outside | -0.00282 | outside | -0.00206 | outside | -0.02158 | 0.00078 | -0.00516 | outside | room is not positive; largest term B |
| `t6021` | 1 | 5 | 6 | no | outside | -0.01965 | outside | -0.02003 | outside | -0.02748 | 0.00082 | -0.02347 | outside | room is not positive; largest term a |
| `t6021` | 2 | 5 | 5 | yes | outside | -0.00274 | outside | -0.00312 | outside | -0.02404 | 0.00088 | -0.00676 | outside | room is not positive; largest term a |
| `t6022` | 1 | 3 | 3 | yes | outside | -0.00755 | outside | -0.00704 | outside | -0.01698 | 0.00058 | -0.00905 | outside | room is not positive; largest term a |
| `t6022` | 2 | 4 | 4 | yes | outside | -0.01437 | outside | -0.01386 | outside | -0.02555 | 0.00071 | -0.01625 | outside | room is not positive; largest term a |
| `t6023` | 1 | 4 | 4 | yes | outside | -0.00674 | outside | -0.00657 | outside | -0.02505 | 0.00076 | -0.00958 | outside | room is not positive; largest term a |
| `t6023` | 2 | 3 | 3 | yes | outside | -0.00655 | outside | -0.00637 | outside | -0.01533 | 0.00062 | -0.00898 | outside | room is not positive; largest term a |
| `t6024` | 1 | 3 | 3 | yes | outside | -0.00771 | outside | -0.00822 | outside | -0.02082 | 0.00066 | -0.01103 | outside | room is not positive; largest term a |
| `t6024` | 2 | 6 | 5 | no | outside | -0.01231 | outside | -0.01282 | outside | -0.03577 | 0.00106 | -0.01682 | outside | room is not positive; largest term a |
| `t6025` | 1 | 4 | 4 | yes | certified | +0.00008 | certified | +0.00075 | outside | -0.01585 | 0.00076 | -0.00230 | outside | room is not positive; largest term a |
| `t6025` | 2 | 4 | 4 | yes | outside | -0.00683 | outside | -0.00616 | outside | -0.02740 | 0.00078 | -0.00929 | outside | room is not positive; largest term a |
| `t6026` | 1 | 4 | 4 | yes | outside | -0.00438 | outside | -0.00466 | outside | -0.01976 | 0.00075 | -0.00771 | outside | room is not positive; largest term a |
| `t6026` | 2 | 4 | 4 | yes | outside | -0.00446 | outside | -0.00473 | outside | -0.01692 | 0.00075 | -0.00779 | outside | room is not positive; largest term a |
| `t6027` | 1 | 5 | 5 | yes | outside | -0.00346 | outside | -0.00369 | outside | -0.02403 | 0.00080 | -0.00690 | outside | room is not positive; largest term a |
| `t6027` | 2 | 3 | 3 | yes | certified | +0.00021 | outside | -0.00003 | outside | -0.01786 | 0.00060 | -0.00264 | outside | room is not positive; largest term a |
| `t6028` | 1 | 5 | 5 | yes | outside | -0.00303 | outside | -0.00250 | outside | -0.02276 | 0.00082 | -0.00541 | outside | room is not positive; largest term a |
| `t6028` | 2 | 4 | 4 | yes | certified | +0.00523 | certified | +0.00575 | outside | -0.01334 | 0.00073 | +0.00315 | certified | — |
| `t6029` | 1 | 4 | 4 | yes | outside | -0.00300 | outside | -0.00225 | outside | -0.01664 | 0.00073 | -0.00513 | outside | room is not positive; largest term a |
| `t6029` | 2 | 5 | 5 | yes | outside | -0.00989 | outside | -0.00914 | outside | -0.03056 | 0.00087 | -0.01245 | outside | room is not positive; largest term a |
| `t6030` | 1 | 3 | 3 | yes | certified | +0.00345 | certified | +0.00287 | outside | -0.01390 | 0.00063 | +0.00030 | certified | — |
| `t6030` | 2 | 4 | 5 | no | outside | -0.01378 | outside | -0.01436 | outside | -0.02336 | 0.00071 | -0.01717 | outside | room is not positive; largest term a |
| `t6031` | 1 | 4 | 4 | yes | certified | +0.00247 | certified | +0.00315 | outside | -0.01584 | 0.00070 | +0.00036 | certified | — |
| `t6031` | 2 | 5 | 5 | yes | outside | -0.00545 | outside | -0.00477 | outside | -0.01783 | 0.00076 | -0.00772 | outside | room is not positive; largest term a |
| `t6032` | 1 | 3 | 3 | yes | certified | +0.00566 | certified | +0.00562 | outside | -0.01026 | 0.00059 | +0.00323 | certified | — |
| `t6032` | 2 | 4 | 4 | yes | certified | +0.00562 | certified | +0.00558 | outside | -0.01152 | 0.00070 | +0.00289 | certified | — |
| `t6033` | 1 | 4 | 4 | yes | outside | -0.00728 | outside | -0.00680 | outside | -0.01903 | 0.00072 | -0.00917 | outside | room is not positive; largest term a |
| `t6033` | 2 | 2 | 2 | yes | outside | -0.00206 | outside | -0.00158 | outside | -0.01563 | 0.00048 | -0.00323 | outside | room is not positive; largest term a |
| `t6034` | 1 | 4 | 4 | yes | outside | -0.00473 | outside | -0.00454 | outside | -0.01786 | 0.00077 | -0.00685 | outside | room is not positive; largest term a |
| `t6034` | 2 | 5 | 5 | yes | outside | -0.01212 | outside | -0.01193 | outside | -0.03356 | 0.00093 | -0.01472 | outside | room is not positive; largest term a |
| `t6035` | 1 | 5 | 5 | yes | outside | -0.01363 | outside | -0.01302 | outside | -0.03517 | 0.00090 | -0.01660 | outside | room is not positive; largest term a |
| `t6035` | 2 | 5 | 5 | yes | outside | -0.00530 | outside | -0.00469 | outside | -0.02684 | 0.00091 | -0.00830 | outside | room is not positive; largest term a |
| `t6036` | 1 | 5 | 5 | yes | outside | -0.00999 | outside | -0.00966 | outside | -0.03175 | 0.00090 | -0.01326 | outside | room is not positive; largest term a |
| `t6036` | 2 | 4 | 4 | yes | outside | -0.00720 | outside | -0.00687 | outside | -0.02872 | 0.00081 | -0.01018 | outside | room is not positive; largest term a |
| `t6037` | 1 | 4 | 4 | yes | certified | +0.00115 | certified | +0.00145 | outside | -0.01112 | 0.00071 | -0.00067 | outside | room is not positive; largest term B |
| `t6037` | 2 | 4 | 4 | yes | certified | +0.00122 | certified | +0.00151 | outside | -0.01600 | 0.00074 | -0.00072 | outside | room is not positive; largest term a |
| `t6038` | 1 | 4 | 4 | yes | certified | +0.00019 | certified | +0.00004 | outside | -0.01862 | 0.00078 | -0.00308 | outside | room is not positive; largest term a |
| `t6038` | 2 | 4 | 4 | yes | outside | -0.00532 | outside | -0.00547 | outside | -0.01872 | 0.00075 | -0.00850 | outside | room is not positive; largest term a |
| `t6039` | 1 | 3 | 3 | yes | outside | -0.00095 | outside | -0.00048 | outside | -0.01604 | 0.00057 | -0.00282 | outside | room is not positive; largest term a |
| `t6039` | 2 | 3 | 3 | yes | outside | -0.00068 | outside | -0.00021 | outside | -0.01367 | 0.00054 | -0.00246 | outside | room is not positive; largest term a |
| `t6040` | 1 | 5 | 5 | yes | outside | -0.01664 | outside | -0.01704 | outside | -0.03666 | 0.00088 | -0.02056 | outside | room is not positive; largest term a |
| `t6040` | 2 | 5 | 5 | yes | certified | +0.00319 | certified | +0.00279 | outside | -0.01219 | 0.00084 | -0.00062 | outside | room is not positive; largest term B |
| `t6041` | 1 | 5 | 5 | yes | outside | -0.00304 | outside | -0.00337 | outside | -0.02214 | 0.00096 | -0.00724 | outside | room is not positive; largest term B |
| `t6041` | 2 | 6 | 6 | yes | outside | -0.00701 | outside | -0.00734 | outside | -0.02873 | 0.00110 | -0.01164 | outside | room is not positive; largest term a |
| `t6042` | 1 | 4 | 4 | yes | outside | -0.00852 | outside | -0.00887 | outside | -0.01777 | 0.00073 | -0.01189 | outside | room is not positive; largest term a |
| `t6042` | 2 | 5 | 5 | yes | certified | +0.00341 | certified | +0.00306 | outside | -0.01579 | 0.00088 | -0.00042 | outside | room is not positive; largest term a |
| `t6043` | 1 | 5 | 5 | yes | outside | -0.01251 | outside | -0.01230 | outside | -0.03262 | 0.00099 | -0.01624 | outside | room is not positive; largest term a |
| `t6043` | 2 | 5 | 5 | yes | certified | +0.00597 | certified | +0.00618 | outside | -0.00987 | 0.00086 | +0.00263 | certified | — |
| `t6044` | 1 | 2 | 2 | yes | outside | -0.01618 | outside | -0.01673 | outside | -0.02397 | 0.00050 | -0.01885 | outside | room is not positive; largest term a |
| `t6044` | 2 | 3 | 3 | yes | outside | -0.00078 | outside | -0.00133 | outside | -0.01511 | 0.00062 | -0.00381 | outside | room is not positive; largest term a |
| `t6045` | 1 | 4 | 4 | yes | outside | -0.00208 | outside | -0.00133 | outside | -0.02317 | 0.00078 | -0.00441 | outside | room is not positive; largest term a |
| `t6045` | 2 | 4 | 4 | yes | certified | +0.00075 | certified | +0.00150 | outside | -0.01676 | 0.00075 | -0.00150 | outside | room is not positive; largest term B |
| `t6046` | 1 | 3 | 3 | yes | outside | -0.00712 | outside | -0.00660 | outside | -0.01815 | 0.00060 | -0.00911 | outside | room is not positive; largest term a |
| `t6046` | 2 | 4 | 4 | yes | outside | -0.01307 | outside | -0.01256 | outside | -0.02194 | 0.00070 | -0.01537 | outside | room is not positive; largest term a |
| `t6047` | 1 | 4 | 4 | yes | outside | -0.00217 | outside | -0.00183 | outside | -0.01572 | 0.00075 | -0.00406 | outside | room is not positive; largest term a |
| `t6047` | 2 | 5 | 5 | yes | outside | -0.00630 | outside | -0.00595 | outside | -0.02608 | 0.00090 | -0.00866 | outside | room is not positive; largest term a |
| `t6048` | 1 | 5 | 5 | yes | outside | -0.01163 | outside | -0.01130 | outside | -0.03434 | 0.00092 | -0.01407 | outside | room is not positive; largest term a |
| `t6048` | 2 | 4 | 4 | yes | outside | -0.00685 | outside | -0.00652 | outside | -0.02036 | 0.00075 | -0.00878 | outside | room is not positive; largest term a |
| `t6049` | 1 | 4 | 4 | yes | outside | -0.01387 | outside | -0.01358 | outside | -0.03581 | 0.00075 | -0.01657 | outside | room is not positive; largest term a |
| `t6049` | 2 | 4 | 4 | yes | outside | -0.00062 | outside | -0.00032 | outside | -0.01920 | 0.00074 | -0.00329 | outside | room is not positive; largest term a |
| `t6050` | 1 | 3 | 3 | yes | outside | -0.01381 | outside | -0.01314 | outside | -0.02102 | 0.00058 | -0.01536 | outside | room is not positive; largest term a |
| `t6050` | 2 | 4 | 4 | yes | certified | +0.00392 | certified | +0.00459 | outside | -0.01005 | 0.00068 | +0.00208 | certified | — |
| `t6051` | 1 | 4 | 4 | yes | outside | +0.00119 | outside | +0.00143 | outside | -0.01390 | 0.00075 | -0.00167 | outside | a rest state is outside the band; room is not positive; largest term a |
| `t6051` | 2 | 3 | 3 | yes | certified | +0.00887 | certified | +0.00911 | outside | -0.00842 | 0.00063 | +0.00640 | certified | — |
| `t6052` | 1 | 4 | 4 | yes | certified | +0.00218 | certified | +0.00285 | outside | -0.01468 | 0.00074 | -0.00016 | outside | room is not positive; largest term a |
| `t6052` | 2 | 4 | 4 | yes | outside | -0.00716 | outside | -0.00649 | outside | -0.02191 | 0.00072 | -0.00944 | outside | room is not positive; largest term a |
| `t6053` | 1 | 3 | 3 | yes | outside | -0.00969 | outside | -0.00992 | outside | -0.03001 | 0.00061 | -0.01240 | outside | room is not positive; largest term a |
| `t6053` | 2 | 4 | 4 | yes | outside | -0.00253 | outside | -0.00276 | outside | -0.01388 | 0.00070 | -0.00549 | outside | room is not positive; largest term a |
| `t6054` | 1 | 4 | 4 | yes | outside | -0.00348 | outside | -0.00285 | outside | -0.01768 | 0.00073 | -0.00586 | outside | room is not positive; largest term a |
| `t6054` | 2 | 4 | 4 | yes | outside | -0.01247 | outside | -0.01184 | outside | -0.03350 | 0.00077 | -0.01496 | outside | room is not positive; largest term a |
| `t6055` | 1 | 6 | 6 | yes | certified | +0.00156 | certified | +0.00121 | outside | -0.01577 | 0.00089 | -0.00236 | outside | room is not positive; largest term a |
| `t6055` | 2 | 5 | 5 | yes | outside | -0.01222 | outside | -0.01258 | outside | -0.02030 | 0.00076 | -0.01573 | outside | room is not positive; largest term a |
| `t6056` | 1 | 5 | 5 | yes | certified | +0.00127 | certified | +0.00158 | outside | -0.01852 | 0.00091 | -0.00118 | outside | room is not positive; largest term a |
| `t6056` | 2 | 3 | 3 | yes | outside | -0.01173 | outside | -0.01142 | outside | -0.03325 | 0.00070 | -0.01353 | outside | room is not positive; largest term a |
| `t6057` | 1 | 6 | 6 | yes | outside | -0.01342 | outside | -0.01285 | outside | -0.03501 | 0.00099 | -0.01655 | outside | room is not positive; largest term a |
| `t6057` | 2 | 5 | 5 | yes | outside | -0.00325 | outside | -0.00268 | outside | -0.01836 | 0.00082 | -0.00589 | outside | room is not positive; largest term B |
| `t6058` | 1 | 4 | 4 | yes | outside | -0.01282 | outside | -0.01247 | outside | -0.03275 | 0.00073 | -0.01469 | outside | room is not positive; largest term a |
| `t6058` | 2 | 4 | 4 | yes | certified | +0.00370 | certified | +0.00405 | outside | -0.01130 | 0.00070 | +0.00195 | certified | — |
| `t6059` | 1 | 4 | 4 | yes | outside | -0.00395 | outside | -0.00341 | outside | -0.01806 | 0.00075 | -0.00653 | outside | room is not positive; largest term a |
| `t6059` | 2 | 5 | 5 | yes | outside | -0.00540 | outside | -0.00486 | outside | -0.01867 | 0.00084 | -0.00823 | outside | room is not positive; largest term a |
| `t6060` | 1 | 5 | 5 | yes | outside | -0.00997 | outside | -0.00943 | outside | -0.01893 | 0.00084 | -0.01291 | outside | room is not positive; largest term a |
| `t6060` | 2 | 4 | 4 | yes | outside | -0.00425 | outside | -0.00371 | outside | -0.02326 | 0.00078 | -0.00702 | outside | room is not positive; largest term a |
| `t6061` | 1 | 4 | 4 | yes | outside | -0.00891 | outside | -0.00859 | outside | -0.01795 | 0.00070 | -0.01072 | outside | room is not positive; largest term a |
| `t6061` | 2 | 3 | 3 | yes | certified | +0.00343 | certified | +0.00376 | outside | -0.01323 | 0.00063 | +0.00182 | certified | — |
| `t6062` | 1 | 4 | 4 | yes | outside | -0.00103 | outside | -0.00108 | outside | -0.02136 | 0.00073 | -0.00397 | outside | room is not positive; largest term a |
| `t6062` | 2 | 3 | 3 | yes | outside | -0.01413 | outside | -0.01418 | outside | -0.02101 | 0.00058 | -0.01662 | outside | room is not positive; largest term a |
| `t6063` | 1 | 2 | 2 | yes | certified | +0.00746 | certified | +0.00786 | outside | -0.01011 | 0.00052 | +0.00577 | certified | — |
| `t6063` | 2 | 4 | 3 | no | outside | -0.01285 | outside | -0.01245 | outside | -0.03675 | 0.00076 | -0.01527 | outside | room is not positive; largest term a |
| `t6064` | 1 | 5 | 5 | yes | outside | -0.00624 | outside | -0.00586 | outside | -0.01284 | 0.00077 | -0.00847 | outside | room is not positive; largest term a |
| `t6064` | 2 | 3 | 3 | yes | outside | -0.00870 | outside | -0.00832 | outside | -0.01923 | 0.00059 | -0.01038 | outside | room is not positive; largest term a |
| `t6065` | 1 | 4 | 4 | yes | certified | +0.01277 | certified | +0.01222 | outside | -0.00483 | 0.00074 | +0.00921 | certified | — |
| `t6065` | 2 | 3 | 3 | yes | outside | -0.00718 | outside | -0.00774 | outside | -0.03001 | 0.00066 | -0.01050 | outside | room is not positive; largest term a |
| `t6066` | 1 | 5 | 5 | yes | outside | -0.00667 | outside | -0.00637 | outside | -0.02716 | 0.00087 | -0.00900 | outside | room is not positive; largest term a |
| `t6066` | 2 | 4 | 4 | yes | outside | -0.00761 | outside | -0.00731 | outside | -0.02871 | 0.00077 | -0.00963 | outside | room is not positive; largest term a |
| `t6067` | 1 | 4 | 4 | yes | outside | -0.00859 | outside | -0.00916 | outside | -0.01906 | 0.00068 | -0.01200 | outside | room is not positive; largest term a |
| `t6067` | 2 | 3 | 3 | yes | certified | +0.00518 | certified | +0.00461 | outside | -0.01355 | 0.00062 | +0.00195 | certified | — |
| `t6068` | 1 | 4 | 4 | yes | outside | -0.00318 | outside | -0.00256 | outside | -0.02489 | 0.00073 | -0.00547 | outside | room is not positive; largest term a |
| `t6068` | 2 | 2 | 2 | yes | certified | +0.00448 | certified | +0.00510 | outside | -0.01542 | 0.00051 | +0.00285 | certified | — |
| `t6069` | 1 | 5 | 5 | yes | outside | -0.01591 | outside | -0.01577 | outside | -0.02352 | 0.00082 | -0.01922 | outside | room is not positive; largest term a |
| `t6069` | 2 | 4 | 5 | no | outside | -0.01204 | outside | -0.01190 | outside | -0.01929 | 0.00072 | -0.01503 | outside | room is not positive; largest term a |
| `t6070` | 1 | 5 | 5 | yes | outside | -0.01466 | outside | -0.01455 | outside | -0.03592 | 0.00090 | -0.01815 | outside | room is not positive; largest term a |
| `t6070` | 2 | 4 | 4 | yes | outside | -0.00633 | outside | -0.00622 | outside | -0.01911 | 0.00076 | -0.00938 | outside | room is not positive; largest term a |
| `t6071` | 1 | 2 | 2 | yes | outside | -0.00282 | outside | -0.00204 | outside | -0.02025 | 0.00051 | -0.00414 | outside | room is not positive; largest term a |
| `t6071` | 2 | 5 | 5 | yes | outside | -0.00583 | outside | -0.00504 | outside | -0.02621 | 0.00086 | -0.00820 | outside | room is not positive; largest term a |
| `t6072` | 1 | 3 | 4 | no | outside | -0.02138 | outside | -0.02122 | outside | -0.02762 | 0.00061 | -0.02305 | outside | room is not positive; largest term a |
| `t6072` | 2 | 4 | 4 | yes | outside | -0.00471 | outside | -0.00455 | outside | -0.02291 | 0.00073 | -0.00674 | outside | room is not positive; largest term a |
| `t6073` | 1 | 4 | 4 | yes | outside | -0.01029 | outside | -0.01049 | outside | -0.02124 | 0.00069 | -0.01339 | outside | room is not positive; largest term a |
| `t6073` | 2 | 5 | 5 | yes | outside | -0.01172 | outside | -0.01191 | outside | -0.01891 | 0.00082 | -0.01517 | outside | room is not positive; largest term a |
| `t6074` | 1 | 3 | 3 | yes | certified | +0.00907 | certified | +0.00992 | outside | -0.01058 | 0.00066 | +0.00727 | certified | — |
| `t6074` | 2 | 2 | 3 | no | outside | -0.00926 | outside | -0.00841 | outside | -0.02966 | 0.00065 | -0.01102 | outside | room is not positive; largest term a |
| `t6075` | 1 | 3 | 3 | yes | outside | -0.00228 | outside | -0.00233 | outside | -0.01937 | 0.00063 | -0.00490 | outside | room is not positive; largest term B |
| `t6075` | 2 | 4 | 4 | yes | certified | +0.00789 | certified | +0.00783 | outside | -0.01023 | 0.00074 | +0.00495 | certified | — |
| `t6076` | 1 | 4 | 4 | yes | certified | +0.00199 | certified | +0.00267 | outside | -0.01428 | 0.00076 | -0.00042 | outside | room is not positive; largest term B |
| `t6076` | 2 | 4 | 4 | yes | outside | -0.00272 | outside | -0.00204 | outside | -0.01739 | 0.00078 | -0.00519 | outside | room is not positive; largest term a |
| `t6077` | 1 | 5 | 5 | yes | certified | +0.00441 | certified | +0.00455 | outside | -0.01026 | 0.00084 | +0.00204 | certified | — |
| `t6077` | 2 | 5 | 5 | yes | certified | +0.00605 | certified | +0.00619 | outside | -0.01114 | 0.00088 | +0.00354 | certified | — |
| `t6078` | 1 | 4 | 4 | yes | outside | -0.00906 | outside | -0.00899 | outside | -0.01953 | 0.00074 | -0.01122 | outside | room is not positive; largest term a |
| `t6078` | 2 | 5 | 5 | yes | outside | -0.00570 | outside | -0.00564 | outside | -0.02469 | 0.00089 | -0.00831 | outside | room is not positive; largest term a |
| `t6079` | 1 | 4 | 4 | yes | certified | +0.00722 | certified | +0.00721 | outside | -0.01173 | 0.00076 | +0.00415 | certified | — |
| `t6079` | 2 | 4 | 4 | yes | certified | +0.00048 | certified | +0.00048 | outside | -0.01614 | 0.00075 | -0.00256 | outside | room is not positive; largest term B |
| `t6080` | 1 | 4 | 4 | yes | outside | -0.00380 | outside | -0.00346 | outside | -0.02408 | 0.00080 | -0.00598 | outside | room is not positive; largest term a |
| `t6080` | 2 | 3 | 3 | yes | certified | +0.00075 | certified | +0.00108 | outside | -0.01417 | 0.00064 | -0.00096 | outside | room is not positive; largest term B |
| `t6081` | 1 | 4 | 4 | yes | certified | +0.00069 | certified | +0.00120 | outside | -0.01711 | 0.00076 | -0.00135 | outside | room is not positive; largest term a |
| `t6081` | 2 | 4 | 4 | yes | outside | -0.00111 | outside | -0.00060 | outside | -0.01647 | 0.00074 | -0.00309 | outside | room is not positive; largest term a |
| `t6082` | 1 | 5 | 5 | yes | outside | -0.00695 | outside | -0.00693 | outside | -0.02434 | 0.00090 | -0.00963 | outside | room is not positive; largest term a |
| `t6082` | 2 | 4 | 4 | yes | certified | +0.00280 | certified | +0.00282 | outside | -0.01219 | 0.00078 | +0.00049 | certified | — |
| `t6083` | 1 | 4 | 4 | yes | outside | -0.00926 | outside | -0.00883 | outside | -0.01946 | 0.00072 | -0.01184 | outside | room is not positive; largest term a |
| `t6083` | 2 | 4 | 4 | yes | certified | +0.00020 | certified | +0.00062 | outside | -0.01566 | 0.00072 | -0.00237 | outside | room is not positive; largest term a |
| `t6084` | 1 | 4 | 4 | yes | outside | -0.00305 | outside | -0.00260 | outside | -0.01554 | 0.00067 | -0.00476 | outside | room is not positive; largest term a |
| `t6084` | 2 | 4 | 4 | yes | outside | -0.01440 | outside | -0.01394 | outside | -0.03589 | 0.00073 | -0.01629 | outside | room is not positive; largest term a |
| `t6085` | 1 | 4 | 4 | yes | outside | -0.00186 | outside | -0.00153 | outside | -0.01996 | 0.00078 | -0.00386 | outside | room is not positive; largest term a |
| `t6085` | 2 | 3 | 3 | yes | certified | +0.00269 | certified | +0.00302 | outside | -0.01511 | 0.00065 | +0.00106 | certified | — |
| `t6086` | 1 | 5 | 5 | yes | outside | -0.00064 | outside | -0.00093 | outside | -0.01574 | 0.00089 | -0.00457 | outside | room is not positive; largest term a |
| `t6086` | 2 | 4 | 4 | yes | outside | -0.01165 | outside | -0.01194 | outside | -0.01934 | 0.00078 | -0.01526 | outside | room is not positive; largest term a |
| `t6087` | 1 | 4 | 5 | no | outside | -0.01078 | outside | -0.01024 | outside | -0.01826 | 0.00071 | -0.01321 | outside | room is not positive; largest term a |
| `t6087` | 2 | 4 | 4 | yes | outside | -0.00509 | outside | -0.00454 | outside | -0.02564 | 0.00077 | -0.00772 | outside | room is not positive; largest term a |
| `t6088` | 1 | 5 | 5 | yes | outside | -0.00220 | outside | -0.00226 | outside | -0.02089 | 0.00090 | -0.00590 | outside | room is not positive; largest term a |
| `t6088` | 2 | 4 | 4 | yes | certified | +0.00524 | certified | +0.00518 | outside | -0.01455 | 0.00081 | +0.00181 | certified | — |
| `t6089` | 1 | 5 | 5 | yes | outside | -0.01218 | outside | -0.01262 | outside | -0.03473 | 0.00089 | -0.01620 | outside | room is not positive; largest term a |
| `t6089` | 2 | 4 | 3 | no | outside | -0.01151 | outside | -0.01195 | outside | -0.03203 | 0.00076 | -0.01513 | outside | room is not positive; largest term a |
| `t6090` | 1 | 4 | 4 | yes | certified | +0.00285 | certified | +0.00286 | outside | -0.01453 | 0.00075 | -0.00019 | outside | room is not positive; largest term B |
| `t6090` | 2 | 4 | 4 | yes | outside | -0.00259 | outside | -0.00259 | outside | -0.02296 | 0.00079 | -0.00573 | outside | room is not positive; largest term a |
| `t6091` | 1 | 6 | 6 | yes | outside | -0.00660 | outside | -0.00625 | outside | -0.02561 | 0.00104 | -0.01040 | outside | room is not positive; largest term a |
| `t6091` | 2 | 5 | 5 | yes | outside | -0.00637 | outside | -0.00602 | outside | -0.02529 | 0.00093 | -0.00986 | outside | room is not positive; largest term a |
| `t6092` | 1 | 3 | 3 | yes | outside | -0.00965 | outside | -0.00949 | outside | -0.03013 | 0.00065 | -0.01145 | outside | room is not positive; largest term a |
| `t6092` | 2 | 3 | 3 | yes | outside | -0.00120 | outside | -0.00104 | outside | -0.01358 | 0.00063 | -0.00293 | outside | room is not positive; largest term a |
| `t6093` | 1 | 4 | 4 | yes | outside | -0.01438 | outside | -0.01399 | outside | -0.02059 | 0.00073 | -0.01656 | outside | room is not positive; largest term a |
| `t6093` | 2 | 4 | 4 | yes | certified | +0.00159 | certified | +0.00198 | outside | -0.01291 | 0.00075 | -0.00065 | outside | room is not positive; largest term a |
| `t6094` | 1 | 4 | 4 | yes | outside | -0.00217 | outside | -0.00204 | outside | -0.02204 | 0.00076 | -0.00507 | outside | room is not positive; largest term a |
| `t6094` | 2 | 5 | 5 | yes | outside | -0.01072 | outside | -0.01059 | outside | -0.03066 | 0.00087 | -0.01395 | outside | room is not positive; largest term a |
| `t6095` | 1 | 3 | 3 | yes | outside | -0.00373 | outside | -0.00364 | outside | -0.01773 | 0.00064 | -0.00556 | outside | room is not positive; largest term a |
| `t6095` | 2 | 3 | 3 | yes | certified | +0.00253 | certified | +0.00262 | outside | -0.01295 | 0.00065 | +0.00066 | certified | — |
| `t6096` | 1 | 3 | 3 | yes | certified | +0.00674 | certified | +0.00708 | outside | -0.00899 | 0.00061 | +0.00459 | certified | — |
| `t6096` | 2 | 5 | 5 | yes | outside | -0.01059 | outside | -0.01025 | outside | -0.03107 | 0.00086 | -0.01349 | outside | room is not positive; largest term a |
| `t6097` | 1 | 3 | 4 | no | outside | -0.00902 | outside | -0.00936 | outside | -0.01621 | 0.00060 | -0.01190 | outside | room is not positive; largest term a |
| `t6097` | 2 | 5 | 5 | yes | outside | -0.00098 | outside | -0.00133 | outside | -0.02149 | 0.00085 | -0.00462 | outside | room is not positive; largest term B |
| `t6098` | 1 | 3 | 3 | yes | outside | -0.00642 | outside | -0.00587 | outside | -0.01625 | 0.00060 | -0.00815 | outside | room is not positive; largest term a |
| `t6098` | 2 | 5 | 5 | yes | certified | +0.00676 | certified | +0.00731 | outside | -0.00819 | 0.00082 | +0.00438 | certified | — |
| `t6099` | 1 | 5 | 5 | yes | certified | +0.00108 | certified | +0.00169 | outside | -0.01408 | 0.00085 | -0.00180 | outside | room is not positive; largest term a |
| `t6099` | 2 | 6 | 6 | yes | outside | -0.00800 | outside | -0.00739 | outside | -0.02856 | 0.00100 | -0.01134 | outside | room is not positive; largest term a |
| `t6100` | 1 | 6 | 6 | yes | outside | -0.00805 | outside | -0.00827 | outside | -0.02683 | 0.00097 | -0.01214 | outside | room is not positive; largest term a |
| `t6100` | 2 | 5 | 5 | yes | outside | -0.00062 | outside | -0.00083 | outside | -0.01427 | 0.00084 | -0.00430 | outside | room is not positive; largest term a |
