# Certification campaign: report

Written by `cert_analyze.py certify` under [`PREDICTION.md`](PREDICTION.md). Constants: [`CALIBRATION.md`](CALIBRATION.md). Predicted needs: [`PREDICTED.md`](PREDICTED.md). One row per port: [`ports.csv`](ports.csv).

## Summary

1. **Conditionally certified under the registered rule:** 59 ports of 200 pass its measured budgets and checks; the count is the predicted one on 59 of them.
2. **Not certified:** 141 ports outside the certified domain, 0 not evaluable. Largest term where the room is not positive: `a` on 136 ports, `B` on 3 ports.
3. **Count:** the observed count equals the predicted `m` on 189 of 200 ports, certified or not.
4. **Target `b <= 0.0026` per write:** `b_direct` meets it on 12.5% of the ports; its median is 0.00416, 1.6 times the target. `b_sum` meets it on 0.5%; median 0.00606.
5. **Scope of certification:** it is conditional on the scalar model's peak-to-gain correspondence and on transferring `mu` to the test cells: `h_mu` is the worst case on six cells, not a bound established for each test cell. The comparator/uncut-peak correspondence within `ell` is supported by those six leak scans; the gain of a read with a FIRE is read 0.25 unit before the end of its pulse, within `eps_kappa` = 0.00207.

## Predictions

| | Prediction | Measured | Verdict |
|---|---|---|---|
| E1 | every rest state inside the band | 2098 of 2100 inside | fails |
| E2 | latch at most once per period, steering by the rule | 0 periods with two rises, 0 periods off the rule, of 2100 | holds |
| E3 | count equals `m` on 85% to 98% of the ports | 189 of 200 ports with a count and a prediction (94.5%) | holds |
| E4 | 20% to 60% of the ports certified | 59 of 200 (29.5%) | holds |
| E5 | no certified port with its count contradicted | 0 of 59 certified ports | holds |
| E6 | target missed: fewer than 25% of ports with `b_direct <= 0.0026`, median between 0.004 and 0.012 | 12.5% of 200 ports, median 0.00416 | holds |
| E7 | standard deviation of the static level between 0.001 and 0.008 | 0.01301 | fails |
| E8 | no run fails | 0 of 100 test runs without a usable result | holds |

## Hypotheses of the theorem and their bounds

| Hypothesis | Bound | Source |
|---|---|---|
| Start distance `a` | `a_s` from stage 2 (median 0.01046), plus the shift of the first read of the test run (median 0.00256, largest 0.01135), plus 0.0002 | ramp and first read of the cell without noise; first read of the test run |
| Cumulated gain `B` | median 0.00651, largest 0.01259 | gains of the reads of the test run; `d0` = 0.04209 from the cohort |
| Threshold `ell` | `h_mu` = 0.00151, plus the noise of the threshold in the reads (median 0.00235, largest 0.00336), plus 0.0002 | six leak scans; transfer of their bound to each test cell is assumed; noise source recorded in each read |
| `19/20 <= level` | smallest `level0 - ell`: 0.95911 | ramp of each cell |
| Rest band | 2098 of 2100 states inside `[0.1, 0.1001]` | 1 ps before each pulse of the test runs |
| One FIRE per read, one write per silent pulse, none with a FIRE | 0 periods with two rises, 0 off the steering rule, of 2100 | latch and steering signals of the test runs |
| Gain of a read with a FIRE | within `eps_kappa` = 0.00207 of the early gain plus `kappa` = 0.07461 | largest distance over the silent reads of the test runs |
| Per write, reported: `k*eta`, `sigma`, `e` | medians 0.00133, 0.00052, 0.00394 | window endpoints of each write; slope `s` = 31.316 per V |

Port with the largest room: `t6065`, port 1: +0.01277, with `a` = 0.00045, `B` = 0.00333, `(20/17)*ell` = 0.00436, against `d0/2` = 0.02105.

## The 200 ports

| Status | Ports |
|---|---|
| outside the certified domain | 141 |
| certified, count confirmed | 59 |

| Cell | Port | m | Count | Agrees | `a` | `B` | `(20/17)*ell` | Room | `b_direct` | Status | Reason |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6001` | 1 | 5 | 5 | yes | 0.02048 | 0.00465 | 0.00413 | -0.00833 | 0.00347 | outside the certified domain | room is not positive; largest term a |
| `t6001` | 2 | 5 | 5 | yes | 0.01151 | 0.00605 | 0.00442 | -0.00105 | 0.00196 | outside the certified domain | room is not positive; largest term a |
| `t6002` | 1 | 2 | 2 | yes | 0.00059 | 0.00589 | 0.00411 | +0.01033 | 0.00339 | certified, count confirmed | — |
| `t6002` | 2 | 4 | 4 | yes | 0.02149 | 0.00364 | 0.00486 | -0.00907 | 0.00257 | outside the certified domain | room is not positive; largest term a |
| `t6003` | 1 | 5 | 5 | yes | 0.00593 | 0.00694 | 0.00486 | +0.00319 | 0.00433 | certified, count confirmed | — |
| `t6003` | 2 | 5 | 5 | yes | 0.02096 | 0.00627 | 0.00500 | -0.01130 | 0.00544 | outside the certified domain | room is not positive; largest term a |
| `t6004` | 1 | 6 | 6 | yes | 0.00563 | 0.00714 | 0.00440 | +0.00375 | 0.00595 | certified, count confirmed | — |
| `t6004` | 2 | 4 | 4 | yes | 0.00350 | 0.00705 | 0.00464 | +0.00573 | 0.00596 | certified, count confirmed | — |
| `t6005` | 1 | 2 | 2 | yes | 0.00714 | 0.00415 | 0.00490 | +0.00473 | 0.00331 | certified, count confirmed | — |
| `t6005` | 2 | 5 | 5 | yes | 0.01708 | 0.00712 | 0.00495 | -0.00823 | 0.00408 | outside the certified domain | room is not positive; largest term a |
| `t6006` | 1 | 4 | 4 | yes | 0.02077 | 0.00512 | 0.00489 | -0.00986 | 0.00241 | outside the certified domain | room is not positive; largest term a |
| `t6006` | 2 | 4 | 4 | yes | 0.01407 | 0.00507 | 0.00454 | -0.00276 | 0.00183 | outside the certified domain | room is not positive; largest term a |
| `t6007` | 1 | 5 | 4 | no | 0.02025 | 0.00487 | 0.00483 | -0.00903 | 0.00386 | outside the certified domain | room is not positive; largest term a |
| `t6007` | 2 | 3 | 3 | yes | 0.01499 | 0.00732 | 0.00451 | -0.00589 | 0.00371 | outside the certified domain | room is not positive; largest term a |
| `t6008` | 1 | 3 | 3 | yes | 0.00533 | 0.00270 | 0.00514 | +0.00775 | 0.00077 | certified, count confirmed | — |
| `t6008` | 2 | 4 | 4 | yes | 0.01597 | 0.01019 | 0.00500 | -0.01024 | 0.00443 | outside the certified domain | room is not positive; largest term a |
| `t6009` | 1 | 3 | 3 | yes | 0.01745 | 0.00529 | 0.00406 | -0.00588 | 0.00322 | outside the certified domain | room is not positive; largest term a |
| `t6009` | 2 | 3 | 3 | yes | 0.00512 | 0.00408 | 0.00492 | +0.00680 | 0.00219 | certified, count confirmed | — |
| `t6010` | 1 | 4 | 4 | yes | 0.00741 | 0.00433 | 0.00502 | +0.00416 | 0.00271 | certified, count confirmed | — |
| `t6010` | 2 | 6 | 6 | yes | 0.01079 | 0.00669 | 0.00454 | -0.00109 | 0.00461 | outside the certified domain | room is not positive; largest term a |
| `t6011` | 1 | 4 | 4 | yes | 0.00178 | 0.00494 | 0.00488 | +0.00932 | 0.00258 | outside the certified domain | a rest state is outside the band |
| `t6011` | 2 | 5 | 5 | yes | 0.00306 | 0.00853 | 0.00417 | +0.00516 | 0.00646 | certified, count confirmed | — |
| `t6012` | 1 | 4 | 4 | yes | 0.00222 | 0.00516 | 0.00460 | +0.00895 | 0.00257 | certified, count confirmed | — |
| `t6012` | 2 | 5 | 5 | yes | 0.01483 | 0.00902 | 0.00466 | -0.00759 | 0.00407 | outside the certified domain | room is not positive; largest term a |
| `t6013` | 1 | 4 | 4 | yes | 0.01283 | 0.00834 | 0.00529 | -0.00554 | 0.00350 | outside the certified domain | room is not positive; largest term a |
| `t6013` | 2 | 3 | 3 | yes | 0.00520 | 0.00532 | 0.00448 | +0.00592 | 0.00178 | certified, count confirmed | — |
| `t6014` | 1 | 3 | 3 | yes | 0.01996 | 0.00720 | 0.00446 | -0.01070 | 0.00496 | outside the certified domain | room is not positive; largest term a |
| `t6014` | 2 | 5 | 5 | yes | 0.01580 | 0.00831 | 0.00485 | -0.00804 | 0.00302 | outside the certified domain | room is not positive; largest term a |
| `t6015` | 1 | 4 | 4 | yes | 0.00461 | 0.00676 | 0.00491 | +0.00464 | 0.00469 | certified, count confirmed | — |
| `t6015` | 2 | 5 | 5 | yes | 0.01455 | 0.00759 | 0.00538 | -0.00660 | 0.00302 | outside the certified domain | room is not positive; largest term a |
| `t6016` | 1 | 4 | 4 | yes | 0.00833 | 0.00698 | 0.00432 | +0.00129 | 0.00530 | certified, count confirmed | — |
| `t6016` | 2 | 5 | 5 | yes | 0.01500 | 0.00540 | 0.00506 | -0.00454 | 0.00467 | outside the certified domain | room is not positive; largest term a |
| `t6017` | 1 | 4 | 4 | yes | 0.01066 | 0.00633 | 0.00455 | -0.00062 | 0.00305 | outside the certified domain | room is not positive; largest term a |
| `t6017` | 2 | 3 | 3 | yes | 0.01114 | 0.00519 | 0.00494 | -0.00035 | 0.00288 | outside the certified domain | room is not positive; largest term a |
| `t6018` | 1 | 4 | 4 | yes | 0.01527 | 0.00702 | 0.00450 | -0.00586 | 0.00269 | outside the certified domain | room is not positive; largest term a |
| `t6018` | 2 | 3 | 3 | yes | 0.00365 | 0.00650 | 0.00530 | +0.00548 | 0.00405 | certified, count confirmed | — |
| `t6019` | 1 | 4 | 4 | yes | 0.02242 | 0.01194 | 0.00523 | -0.01866 | 0.00433 | outside the certified domain | room is not positive; largest term a |
| `t6019` | 2 | 4 | 4 | yes | 0.00765 | 0.00599 | 0.00596 | +0.00132 | 0.00449 | certified, count confirmed | — |
| `t6020` | 1 | 4 | 4 | yes | 0.01977 | 0.00924 | 0.00550 | -0.01358 | 0.00484 | outside the certified domain | room is not positive; largest term a |
| `t6020` | 2 | 4 | 4 | yes | 0.00605 | 0.01259 | 0.00509 | -0.00282 | 0.00770 | outside the certified domain | room is not positive; largest term B |
| `t6021` | 1 | 5 | 6 | no | 0.02768 | 0.00830 | 0.00459 | -0.01965 | 0.00664 | outside the certified domain | room is not positive; largest term a |
| `t6021` | 2 | 5 | 5 | yes | 0.01234 | 0.00668 | 0.00465 | -0.00274 | 0.00370 | outside the certified domain | room is not positive; largest term a |
| `t6022` | 1 | 3 | 3 | yes | 0.01675 | 0.00725 | 0.00448 | -0.00755 | 0.00518 | outside the certified domain | room is not positive; largest term a |
| `t6022` | 2 | 4 | 4 | yes | 0.02044 | 0.00997 | 0.00488 | -0.01437 | 0.00470 | outside the certified domain | room is not positive; largest term a |
| `t6023` | 1 | 4 | 4 | yes | 0.01664 | 0.00659 | 0.00443 | -0.00674 | 0.00452 | outside the certified domain | room is not positive; largest term a |
| `t6023` | 2 | 3 | 3 | yes | 0.01814 | 0.00438 | 0.00495 | -0.00655 | 0.00416 | outside the certified domain | room is not positive; largest term a |
| `t6024` | 1 | 3 | 3 | yes | 0.01574 | 0.00816 | 0.00473 | -0.00771 | 0.00510 | outside the certified domain | room is not positive; largest term a |
| `t6024` | 2 | 6 | 5 | no | 0.02287 | 0.00619 | 0.00417 | -0.01231 | 0.00561 | outside the certified domain | room is not positive; largest term a |
| `t6025` | 1 | 4 | 4 | yes | 0.00864 | 0.00692 | 0.00529 | +0.00008 | 0.00446 | certified, count confirmed | — |
| `t6025` | 2 | 4 | 4 | yes | 0.01941 | 0.00407 | 0.00428 | -0.00683 | 0.00252 | outside the certified domain | room is not positive; largest term a |
| `t6026` | 1 | 4 | 4 | yes | 0.01386 | 0.00699 | 0.00445 | -0.00438 | 0.00517 | outside the certified domain | room is not positive; largest term a |
| `t6026` | 2 | 4 | 4 | yes | 0.01451 | 0.00568 | 0.00519 | -0.00446 | 0.00237 | outside the certified domain | room is not positive; largest term a |
| `t6027` | 1 | 5 | 5 | yes | 0.01306 | 0.00654 | 0.00478 | -0.00346 | 0.00638 | outside the certified domain | room is not positive; largest term a |
| `t6027` | 2 | 3 | 3 | yes | 0.00856 | 0.00723 | 0.00492 | +0.00021 | 0.00463 | certified, count confirmed | — |
| `t6028` | 1 | 5 | 5 | yes | 0.01213 | 0.00727 | 0.00455 | -0.00303 | 0.00626 | outside the certified domain | room is not positive; largest term a |
| `t6028` | 2 | 4 | 4 | yes | 0.00512 | 0.00516 | 0.00542 | +0.00523 | 0.00364 | certified, count confirmed | — |
| `t6029` | 1 | 4 | 4 | yes | 0.01255 | 0.00646 | 0.00492 | -0.00300 | 0.00353 | outside the certified domain | room is not positive; largest term a |
| `t6029` | 2 | 5 | 5 | yes | 0.01711 | 0.00873 | 0.00497 | -0.00989 | 0.00971 | outside the certified domain | room is not positive; largest term a |
| `t6030` | 1 | 3 | 3 | yes | 0.00552 | 0.00698 | 0.00497 | +0.00345 | 0.00507 | certified, count confirmed | — |
| `t6030` | 2 | 4 | 5 | no | 0.02500 | 0.00511 | 0.00460 | -0.01378 | 0.00433 | outside the certified domain | room is not positive; largest term a |
| `t6031` | 1 | 4 | 4 | yes | 0.00732 | 0.00611 | 0.00502 | +0.00247 | 0.00641 | certified, count confirmed | — |
| `t6031` | 2 | 5 | 5 | yes | 0.01327 | 0.00901 | 0.00409 | -0.00545 | 0.00512 | outside the certified domain | room is not positive; largest term a |
| `t6032` | 1 | 3 | 3 | yes | 0.00207 | 0.00844 | 0.00475 | +0.00566 | 0.00387 | certified, count confirmed | — |
| `t6032` | 2 | 4 | 4 | yes | 0.00472 | 0.00493 | 0.00565 | +0.00562 | 0.00247 | certified, count confirmed | — |
| `t6033` | 1 | 4 | 4 | yes | 0.01831 | 0.00447 | 0.00542 | -0.00728 | 0.00180 | outside the certified domain | room is not positive; largest term a |
| `t6033` | 2 | 2 | 2 | yes | 0.01408 | 0.00447 | 0.00443 | -0.00206 | 0.00240 | outside the certified domain | room is not positive; largest term a |
| `t6034` | 1 | 4 | 4 | yes | 0.01488 | 0.00590 | 0.00488 | -0.00473 | 0.00174 | outside the certified domain | room is not positive; largest term a |
| `t6034` | 2 | 5 | 5 | yes | 0.02031 | 0.00794 | 0.00480 | -0.01212 | 0.00587 | outside the certified domain | room is not positive; largest term a |
| `t6035` | 1 | 5 | 5 | yes | 0.02009 | 0.01010 | 0.00437 | -0.01363 | 0.00803 | outside the certified domain | room is not positive; largest term a |
| `t6035` | 2 | 5 | 5 | yes | 0.01728 | 0.00444 | 0.00450 | -0.00530 | 0.00344 | outside the certified domain | room is not positive; largest term a |
| `t6036` | 1 | 5 | 5 | yes | 0.02153 | 0.00450 | 0.00488 | -0.00999 | 0.00243 | outside the certified domain | room is not positive; largest term a |
| `t6036` | 2 | 4 | 4 | yes | 0.01386 | 0.00939 | 0.00488 | -0.00720 | 0.00358 | outside the certified domain | room is not positive; largest term a |
| `t6037` | 1 | 4 | 4 | yes | 0.00711 | 0.00779 | 0.00486 | +0.00115 | 0.00657 | certified, count confirmed | — |
| `t6037` | 2 | 4 | 4 | yes | 0.01065 | 0.00451 | 0.00455 | +0.00122 | 0.00189 | certified, count confirmed | — |
| `t6038` | 1 | 4 | 4 | yes | 0.01002 | 0.00590 | 0.00481 | +0.00019 | 0.00314 | certified, count confirmed | — |
| `t6038` | 2 | 4 | 4 | yes | 0.01512 | 0.00617 | 0.00495 | -0.00532 | 0.00454 | outside the certified domain | room is not positive; largest term a |
| `t6039` | 1 | 3 | 3 | yes | 0.01157 | 0.00545 | 0.00486 | -0.00095 | 0.00317 | outside the certified domain | room is not positive; largest term a |
| `t6039` | 2 | 3 | 3 | yes | 0.01051 | 0.00628 | 0.00481 | -0.00068 | 0.00548 | outside the certified domain | room is not positive; largest term a |
| `t6040` | 1 | 5 | 5 | yes | 0.02220 | 0.01006 | 0.00530 | -0.01664 | 0.00510 | outside the certified domain | room is not positive; largest term a |
| `t6040` | 2 | 5 | 5 | yes | 0.00461 | 0.00774 | 0.00538 | +0.00319 | 0.00269 | certified, count confirmed | — |
| `t6041` | 1 | 5 | 5 | yes | 0.00638 | 0.01165 | 0.00593 | -0.00304 | 0.00514 | outside the certified domain | room is not positive; largest term B |
| `t6041` | 2 | 6 | 6 | yes | 0.01582 | 0.00676 | 0.00535 | -0.00701 | 0.00407 | outside the certified domain | room is not positive; largest term a |
| `t6042` | 1 | 4 | 4 | yes | 0.01878 | 0.00603 | 0.00463 | -0.00852 | 0.00539 | outside the certified domain | room is not positive; largest term a |
| `t6042` | 2 | 5 | 5 | yes | 0.00675 | 0.00570 | 0.00506 | +0.00341 | 0.00359 | certified, count confirmed | — |
| `t6043` | 1 | 5 | 5 | yes | 0.02150 | 0.00673 | 0.00521 | -0.01251 | 0.00439 | outside the certified domain | room is not positive; largest term a |
| `t6043` | 2 | 5 | 5 | yes | 0.00167 | 0.00800 | 0.00529 | +0.00597 | 0.00240 | certified, count confirmed | — |
| `t6044` | 1 | 2 | 2 | yes | 0.02652 | 0.00653 | 0.00405 | -0.01618 | 0.00446 | outside the certified domain | room is not positive; largest term a |
| `t6044` | 2 | 3 | 3 | yes | 0.01257 | 0.00446 | 0.00466 | -0.00078 | 0.00280 | outside the certified domain | room is not positive; largest term a |
| `t6045` | 1 | 4 | 4 | yes | 0.01195 | 0.00652 | 0.00452 | -0.00208 | 0.00411 | outside the certified domain | room is not positive; largest term a |
| `t6045` | 2 | 4 | 4 | yes | 0.00769 | 0.00794 | 0.00454 | +0.00075 | 0.00369 | certified, count confirmed | — |
| `t6046` | 1 | 3 | 3 | yes | 0.01739 | 0.00622 | 0.00444 | -0.00712 | 0.00561 | outside the certified domain | room is not positive; largest term a |
| `t6046` | 2 | 4 | 4 | yes | 0.02210 | 0.00717 | 0.00473 | -0.01307 | 0.00684 | outside the certified domain | room is not positive; largest term a |
| `t6047` | 1 | 4 | 4 | yes | 0.01179 | 0.00577 | 0.00554 | -0.00217 | 0.00323 | outside the certified domain | room is not positive; largest term a |
| `t6047` | 2 | 5 | 5 | yes | 0.01639 | 0.00605 | 0.00478 | -0.00630 | 0.00232 | outside the certified domain | room is not positive; largest term a |
| `t6048` | 1 | 5 | 5 | yes | 0.02222 | 0.00522 | 0.00511 | -0.01163 | 0.00377 | outside the certified domain | room is not positive; largest term a |
| `t6048` | 2 | 4 | 4 | yes | 0.01556 | 0.00696 | 0.00524 | -0.00685 | 0.00339 | outside the certified domain | room is not positive; largest term a |
| `t6049` | 1 | 4 | 4 | yes | 0.02349 | 0.00680 | 0.00451 | -0.01387 | 0.00473 | outside the certified domain | room is not positive; largest term a |
| `t6049` | 2 | 4 | 4 | yes | 0.01000 | 0.00713 | 0.00441 | -0.00062 | 0.00506 | outside the certified domain | room is not positive; largest term a |
| `t6050` | 1 | 3 | 3 | yes | 0.02277 | 0.00703 | 0.00493 | -0.01381 | 0.00496 | outside the certified domain | room is not positive; largest term a |
| `t6050` | 2 | 4 | 4 | yes | 0.00480 | 0.00761 | 0.00458 | +0.00392 | 0.00601 | certified, count confirmed | — |
| `t6051` | 1 | 4 | 4 | yes | 0.01156 | 0.00380 | 0.00437 | +0.00119 | 0.00140 | outside the certified domain | a rest state is outside the band |
| `t6051` | 2 | 3 | 3 | yes | 0.00130 | 0.00612 | 0.00463 | +0.00887 | 0.00370 | certified, count confirmed | — |
| `t6052` | 1 | 4 | 4 | yes | 0.00768 | 0.00592 | 0.00515 | +0.00218 | 0.00294 | certified, count confirmed | — |
| `t6052` | 2 | 4 | 4 | yes | 0.01922 | 0.00408 | 0.00478 | -0.00716 | 0.00308 | outside the certified domain | room is not positive; largest term a |
| `t6053` | 1 | 3 | 3 | yes | 0.01442 | 0.01025 | 0.00594 | -0.00969 | 0.00818 | outside the certified domain | room is not positive; largest term a |
| `t6053` | 2 | 4 | 4 | yes | 0.01417 | 0.00463 | 0.00465 | -0.00253 | 0.00169 | outside the certified domain | room is not positive; largest term a |
| `t6054` | 1 | 4 | 4 | yes | 0.01280 | 0.00677 | 0.00483 | -0.00348 | 0.00444 | outside the certified domain | room is not positive; largest term a |
| `t6054` | 2 | 4 | 4 | yes | 0.02029 | 0.00796 | 0.00515 | -0.01247 | 0.00297 | outside the certified domain | room is not positive; largest term a |
| `t6055` | 1 | 6 | 6 | yes | 0.00948 | 0.00533 | 0.00455 | +0.00156 | 0.00319 | certified, count confirmed | — |
| `t6055` | 2 | 5 | 5 | yes | 0.02008 | 0.00806 | 0.00500 | -0.01222 | 0.00351 | outside the certified domain | room is not positive; largest term a |
| `t6056` | 1 | 5 | 5 | yes | 0.00880 | 0.00561 | 0.00525 | +0.00127 | 0.00469 | certified, count confirmed | — |
| `t6056` | 2 | 3 | 3 | yes | 0.02138 | 0.00596 | 0.00531 | -0.01173 | 0.00389 | outside the certified domain | room is not positive; largest term a |
| `t6057` | 1 | 6 | 6 | yes | 0.02263 | 0.00677 | 0.00494 | -0.01342 | 0.00477 | outside the certified domain | room is not positive; largest term a |
| `t6057` | 2 | 5 | 5 | yes | 0.00822 | 0.01076 | 0.00520 | -0.00325 | 0.00869 | outside the certified domain | room is not positive; largest term B |
| `t6058` | 1 | 4 | 4 | yes | 0.02130 | 0.00767 | 0.00477 | -0.01282 | 0.00543 | outside the certified domain | room is not positive; largest term a |
| `t6058` | 2 | 4 | 4 | yes | 0.00378 | 0.00881 | 0.00463 | +0.00370 | 0.00678 | certified, count confirmed | — |
| `t6059` | 1 | 4 | 4 | yes | 0.01375 | 0.00628 | 0.00484 | -0.00395 | 0.00314 | outside the certified domain | room is not positive; largest term a |
| `t6059` | 2 | 5 | 5 | yes | 0.01499 | 0.00680 | 0.00453 | -0.00540 | 0.00490 | outside the certified domain | room is not positive; largest term a |
| `t6060` | 1 | 5 | 5 | yes | 0.01829 | 0.00808 | 0.00452 | -0.00997 | 0.00611 | outside the certified domain | room is not positive; largest term a |
| `t6060` | 2 | 4 | 4 | yes | 0.01434 | 0.00656 | 0.00427 | -0.00425 | 0.00382 | outside the certified domain | room is not positive; largest term a |
| `t6061` | 1 | 4 | 4 | yes | 0.01928 | 0.00592 | 0.00463 | -0.00891 | 0.00291 | outside the certified domain | room is not positive; largest term a |
| `t6061` | 2 | 3 | 3 | yes | 0.00732 | 0.00555 | 0.00462 | +0.00343 | 0.00263 | certified, count confirmed | — |
| `t6062` | 1 | 4 | 4 | yes | 0.01063 | 0.00683 | 0.00449 | -0.00103 | 0.00476 | outside the certified domain | room is not positive; largest term a |
| `t6062` | 2 | 3 | 3 | yes | 0.02228 | 0.00761 | 0.00517 | -0.01413 | 0.00624 | outside the certified domain | room is not positive; largest term a |
| `t6063` | 1 | 2 | 2 | yes | 0.00472 | 0.00440 | 0.00435 | +0.00746 | 0.00353 | certified, count confirmed | — |
| `t6063` | 2 | 4 | 3 | no | 0.02368 | 0.00585 | 0.00424 | -0.01285 | 0.00241 | outside the certified domain | room is not positive; largest term a |
| `t6064` | 1 | 5 | 5 | yes | 0.01829 | 0.00418 | 0.00470 | -0.00624 | 0.00261 | outside the certified domain | room is not positive; largest term a |
| `t6064` | 2 | 3 | 3 | yes | 0.01765 | 0.00699 | 0.00498 | -0.00870 | 0.00507 | outside the certified domain | room is not positive; largest term a |
| `t6065` | 1 | 4 | 4 | yes | 0.00045 | 0.00333 | 0.00436 | +0.01277 | 0.00100 | certified, count confirmed | — |
| `t6065` | 2 | 3 | 3 | yes | 0.01765 | 0.00552 | 0.00494 | -0.00718 | 0.00386 | outside the certified domain | room is not positive; largest term a |
| `t6066` | 1 | 5 | 5 | yes | 0.01599 | 0.00694 | 0.00466 | -0.00667 | 0.00306 | outside the certified domain | room is not positive; largest term a |
| `t6066` | 2 | 4 | 4 | yes | 0.01686 | 0.00743 | 0.00424 | -0.00761 | 0.00808 | outside the certified domain | room is not positive; largest term a |
| `t6067` | 1 | 4 | 4 | yes | 0.01833 | 0.00566 | 0.00552 | -0.00859 | 0.00416 | outside the certified domain | room is not positive; largest term a |
| `t6067` | 2 | 3 | 3 | yes | 0.00433 | 0.00677 | 0.00464 | +0.00518 | 0.00470 | certified, count confirmed | — |
| `t6068` | 1 | 4 | 4 | yes | 0.01497 | 0.00439 | 0.00474 | -0.00318 | 0.00221 | outside the certified domain | room is not positive; largest term a |
| `t6068` | 2 | 2 | 2 | yes | 0.00780 | 0.00397 | 0.00467 | +0.00448 | 0.00269 | certified, count confirmed | — |
| `t6069` | 1 | 5 | 5 | yes | 0.02670 | 0.00576 | 0.00437 | -0.01591 | 0.00408 | outside the certified domain | room is not positive; largest term a |
| `t6069` | 2 | 4 | 5 | no | 0.02286 | 0.00564 | 0.00447 | -0.01204 | 0.00697 | outside the certified domain | room is not positive; largest term a |
| `t6070` | 1 | 5 | 5 | yes | 0.02019 | 0.01061 | 0.00478 | -0.01466 | 0.00813 | outside the certified domain | room is not positive; largest term a |
| `t6070` | 2 | 4 | 4 | yes | 0.01307 | 0.00829 | 0.00589 | -0.00633 | 0.00312 | outside the certified domain | room is not positive; largest term a |
| `t6071` | 1 | 2 | 2 | yes | 0.01008 | 0.00827 | 0.00540 | -0.00282 | 0.00463 | outside the certified domain | room is not positive; largest term a |
| `t6071` | 2 | 5 | 5 | yes | 0.01321 | 0.00764 | 0.00589 | -0.00583 | 0.00617 | outside the certified domain | room is not positive; largest term a |
| `t6072` | 1 | 3 | 4 | no | 0.02866 | 0.00895 | 0.00468 | -0.02138 | 0.00428 | outside the certified domain | room is not positive; largest term a |
| `t6072` | 2 | 4 | 4 | yes | 0.01409 | 0.00692 | 0.00462 | -0.00471 | 0.00454 | outside the certified domain | room is not positive; largest term a |
| `t6073` | 1 | 4 | 4 | yes | 0.01589 | 0.01050 | 0.00482 | -0.01029 | 0.00502 | outside the certified domain | room is not positive; largest term a |
| `t6073` | 2 | 5 | 5 | yes | 0.02062 | 0.00651 | 0.00551 | -0.01172 | 0.00484 | outside the certified domain | room is not positive; largest term a |
| `t6074` | 1 | 3 | 3 | yes | 0.00267 | 0.00467 | 0.00452 | +0.00907 | 0.00260 | certified, count confirmed | — |
| `t6074` | 2 | 2 | 3 | no | 0.02271 | 0.00308 | 0.00439 | -0.00926 | 0.00388 | outside the certified domain | room is not positive; largest term a |
| `t6075` | 1 | 3 | 3 | yes | 0.00964 | 0.00937 | 0.00419 | -0.00228 | 0.00460 | outside the certified domain | room is not positive; largest term a |
| `t6075` | 2 | 4 | 4 | yes | 0.00261 | 0.00533 | 0.00510 | +0.00789 | 0.00310 | certified, count confirmed | — |
| `t6076` | 1 | 4 | 4 | yes | 0.00465 | 0.00884 | 0.00544 | +0.00199 | 0.00595 | certified, count confirmed | — |
| `t6076` | 2 | 4 | 4 | yes | 0.01302 | 0.00509 | 0.00553 | -0.00272 | 0.00443 | outside the certified domain | room is not positive; largest term a |
| `t6077` | 1 | 5 | 5 | yes | 0.00571 | 0.00612 | 0.00468 | +0.00441 | 0.00544 | certified, count confirmed | — |
| `t6077` | 2 | 5 | 5 | yes | 0.00313 | 0.00723 | 0.00451 | +0.00605 | 0.00516 | certified, count confirmed | — |
| `t6078` | 1 | 4 | 4 | yes | 0.01838 | 0.00710 | 0.00450 | -0.00906 | 0.00452 | outside the certified domain | room is not positive; largest term a |
| `t6078` | 2 | 5 | 5 | yes | 0.01309 | 0.00886 | 0.00467 | -0.00570 | 0.00766 | outside the certified domain | room is not positive; largest term a |
| `t6079` | 1 | 4 | 4 | yes | 0.00490 | 0.00436 | 0.00444 | +0.00722 | 0.00350 | certified, count confirmed | — |
| `t6079` | 2 | 4 | 4 | yes | 0.00754 | 0.00712 | 0.00578 | +0.00048 | 0.00758 | certified, count confirmed | — |
| `t6080` | 1 | 4 | 4 | yes | 0.01382 | 0.00635 | 0.00455 | -0.00380 | 0.00709 | outside the certified domain | room is not positive; largest term a |
| `t6080` | 2 | 3 | 3 | yes | 0.00554 | 0.00986 | 0.00477 | +0.00075 | 0.00553 | certified, count confirmed | — |
| `t6081` | 1 | 4 | 4 | yes | 0.00994 | 0.00598 | 0.00431 | +0.00069 | 0.00544 | certified, count confirmed | — |
| `t6081` | 2 | 4 | 4 | yes | 0.01325 | 0.00442 | 0.00436 | -0.00111 | 0.00269 | outside the certified domain | room is not positive; largest term a |
| `t6082` | 1 | 5 | 5 | yes | 0.01882 | 0.00426 | 0.00479 | -0.00695 | 0.00362 | outside the certified domain | room is not positive; largest term a |
| `t6082` | 2 | 4 | 4 | yes | 0.00807 | 0.00583 | 0.00422 | +0.00280 | 0.00504 | certified, count confirmed | — |
| `t6083` | 1 | 4 | 4 | yes | 0.01987 | 0.00506 | 0.00525 | -0.00926 | 0.00299 | outside the certified domain | room is not positive; largest term a |
| `t6083` | 2 | 4 | 4 | yes | 0.01138 | 0.00441 | 0.00494 | +0.00020 | 0.00299 | certified, count confirmed | — |
| `t6084` | 1 | 4 | 4 | yes | 0.01144 | 0.00759 | 0.00494 | -0.00305 | 0.00406 | outside the certified domain | room is not positive; largest term a |
| `t6084` | 2 | 4 | 4 | yes | 0.02258 | 0.00815 | 0.00459 | -0.01440 | 0.00608 | outside the certified domain | room is not positive; largest term a |
| `t6085` | 1 | 4 | 4 | yes | 0.01421 | 0.00406 | 0.00452 | -0.00186 | 0.00321 | outside the certified domain | room is not positive; largest term a |
| `t6085` | 2 | 3 | 3 | yes | 0.00716 | 0.00678 | 0.00429 | +0.00269 | 0.00492 | certified, count confirmed | — |
| `t6086` | 1 | 5 | 5 | yes | 0.01059 | 0.00616 | 0.00480 | -0.00064 | 0.00366 | outside the certified domain | room is not positive; largest term a |
| `t6086` | 2 | 4 | 4 | yes | 0.02315 | 0.00513 | 0.00429 | -0.01165 | 0.00521 | outside the certified domain | room is not positive; largest term a |
| `t6087` | 1 | 4 | 5 | no | 0.02167 | 0.00432 | 0.00571 | -0.01078 | 0.00368 | outside the certified domain | room is not positive; largest term a |
| `t6087` | 2 | 4 | 4 | yes | 0.01514 | 0.00610 | 0.00476 | -0.00509 | 0.00536 | outside the certified domain | room is not positive; largest term a |
| `t6088` | 1 | 5 | 5 | yes | 0.01300 | 0.00553 | 0.00458 | -0.00220 | 0.00374 | outside the certified domain | room is not positive; largest term a |
| `t6088` | 2 | 4 | 4 | yes | 0.00351 | 0.00739 | 0.00478 | +0.00524 | 0.00487 | certified, count confirmed | — |
| `t6089` | 1 | 5 | 5 | yes | 0.01974 | 0.00921 | 0.00415 | -0.01218 | 0.00712 | outside the certified domain | room is not positive; largest term a |
| `t6089` | 2 | 4 | 3 | no | 0.02243 | 0.00511 | 0.00489 | -0.01151 | 0.00284 | outside the certified domain | room is not positive; largest term a |
| `t6090` | 1 | 4 | 4 | yes | 0.00622 | 0.00762 | 0.00423 | +0.00285 | 0.00364 | certified, count confirmed | — |
| `t6090` | 2 | 4 | 4 | yes | 0.01347 | 0.00532 | 0.00473 | -0.00259 | 0.00493 | outside the certified domain | room is not positive; largest term a |
| `t6091` | 1 | 6 | 6 | yes | 0.01612 | 0.00641 | 0.00499 | -0.00660 | 0.00346 | outside the certified domain | room is not positive; largest term a |
| `t6091` | 2 | 5 | 5 | yes | 0.01617 | 0.00657 | 0.00456 | -0.00637 | 0.00365 | outside the certified domain | room is not positive; largest term a |
| `t6092` | 1 | 3 | 3 | yes | 0.02153 | 0.00435 | 0.00469 | -0.00965 | 0.00294 | outside the certified domain | room is not positive; largest term a |
| `t6092` | 2 | 3 | 3 | yes | 0.01044 | 0.00700 | 0.00468 | -0.00120 | 0.00401 | outside the certified domain | room is not positive; largest term a |
| `t6093` | 1 | 4 | 4 | yes | 0.02105 | 0.00965 | 0.00460 | -0.01438 | 0.00567 | outside the certified domain | room is not positive; largest term a |
| `t6093` | 2 | 4 | 4 | yes | 0.00843 | 0.00592 | 0.00499 | +0.00159 | 0.00368 | certified, count confirmed | — |
| `t6094` | 1 | 4 | 4 | yes | 0.01247 | 0.00542 | 0.00519 | -0.00217 | 0.00420 | outside the certified domain | room is not positive; largest term a |
| `t6094` | 2 | 5 | 5 | yes | 0.02120 | 0.00507 | 0.00537 | -0.01072 | 0.00315 | outside the certified domain | room is not positive; largest term a |
| `t6095` | 1 | 3 | 3 | yes | 0.01296 | 0.00593 | 0.00577 | -0.00373 | 0.00635 | outside the certified domain | room is not positive; largest term a |
| `t6095` | 2 | 3 | 3 | yes | 0.00871 | 0.00476 | 0.00493 | +0.00253 | 0.00382 | certified, count confirmed | — |
| `t6096` | 1 | 3 | 3 | yes | 0.00356 | 0.00559 | 0.00503 | +0.00674 | 0.00352 | certified, count confirmed | — |
| `t6096` | 2 | 5 | 5 | yes | 0.01920 | 0.00768 | 0.00462 | -0.01059 | 0.00566 | outside the certified domain | room is not positive; largest term a |
| `t6097` | 1 | 3 | 4 | no | 0.02114 | 0.00387 | 0.00492 | -0.00902 | 0.00459 | outside the certified domain | room is not positive; largest term a |
| `t6097` | 2 | 5 | 5 | yes | 0.00875 | 0.00797 | 0.00519 | -0.00098 | 0.00647 | outside the certified domain | room is not positive; largest term a |
| `t6098` | 1 | 3 | 3 | yes | 0.01475 | 0.00753 | 0.00505 | -0.00642 | 0.00634 | outside the certified domain | room is not positive; largest term a |
| `t6098` | 2 | 5 | 5 | yes | 0.00345 | 0.00518 | 0.00553 | +0.00676 | 0.00509 | certified, count confirmed | — |
| `t6099` | 1 | 5 | 5 | yes | 0.00839 | 0.00711 | 0.00435 | +0.00108 | 0.00540 | certified, count confirmed | — |
| `t6099` | 2 | 6 | 6 | yes | 0.01726 | 0.00685 | 0.00482 | -0.00800 | 0.00292 | outside the certified domain | room is not positive; largest term a |
| `t6100` | 1 | 6 | 6 | yes | 0.01589 | 0.00792 | 0.00516 | -0.00805 | 0.00426 | outside the certified domain | room is not positive; largest term a |
| `t6100` | 2 | 5 | 5 | yes | 0.01001 | 0.00578 | 0.00574 | -0.00062 | 0.00617 | outside the certified domain | room is not positive; largest term a |

## Traces and reproduction

- **Extraction.** Every value of a run is extracted by `cert_run.py` when the run ends. The script was pushed in commit `5b9d75f`, before the first run. Its SHA-256 now is `e389e8fddb1dee43a1e9e0c26730a52da6ed9c85c2c36ebaf99e005076be5c43`: identical to the file of that commit.
- **What is public.** For each run: one row per pulse with every quantity that enters a bound (`results/<stage>/<run>.csv`), and its metadata with the SHA-256 of the deck, of the binary, of the rows and of the compact trace (`results/<stage>/<run>.json`).
- **Traces.** The compact trace of a run holds the solver points around each pulse and each write window, as `PREDICTION.md` says. The traces are in the private repository `HevisNico/kernel-R-circuit`, folder `07-certification-traces/`; 350 of the 350 runs with a result have the hash of their trace in their public metadata. That hash is the hash of the compact trace, not of the full solver output, which is not kept. Amendment 1 said that no trace would be kept; amendment 2 withdrew it before the runs of stages 2 and 3.
- **Reproduction.** Each run is made once. In the original campaign a run without noise replayed from its deck gave the same output byte for byte. The 100 runs with noise are not reproduced by their seed. Their extraction can be checked again only from the compact traces; their statistics can be reproduced by new runs, not their values.
