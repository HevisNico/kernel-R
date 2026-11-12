# Decomposition of the budget, and the cumulative budget

Written by `cumulative_analyze.py` under `CUMULATIVE_PROTOCOL.md`, a rule declared after the result of
[`BRIDGE_APPLICATION.md`](../BRIDGE_APPLICATION.md): **no port is in the certified domain**. That result is not changed by anything here.

## Part 1. Which term makes the per-write budget fail

`b = k*eta + sigma + e`, measured on the nominal replays: 1.32e-03 + 7.47e-05 + (9.83e-04 + 2.61e-03) = **0.00499** per write. The local calibration error is 52% of it and the transfer residual 26%. `d0/2` is about 0.0211.

- Ports evaluated: 200 of 200. Positive room under these estimates: **19**, of which the count disagrees on 0. This is not a certificate.
- Largest term of the budget: `m*b` on 180 ports, `a` on 20 ports.
- Port with the largest room: `mc_2084`, port 1, with `m` = 2, `a` = 0.00374, `m*b` = 0.00997, room +0.01048. Its `b` could be 2.1 times larger.
- For the median port `b` would have to be divided by 2.0: from 0.0050 to 0.0026 per write, 6% of a dose. On 1 port no `b` suffices: `a` alone exceeds what `d0/2` leaves.

| m | Ports | `m*b` | Median `a` | Median room | Largest room | Median `b_max` | `b / b_max`, median |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 0.00499 | 0.00652 | +0.00950 | +0.00950 | +0.01449 | 0.3 |
| 2 | 8 | 0.00997 | 0.00631 | +0.00651 | +0.01048 | +0.00824 | 0.6 |
| 3 | 43 | 0.01496 | 0.00984 | -0.00415 | +0.00645 | +0.00360 | 1.4 |
| 4 | 75 | 0.01995 | 0.00987 | -0.00850 | +0.00124 | +0.00286 | 1.7 |
| 5 | 63 | 0.02494 | 0.01151 | -0.01527 | -0.00338 | +0.00193 | 2.6 |
| 6 | 10 | 0.02992 | 0.01406 | -0.02285 | -0.01262 | +0.00118 | 4.4 |

`b` is one number, measured on nominal devices and applied to every port as an estimate. `ell` is 0 where it is not measured, that is everywhere except cell 2064.

## Part 2. The cumulative budget

Lean: `needAlong_of_cumulative_tolerance`. `B = max over n <= m of |beta*(V(0)-V(n)) - n*d0| + epsilon*|V(0)-V(n)|`, from the stored voltages of the original runs, with `beta` = 31.377 and `epsilon` = 1.937 per V.

| Status | Ports |
|---|---|
| outside the sufficient region | 128 |
| inside under estimates, count agrees | 69 |
| not evaluable | 3 |

- Median `B` over the 197 ports with a value: 0.01376, of which calibration 0.01050 and distance of the measured cumulated gain to `n*d0` 0.00278.
- Port with the largest room: `mc_2044`, port 2: +0.01112.
- Inside under estimates: **69** ports, of which the count disagrees on **0**.

**Inside under estimates is not certified.** `a` and `d0` are peak-based proxies, `ell` is not measured for 99 cells, the calibration is that of nominal devices, a stored voltage of the campaign is a 40 µs average of a noisy signal, and the scalar read equation is not established. The count of certified ports stays 0.

## Cell 2064

| Port | Observed | m | Historical room, `ell = 0` | Per-write room | Writes | `B` | Cumulative room | Status |
|---|---|---|---|---|---|---|---|---|
| 1 | 3 | 4 | +0.000233 | -0.019133 | 4 | 0.01244 | -0.011628 | outside the sufficient region |
| 2 | 5 | 5 | -0.012314 | -0.017671 | 5 | 0.01533 | -0.008069 | outside the sufficient region |

## Ports inside under estimates

| Run | Port | Observed | m | `a` | `B` | Cumulative room | Count |
|---|---|---|---|---|---|---|---|
| `mc_2044` | 2 | 2 | 2 | 0.00179 | 0.00784 | +0.01112 | agrees |
| `mc_2028` | 2 | 3 | 3 | 0.00027 | 0.01110 | +0.01030 | agrees |
| `mc_2090` | 2 | 3 | 3 | 0.00197 | 0.00857 | +0.01029 | agrees |
| `mc_2027` | 2 | 1 | 1 | 0.00652 | 0.00462 | +0.00987 | agrees |
| `mc_2016` | 1 | 2 | 2 | 0.00608 | 0.00666 | +0.00929 | agrees |
| `mc_2100` | 2 | 3 | 3 | 0.00062 | 0.01146 | +0.00919 | agrees |
| `mc_2040` | 2 | 4 | 4 | 0.00049 | 0.01226 | +0.00861 | agrees |
| `mc_2017` | 2 | 4 | 4 | 0.00213 | 0.01063 | +0.00846 | agrees |
| `mc_2099` | 1 | 3 | 3 | 0.00545 | 0.00839 | +0.00792 | agrees |
| `mc_2074` | 2 | 4 | 4 | 0.00029 | 0.01331 | +0.00788 | agrees |
| `mc_2004` | 1 | 4 | 4 | 0.00149 | 0.01168 | +0.00787 | agrees |
| `mc_2069` | 1 | 4 | 4 | 0.00041 | 0.01281 | +0.00772 | agrees |
| `mc_2007` | 1 | 2 | 2 | 0.00390 | 0.01069 | +0.00743 | agrees |
| `mc_2009` | 1 | 3 | 3 | 0.00541 | 0.00887 | +0.00724 | agrees |
| `mc_2085` | 1 | 4 | 4 | 0.00191 | 0.01170 | +0.00702 | agrees |
| `mc_2082` | 1 | 3 | 3 | 0.00388 | 0.01057 | +0.00668 | agrees |
| `mc_2094` | 1 | 4 | 4 | 0.00356 | 0.01072 | +0.00655 | agrees |
| `mc_2033` | 1 | 4 | 4 | 0.00283 | 0.01226 | +0.00634 | agrees |
| `mc_2059` | 2 | 3 | 3 | 0.00455 | 0.00982 | +0.00634 | agrees |
| `mc_2065` | 2 | 4 | 4 | 0.00385 | 0.01122 | +0.00604 | agrees |
| `mc_2033` | 2 | 4 | 4 | 0.00432 | 0.01059 | +0.00577 | agrees |
| `mc_2091` | 2 | 3 | 3 | 0.00647 | 0.00861 | +0.00573 | agrees |
| `mc_2029` | 2 | 4 | 4 | 0.00312 | 0.01240 | +0.00568 | agrees |
| `mc_2066` | 1 | 4 | 4 | 0.00346 | 0.01213 | +0.00567 | agrees |
| `mc_2084` | 1 | 2 | 2 | 0.00374 | 0.01484 | +0.00561 | agrees |
| `mc_2006` | 2 | 3 | 3 | 0.00300 | 0.01258 | +0.00560 | agrees |
| `mc_2024` | 1 | 4 | 4 | 0.00240 | 0.01336 | +0.00536 | agrees |
| `mc_2079` | 2 | 4 | 4 | 0.00054 | 0.01437 | +0.00509 | agrees |
| `mc_2032` | 1 | 5 | 5 | 0.00057 | 0.01556 | +0.00496 | agrees |
| `mc_2088` | 1 | 5 | 5 | 0.00187 | 0.01438 | +0.00485 | agrees |
| `mc_2030` | 2 | 5 | 5 | 0.00071 | 0.01530 | +0.00472 | agrees |
| `mc_2070` | 2 | 5 | 5 | 0.00110 | 0.01491 | +0.00469 | agrees |
| `mc_2084` | 2 | 3 | 3 | 0.00715 | 0.00906 | +0.00469 | agrees |
| `mc_2089` | 1 | 5 | 5 | 0.00271 | 0.01357 | +0.00466 | agrees |
| `mc_2053` | 1 | 4 | 4 | 0.00254 | 0.01486 | +0.00460 | agrees |
| `mc_2053` | 2 | 3 | 3 | 0.00620 | 0.01089 | +0.00442 | agrees |
| `mc_2071` | 2 | 3 | 3 | 0.00717 | 0.01033 | +0.00421 | agrees |
| `mc_2052` | 2 | 4 | 4 | 0.00452 | 0.01204 | +0.00399 | agrees |
| `mc_2079` | 1 | 3 | 3 | 0.00689 | 0.00988 | +0.00398 | agrees |
| `mc_2006` | 1 | 3 | 3 | 0.00648 | 0.01006 | +0.00395 | agrees |
| `mc_2016` | 2 | 3 | 3 | 0.00788 | 0.00958 | +0.00372 | agrees |
| `mc_2048` | 2 | 4 | 4 | 0.00320 | 0.01509 | +0.00352 | agrees |
| `mc_2080` | 2 | 4 | 4 | 0.00271 | 0.01440 | +0.00339 | agrees |
| `mc_2025` | 2 | 3 | 3 | 0.00637 | 0.01180 | +0.00330 | agrees |
| `mc_2003` | 2 | 5 | 5 | 0.00258 | 0.01599 | +0.00311 | agrees |
| `mc_2018` | 1 | 5 | 5 | 0.00220 | 0.01569 | +0.00308 | agrees |
| `mc_2086` | 2 | 4 | 4 | 0.00592 | 0.01192 | +0.00303 | agrees |
| `mc_2051` | 1 | 5 | 5 | 0.00287 | 0.01567 | +0.00300 | agrees |
| `mc_2075` | 1 | 5 | 5 | 0.00202 | 0.01596 | +0.00296 | agrees |
| `mc_2087` | 1 | 5 | 5 | 0.00504 | 0.01304 | +0.00261 | agrees |
| `mc_2085` | 2 | 2 | 2 | 0.00655 | 0.01449 | +0.00252 | agrees |
| `mc_2041` | 2 | 3 | 3 | 0.00717 | 0.01044 | +0.00246 | agrees |
| `mc_2029` | 1 | 4 | 4 | 0.00427 | 0.01528 | +0.00204 | agrees |
| `mc_2008` | 1 | 5 | 5 | 0.00072 | 0.01805 | +0.00190 | agrees |
| `mc_2034` | 2 | 5 | 5 | 0.00614 | 0.01339 | +0.00154 | agrees |
| `mc_2031` | 1 | 3 | 3 | 0.00743 | 0.01125 | +0.00152 | agrees |
| `mc_2043` | 2 | 3 | 3 | 0.00776 | 0.01181 | +0.00140 | agrees |
| `mc_2047` | 2 | 3 | 3 | 0.00984 | 0.00972 | +0.00109 | agrees |
| `mc_2089` | 2 | 4 | 4 | 0.00658 | 0.01327 | +0.00109 | agrees |
| `mc_2061` | 2 | 4 | 4 | 0.00753 | 0.01344 | +0.00084 | agrees |
| `mc_2056` | 2 | 4 | 4 | 0.00912 | 0.01129 | +0.00069 | agrees |
| `mc_2100` | 1 | 5 | 5 | 0.00695 | 0.01376 | +0.00065 | agrees |
| `mc_2073` | 1 | 4 | 4 | 0.00471 | 0.01556 | +0.00044 | agrees |
| `mc_2013` | 1 | 5 | 5 | 0.00148 | 0.01895 | +0.00043 | agrees |
| `mc_2002` | 2 | 5 | 5 | 0.00702 | 0.01355 | +0.00042 | agrees |
| `mc_2015` | 1 | 5 | 5 | 0.00604 | 0.01470 | +0.00040 | agrees |
| `mc_2021` | 2 | 5 | 5 | 0.00517 | 0.01609 | +0.00027 | agrees |
| `mc_2077` | 2 | 4 | 4 | 0.00511 | 0.01655 | +0.00025 | agrees |
| `mc_2030` | 1 | 5 | 5 | 0.00521 | 0.01550 | +0.00020 | agrees |

Every port is in `cumulative_ports.csv`.
