# Periodic ring of R cells at transistor level: campaign 3

**Status: preregistered, implemented, rehearsed on the nominal cell; waiting for the independent review.** No
attempt marker exists and no run of the campaign has started. Nothing has been simulated with the seeds 7401 to
7412.

| File | What it is |
|---|---|
| [`COMMITMENT.md`](COMMITMENT.md), [`AMENDMENT_1.md`](AMENDMENT_1.md), [`AMENDMENT_2.md`](AMENDMENT_2.md) | the commitment, fixed before the network runs of campaign 2, its budget, and write' with N-own' and N-word' |
| [`DIAGNOSIS_N_OWN.md`](DIAGNOSIS_N_OWN.md) | the diagnosis of the N-own failure of campaign 2, behind amendment 2 |
| [`PREDICTION.md`](PREDICTION.md) | the predictions and the rules, pushed alone at `6aa0f40` (SHA-256 `e3e3d83921d2cac5e9774c8b88d95957e5ea0bfeb61a69c836af4830fcb56fb6`) |
| [`AMENDMENT_3.md`](AMENDMENT_3.md), [`ROBUST_SCAN_REHEARSAL.json`](ROBUST_SCAN_REHEARSAL.json) | the scan limit 860 s, from the rehearsal of the robust scan |
| [`robustscan.py`](robustscan.py) | the robust scan: `../network-circuit/phase1/cellscan.py` with only the two changes of `PREDICTION.md`; `cellscan.py` is frozen by hash in campaigns 1 and 2 and is not edited |
| [`plan.py`](plan.py), [`run.py`](run.py) | the runs, their limits, the manifests; one run as the launch kit starts it |
| [`predicted.py`](predicted.py), [`check.sh`](check.sh) | the majority rule, the prediction step, `Predicted.lean` and its check |
| [`analyze.py`](analyze.py) | the one analysis, with N-own' and N-word' (write': at least 1 us above 0.9 V) and M7 |
| [`rehearsal.py`](rehearsal.py), [`REHEARSAL.json`](REHEARSAL.json) | the whole chain on the nominal cell through the launch kit, and its record |
| [`test_campaign.py`](test_campaign.py) | checks without a simulator; run by `.github/workflows/network-circuit-ring-campaign-3.yml` |

Everything else is the bench of `../network-circuit`, the ring of `../network-circuit-ring` and the launch kit,
unchanged; the code is that of campaign 2 with the changes the commitment and its amendments name.

## The robust scan and its limit

On the nominal cell, four at a time: the robust scan takes 19 pulses and 14.06 ms (400 to 420 s), against 15 pulses
and 10.54 ms for the ordinary scan; with one round of repeats forced, 23 pulses and up to 18.46 ms (498 to 516 s).
The two extra reads fired on every port (latencies 0.70 and 0.79 unit), leaving 6 or 7 fired states per port. In
the forced round, the majority rule kept 19 of 23 records and every bracket stayed consistent.

The limit of [`AMENDMENT_3.md`](AMENDMENT_3.md) is **860 s**, the largest the frozen kit accepts for one measures
manifest of twelve instances. The raw worst case (the longest scan of campaign 2 plus both extras, at the slowest
rates seen) is 787 s; the slow machine's fitted model for it, times 1.3, is 833 s. Not covered: 1.3 times the raw
worst case, 1 030 s. Kit budget: 14 400 s for the measures, 14 165 s for the network runs at five doses per port,
28 565 s in all.

## Reproduce

```sh
"$PY" -B -m unittest research/network-circuit-ring-campaign-3/test_campaign.py
```

```sh
bash research/network-circuit-ring-campaign-3/check.sh
```

```sh
"$PY" -B research/network-circuit-ring-campaign-3/robustscan.py /a/new/folder tt none a 1 "$NGSPICE" "$PDK" force
```

```sh
"$PY" -B research/network-circuit-ring-campaign-3/rehearsal.py --ngspice "$NGSPICE" --pdk "$PDK" --work /a/new/folder --report REHEARSAL.json
```
