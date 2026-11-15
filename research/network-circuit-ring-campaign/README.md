# Periodic ring of R cells at transistor level: campaign 2

**Status: preregistered, implemented, rehearsed on the nominal cell; waiting for the independent review.** No
attempt marker exists and no run of the campaign has started. Nothing has been simulated with the seeds 7301 to
7306.

The rules are in [`PREDICTION.md`](PREDICTION.md), pushed alone at `7ae9710` before any file of the
implementation (SHA-256 `cc16b94e6aa4eca8f065724db3d7a32a3640c90e4eaaf4c73fe250e9ea6208e7`). The design, the Lean
instance for every N and the cost are phase 0, in [`../network-circuit-ring`](../network-circuit-ring/README.md).

| File | What it is |
|---|---|
| [`PREDICTION.md`](PREDICTION.md) | the predictions and the rules, frozen |
| [`plan.py`](plan.py) | the runs of each stage and machine, their limits from the cost model, the two manifests of the launch kit |
| [`run.py`](run.py) | one run as the launch kit starts it: a scan, the train, a run of the ring or of the control |
| [`predicted.py`](predicted.py) | from the collected measures to `MEASURES.json`, `PREDICTED.json` and `Predicted.lean` |
| [`check.sh`](check.sh) | compiles the ring with the pinned Lean and checks `Predicted.lean` |
| [`analyze.py`](analyze.py) | the one analysis: `RESULTS.json` and `REPORT.md` |
| [`rehearsal.py`](rehearsal.py), [`REHEARSAL.json`](REHEARSAL.json) | the whole chain on the nominal cell through the launch kit (synthetic kind, local Git remote), and its record |
| [`test_campaign.py`](test_campaign.py) | checks without a simulator; run by `.github/workflows/network-circuit-ring-campaign.yml` |

The bench (`../network-circuit/net.py`, `router.py`, `measure.py`, `phase1/cellscan.py`, `phase1/collect.py`,
`phase1/constants.py`), the ring (`../network-circuit-ring/ring.py`, `RingNetwork.lean`) and the launch kit
(`../sky130-supervisor-closure/launchkit/launch.py`) are used without any change. Every file the runs or the
analysis read is frozen by hash in the manifests (`plan.FROZEN`).

## Order

1. Inventories of the two machines; manifest of the measures (`plan.py manifest measures`); green CI on its source
   commit; attempt marker (`launch.py prepare`); one launch per machine (`launch.py run-machine`); collection.
2. `predicted.py` on the collected measures: `MEASURES.json` and `PREDICTED.json` in one commit, `Predicted.lean`
   in the next, checked by `check.sh`. That commit is the source commit of the network runs. If the Lean check
   fails, no network run is launched.
3. Manifest of the network runs (`plan.py manifest runs`), bound to `PREDICTED.json`; green CI; marker; one launch
   per machine; collection.
4. `analyze.py`, once, on the evidence of both machines.

Waveforms go to the private repository `HevisNico/kernel-R-circuit` during the campaign; a waveform above 100 MiB
is stored as parts of 90 000 000 bytes with the SHA-256 of every part and of the whole file. After the analysis
they are published on an evidence branch of this repository with no shared history.

## Rehearsal on the nominal cell

[`REHEARSAL.json`](REHEARSAL.json): the whole chain on the frozen files of `bc64cc8`, through the launch kit in
its synthetic kind with a local Git remote, on the **nominal cell** (model section `tt`, no mismatch, no seed), which
is not an instance. Five measure runs, the prediction step, `Predicted.lean` checked by the kernel, five network
runs, the analysis. A second launch of each machine at each stage was refused.

| | Result |
|---|---|
| needs | 4, 4, 4, 4; laps 26 without noise, 19 for the noisy runs; own room under both budgets on the four ports |
| P1, P2 | the four zero-error words; freeze at lap 16; first pulses at laps 1, 5, 9, 13 |
| H, P4 | hold; largest move that is not a dose 0.0001 mV; closest pulses on a cell 17.20 units |
| N-own, N-word | hold on 12 port-runs each (three shortened noisy runs) |
| C | **fails**, as `PREDICTION.md` states in advance for the nominal cell: the control gave the four zero-error words |
| M5 | run offsets 0.072 mV rms, scatter within a run 0.067 mV rms (fixed constants: 0.090 and 0.064) |
| M6 | in the three noisy runs, an `s` departs from the measured dose by up to 0.022 mV, above the 0.01 mV of H: the noise of the doses (0.009 mV per dose). H is not reported on noisy runs as a hypothesis, only in M6 |
| wall time | scans 273 to 284 s (limit 410), train 451 s (730), run without noise 978 s (1 530), control 917 s (1 390), noisy runs 927 to 965 s (1 410); at most three runs at a time |
| waveforms | 101 MB without noise, 83 MB for the control, 115 MB for a shortened noisy run: the noisy ones are above 100 MiB and are split for the archive |

## For the independent review

Points where the implementation reads `PREDICTION.md` and a reviewer may read it otherwise:

1. **Limits of the network runs** come from the cost model, per run, at the laps and zero-error pulses of its
   instance (`plan.network_run`), not from fixed values; the 19 200 s are those of five doses per port.
2. **The budget rule**: if the network runs exceed 14 400 s for the two machines, the last noisy runs of the
   machine with the larger bound are removed until they fit (`plan.network_runs`); never a run without noise or
   the control.
3. **The claim under noise covers every measured instance**, eligible or not: it is per port.
4. **C** holds only when the word of `a2` is letters `s`, fewer than its need, then an `F`; any other letter before
   the first `F` makes it fail.
5. **H** "every pulse is delivered" counts a refused pulse as not delivered; "between two pulses of a port" is
   between consecutive pulses only, the start and the end of the run being bound by P4.
6. **Reading rule**: if `PREDICTED.json` is not what `predicted.py` gives from the measures, H and P4 are also
   reported "not established", with the claims.

## Reproduce

```sh
"$PY" -B -m unittest research/network-circuit-ring-campaign/test_campaign.py
```

```sh
bash research/network-circuit-ring-campaign/check.sh
```

```sh
"$PY" -B research/network-circuit-ring-campaign/rehearsal.py --ngspice "$NGSPICE" --pdk "$PDK" --work /a/new/folder --report REHEARSAL.json
```
