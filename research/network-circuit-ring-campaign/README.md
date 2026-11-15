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
