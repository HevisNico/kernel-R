# Network of R cells: the registered campaign

**Status: frozen, not launched.** [`PREDICTION.md`](PREDICTION.md) was
pushed alone (commit `576bb03`, 2026-11-14 17:06:25 UTC), before any file
of this folder existed. The implementation below awaits an independent
review. No instance of the campaign has been simulated.

The campaign asks whether, on six cells with mismatch that no one has looked
at, the learned state of a two-cell network is the one computed beforehand
from measures made on each cell alone. The primary claim is deterministic,
on runs without noise. Read `PREDICTION.md` first.

| File | What it is |
|---|---|
| [`PREDICTION.md`](PREDICTION.md) | the preregistration; never edited |
| [`plan.py`](plan.py) | the measure runs, the network runs, and the two manifests of the launch kit |
| [`run.py`](run.py) | one run, as the launch kit starts it: a scan, a train, or a network run |
| [`predicted.py`](predicted.py) | from the collected measures to `PREDICTED.json`, and `Predicted.lean` for the Lean kernel |
| [`check.sh`](check.sh) | compiles the model, the lemma on the order of the dates and `Predicted.lean` |
| [`analyze.py`](analyze.py) | the one analysis: `RESULTS.json` and `REPORT.md` |
| [`rehearsal.py`](rehearsal.py), [`REHEARSAL.json`](REHEARSAL.json) | the whole chain on the nominal cell, which is not an instance |
| [`test_campaign.py`](test_campaign.py) | checks without a simulator; run by `.github/workflows/network-circuit-campaign.yml` |

The simulation itself is that of [`../network-circuit`](../network-circuit/README.md)
and its [`phase1`](../network-circuit/phase1/README.md), frozen by hash in
the manifests with the circuit, the junction areas and the launcher.

## How the campaign runs

The launcher is the second launch kit,
[`../sky130-supervisor-closure/launchkit`](../sky130-supervisor-closure/launchkit/README.md),
unchanged. It is used twice, with two protocols, so each machine is claimed
once per stage:

| Stage | Protocol of the launcher | Manifest | Marker | Runs per machine |
|---|---|---|---|---|
| measures | `PREDICTION.md` | `CAMPAIGN_M.json` | `RUN_ATTEMPT_M.json` | 12 scans, 3 trains without noise, 9 noisy trains |
| network runs | `PREDICTED.json` | `CAMPAIGN_R.json` | `RUN_ATTEMPT_R.json` | 3 without noise, the control on one machine, 6 noisy |

Between the two, the prediction step: `predicted.py` reads the collected
measures of both machines and writes `MEASURES.json`, `CONSTANTS.json`,
`PREDICTED.json` and `Predicted.lean`. These are committed and pushed. The
launcher of the network runs is bound to the SHA-256 of `PREDICTED.json` and
refuses to start if that file is not published or has changed: the
predictions exist in Git before any network run.

With `PY` the pinned interpreter, `KIT` the launcher, on the campaign
branch, after the review:

```sh
"$PY" -B "$KIT" inventory --machine a --out research/network-circuit-campaign/INVENTORY_a.json --ngspice "$NGSPICE" --pdk "$PDK"
```

One inventory per machine, each on its own machine, both committed. Then:

```sh
"$PY" -B research/network-circuit-campaign/plan.py manifest measures "$PROTOCOL_COMMIT" "$SOURCE_COMMIT" > research/network-circuit-campaign/CAMPAIGN_M.json
```

```sh
"$PY" -B "$KIT" prepare --repo "$PWD" --manifest research/network-circuit-campaign/CAMPAIGN_M.json --ngspice "$NGSPICE" --pdk "$PDK"
```

The marker is committed and pushed, then one launch per machine:

```sh
"$PY" -B "$KIT" run-machine --repo "$PWD" --manifest research/network-circuit-campaign/CAMPAIGN_M.json --ngspice "$NGSPICE" --pdk "$PDK" --branch "$BRANCH" --machine a --out "$PWD/../measures-a"
```

```sh
"$PY" -B "$KIT" collect --out "$PWD/../measures-a" --destination "$PWD/../collected-measures-a"
```

When both machines have pushed their collected measures:

```sh
"$PY" -B research/network-circuit-campaign/predicted.py research/network-circuit-campaign research/network-circuit-campaign/evidence/measures-a research/network-circuit-campaign/evidence/measures-b
```

```sh
bash research/network-circuit-campaign/check.sh
```

`PREDICTED.json` is committed with the measures (the protocol commit of the
second stage), `Predicted.lean` in the next commit (its source commit, whose
CI runs the Lean check). Then the same three commands with `runs`,
`CAMPAIGN_R.json` and `PREDICTED.json` as protocol, and at the end, once:

```sh
"$PY" -B research/network-circuit-campaign/analyze.py research/network-circuit-campaign research/network-circuit-campaign/PREDICTED.json research/network-circuit-campaign/CONSTANTS.json --measures "$MEASURES_A" "$MEASURES_B" --runs "$RUNS_A" "$RUNS_B"
```

## Budget

Four runs at a time per machine. By the formula of the launcher (sum of
limit + 10 s, divided by four, plus the largest): 3 995 s per machine for
the measures, at most 3 045 s for the network runs; 13 862.5 s for the two
machines and the two stages, under the 14 400 s allowed. The manifests carry
7 990 s and 6 410 s as their own budgets, which add up to 14 400 s.

## What the implementation adds to `PREDICTION.md`

Nothing is decided here that the preregistration left open, except how its
words are computed:

- **D2, "no stored voltage moves by more than 0.01 mV during a pulse of
  another port or of a FIRE"**, is checked port by port over the whole run:
  between two pulses of a port (which is when the pulses of the other ports
  happen) and across each of its own FIRE pulses, its stored voltage moves
  by at most 0.01 mV; across each of its own `s` pulses, by its measured
  dose within 0.01 mV.
- **"Its own record says that it reached its last date"**: `run.py` writes
  `record.json` with that flag, from the last time point of the waveform.
- **A measure run that is complete but whose record says otherwise** does
  not count.
- **If a machine has no measured instance**, the launcher cannot start the
  network runs at all (it needs both shards). The campaign then ends with
  the primary claim not established.
- `predicted.py` and the two phase-1 scripts it calls were given what the
  campaign needs without changing what they computed before: a function per
  instance in `constants.py`, the allowance for the simulator in
  `predict.py`. The committed results of phase 1 are regenerated unchanged
  by the tests.

## Rehearsal

`REHEARSAL.json`, written by `rehearsal.py`: the whole chain on the nominal
cell (no mismatch), through the real launcher in its synthetic kind with a
local Git remote. It is not a registered run and the nominal cell is not an
instance. See the section "Rehearsal results" below.

## Tests

```sh
"$PY" -B -m unittest research/network-circuit-campaign/test_campaign.py
```

```sh
"$PY" -B research/network-circuit-campaign/rehearsal.py --ngspice "$NGSPICE" --pdk "$PDK" --work /a/new/empty/folder --report /a/new/report.json
```
