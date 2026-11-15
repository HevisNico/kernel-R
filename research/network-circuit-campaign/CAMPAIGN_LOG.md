# Network campaign: log

What happened, in order. Times are UTC, 2026-11-14. The results are in
[`REPORT.md`](REPORT.md) and [`RESULTS.json`](RESULTS.json), as generated;
the two amendment scripts printed [`N4_OUTPUT.txt`](N4_OUTPUT.txt) and
[`N5_N6_OUTPUT.txt`](N5_N6_OUTPUT.txt).

## Before any run

| Time | Commit | What |
|---|---|---|
| 17:06:25 | `576bb03` | `PREDICTION.md`, alone |
| | `6644fb5`, `af0ab72`, `28af2d0`, `54a9989` | implementation, rehearsal on the nominal cell, merge of `main`; reviewed at `54a9989` |
| 18:49:30 | `de663d4` | `AMENDMENT_1.md`, alone: the source commit of the measures |
| | `29dacdc`, `6a693d8` | manifest of the measures, inventories of the two machines |
| 20:34:31 | `3cb4416` | `AMENDMENT_2.md`, alone, on the branch `research/network-circuit-campaign-amendment-2` (SHA-256 `c7ceef16ce914ee8701b9e57f11f8f8cbdc2fa554bdeb66f1a91e726e7dca40b`) |
| 20:34:48 | `465a82a` | `RUN_ATTEMPT_M.json`: the six workflows of `de663d4` successful |

**CI.** Pull request 149 was merged into `main` at 18:51:08, while this
one was open; from then on GitHub marked this one as conflicting and
started no run for its later commits, although a local merge is clean. The launcher checks
the source commit: `de663d4` had its six pull-request runs. The source
commit of the network stage, `79f84f0`, got the same six workflows by
`workflow_dispatch`. Nothing was pushed to trigger a run.

**Amendment 2** could not be added to this branch before the measures: the
launcher refuses a launch when a file other than the manifest, the marker
and the inventories has changed since the source commit. It was pushed
alone on its own branch before the marker, and added here byte for byte
(`9091ce9`) after the measures and before the predictions.

## Measures

| Machine | Claim | Launch | Last run ended | Runs | Restart during the shard |
|---|---|---|---|---|---|
| a | `05fc140` | 20:35:00 | 21:09:03 | 24 of 24 complete | none |
| b | `62d864b` | 20:36:19 | 21:06:54 | 24 of 24 complete | none |

Scans 143 to 243 s (limit 375), trains without noise 307 to 347 s (700),
noisy trains 394 to 470 s (700). The container of machine b had restarted
while idle before the launch; nothing was running, and no resume applies.

Collected evidence, whole folders with waveforms, in
`HevisNico/kernel-R-circuit`: `network-campaign-1/measures-a` (`38bf109`),
`network-campaign-1/measures-b` (`ddeb822`). Every file except the
waveforms is here under [`evidence/`](evidence), with the `SURVIVORS.json`
of each folder (`657ca52`).

## Predictions

| Time | Commit | What |
|---|---|---|
| | `9091ce9` | `AMENDMENT_2.md` on this branch |
| 21:14 | `ada666c` | `PREDICTED.json` (SHA-256 `bacea3b51dac1759cbc68029bae8ac4537d5438f9fe36138308f95630678de52`) and `MEASURES.json` |
| 21:14 | `79f84f0` | `Predicted.lean`, checked by `check.sh`: the source commit of the network runs |
| | `46ff6a1` | manifest of the network runs |
| 22:26:26 | `0170e2e` | `RUN_ATTEMPT_R.json`: the six workflows of `79f84f0` successful |

Measured: 7201 to 7205. **7206 is not measured**: `constants.py` gives no
threshold for its port `a2`, because among the isolated reads of its scan a
state that fired is not stronger than a state that stayed silent (the scan
trained it with four doses, the train 18 units apart fired after three).
By `PREDICTION.md` it has no prediction and no network run. Eligible:
7201, 7203, 7204, 7205. Not eligible: 7202 (port `b2`, last silence
0.039 mV). Control instance: 7204.

## Network runs

| Machine | Claim | Launch | Last run ended | Runs | Restart during the shard |
|---|---|---|---|---|---|
| a | `ef07f6a` | 22:26:43 | 22:55:13 | 9 of 9 complete | none |
| b | `0311c9a` | 22:27:18 | 22:42:58 | 7 of 7 complete | none |

Runs without noise 401 to 482 s, control 368 s, noisy runs 497 to 646 s
(limit 860). The container of machine b had again restarted while idle
before the launch; no resume applies.

Collected evidence in `HevisNico/kernel-R-circuit`:
`network-campaign-1/runs-a` (`c3c6032`), `network-campaign-1/runs-b`
(`4a30d5a`).

No word of a network run was read before the analysis: while the shards
ran, only the status strings of the launcher's state files were looked at.

## Analysis

Run once, at 22:57:24, on the evidence of the two machines. Then the
script of amendment 1 and the script of amendment 2, once each, as written.

Compute used, both machines and both stages: 109 minutes of the 240
allowed.
