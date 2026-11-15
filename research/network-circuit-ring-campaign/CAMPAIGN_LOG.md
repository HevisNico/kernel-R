# Ring campaign 2: log

What happened, in order. Times are UTC, 2026-11-15. The results are in [`REPORT.md`](REPORT.md) and
[`RESULTS.json`](RESULTS.json), as generated.

## Before any run

| Time | Commit | What |
|---|---|---|
| 01:30:46 | `7ae9710` | `PREDICTION.md`, alone (SHA-256 `cc16b94e6aa4eca8f065724db3d7a32a3640c90e4eaaf4c73fe250e9ea6208e7`) |
| | `d72b43c`, `bc64cc8`, `291f6da` | frozen implementation; rehearsal on the nominal cell through the launch kit (`REHEARSAL.json`) |
| | | independent review of pull request 166 at `291f6da`: go |
| 07:19 | `bc9922a`, `237c89d` | inventories of machines a and b |
| | `ba1f269` | manifest of the measures (protocol `7ae9710`, source `291f6da`) |
| 08:21:17 | `6f97f78` | `RUN_ATTEMPT_M.json`: the five workflows of `291f6da` successful |

Machine b is a new session created for this campaign; its pins were checked against those of machine a and match.

## Measures

| Machine | Claim | Launch | Runs | Restart during the shard |
|---|---|---|---|---|
| a | `fb3de0e` | 08:22:36 | 14 of 15 complete, the last ended 08:49:49; `a-7302-scan-a1` reached its limit (410 s) | none |
| b | `853d78e` | 08:22:19 | 15 of 15 complete, the last ended 08:44:10 | none |

- **A first launch of machine a was refused at 08:21:31, before any claim**: the remote of its checkout was spelled
  `HevisNico/kernel-r`, and the kit accepts only `HevisNico/kernel-R`. The kit checks the published marker before
  it claims (`launch.py`, lines 493 and 495); no claim ref and no evidence folder existed. The remote was set to
  `https://github.com/HevisNico/kernel-R` and machine a was launched once.
- **The collect of measures-a was refused** because the run stopped at its limit had left its `evidence/pdk`
  symbolic link to the PDK (`run.py` removes it only when a run ends). That link alone was removed, its path and
  target noted; the partial copy of the refused collect was kept, not deleted, and the collect was run again.
- Scans 233 to 389 s (limit 410), trains 449 to 537 s (730).
- Waveforms in `HevisNico/kernel-R-circuit`: `network-campaign-2/measures-a` (`4dd0826`),
  `network-campaign-2/measures-b` (`92df8f5`); every file checked against `SURVIVORS.json` again in the pushed
  branch. Every other file here under [`evidence/`](evidence) (`cf04c75`, `0d7f39f`).

## Predictions

| Time | Commit | What |
|---|---|---|
| 08:58:40 | `7aa9411` | `PREDICTED.json` (SHA-256 `223f0c6d996fd56854387874ee30299ee717058d08b0d6cd1300678c8a7ab4d8`) and `MEASURES.json` |
| | `b7f0e6a` | `Predicted.lean`, checked by `check.sh`: the source commit of the network runs |
| | `7ca4e9d` | manifest of the network runs |

Measured: 7301, 7303, 7304, 7306. **7302 is not measured**: its scan of `a1` reached its time limit. **7305 is not
measured**: `constants.port` gives no slope for its port `a1`, whose isolated reads fired at one stored state
only. Eligible: 7304, 7306. Not eligible: 7301 (`a1`), 7303 (`c1`). Control instance: 7306.

## Before the network runs, on other branches

Pushed alone, each before the attempt marker of the network runs, and resting on the measures only:

| Time | Branch | Commit | What |
|---|---|---|---|
| 09:19:39 | `research/network-circuit-ring-lessons` | `453966e` | `LESSONS_FROM_THE_MEASURES.md` |
| 09:28:24 | `research/network-circuit-ring-lessons` | `49c5d96` | `CAMPAIGN_3_DECISIONS.md` |
| 09:33:13 | `research/network-circuit-ring-campaign-3-commitment` | `d758fdb` | campaign 3 `COMMITMENT.md` |
| 09:35:50 | `research/network-circuit-ring-campaign-3-commitment` | `e1e4a60` | campaign 3 `AMENDMENT_1.md` (budget) |
| 09:46:23 | `research/network-noise-study-commitment` | `0cfe85a` | noise study `COMMITMENT.md` |

## Network runs

| Time | Commit | What |
|---|---|---|
| 10:11:00 | `e700396` | `RUN_ATTEMPT_R.json`: the five workflows of `b7f0e6a` successful |

| Machine | Claim | Launch | Runs | Restart during the shard |
|---|---|---|---|---|
| a | `19c21a4` | 10:11:16 | 8 of 8 complete, the last ended 10:49:35 | none |
| b | `3fc95ec` | 10:12:19 | 9 of 9 complete, the last ended 11:00:26 | none |

The container of machine b had restarted while idle before the launch (boot 10:11:23); nothing was running, and
no resume applies. Its pins were checked again before the launch.

No word of a network run was read before the analysis: while the shards ran, only the status strings of the
launcher's state files were looked at.

Runs without noise 1 029 to 1 234 s, control 933 s, noisy runs 943 to 1 194 s; no run reached its limit.

Collected evidence in `HevisNico/kernel-R-circuit`: `network-campaign-2/runs-a` (`5277d54`),
`network-campaign-2/runs-b` (`515c126`), with the seven waveforms above 100 MiB of each shard stored as parts of
90 000 000 bytes (`PARTS.json`); every file checked again in the pushed branch. Every other file here under
[`evidence/`](evidence) (`bcf09e2`, `1865595`). For the analysis, the folder of machine b was rebuilt on machine a
from its archive, every file and every joined waveform checked against its `SURVIVORS.json`.

## Analysis

Run once, at 11:06:40, on machine a, on the evidence of the two machines (`analyze.py`, with the measures of
`evidence/measures-a`, `evidence/measures-b` and the collected network runs of both machines).

| | Verdict |
|---|---|
| `PREDICTED.json` is that of the measures | yes |
| Primary claim, P1 and P2, on 7304 and 7306 | holds |
| H, P4 | hold |
| N-own, 18 port-runs | **fails**: one port-run, `c1` of 7301 in `a-7301-ring-noisy1`, reads `ssss?FFFFFF` |
| N-word, 6 port-runs | holds |
| C, on 7306 | fails, as stated in advance for the nominal cell |

The generated files are committed as generated.

Compute used, by the first launch and the last end of each shard: measures 27 and 22 minutes, network runs 38 and
48 minutes; 135 minutes for the two machines and the two stages.
