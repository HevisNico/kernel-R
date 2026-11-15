# Ring campaign 3: log

What happened, in order. Times are UTC, 2026-11-15. The results are in [`REPORT.md`](REPORT.md) and
[`RESULTS.json`](RESULTS.json), as generated.

## Before any run

| Time | Commit | What |
|---|---|---|
| 09:33 to 11:33 | `d758fdb`, `e1e4a60`, `e69fab5`, `b74dae2` | commitment, amendment 1 (budget), diagnosis of campaign 2, amendment 2 (write') |
| 11:34:31 | `6aa0f40` | `PREDICTION.md`, alone (SHA-256 `e3e3d83921d2cac5e9774c8b88d95957e5ea0bfeb61a69c836af4830fcb56fb6`) |
| 11:58:26 | `d2c3a2e` | implementation, not frozen; the rehearsal of the robust scan (`ROBUST_SCAN_REHEARSAL.json`) |
| 11:58:52 | `3dffb63` | `AMENDMENT_3.md`, alone: the scan limit 860 s, from the rehearsal only |
| 11:59:59, 12:58:05 | `7aec66d`, `1a1c588` | frozen implementation; `REHEARSAL.json`, the whole chain on the nominal cell through the kit |
| | | independent review at `1a1c588`: go, on the condition that every workflow be green on the source commit; draft pull request #167 opened (stacked on #166, then retargeted to `main`) |
| 13:06, 13:08, 13:09 | `af0a6e9`, `57f9295`, `97783df` | inventories of machines a and b; manifest of the measures (protocol `6aa0f40`, source `1a1c588`) |
| 14:07:35 | `7230a06` | `RUN_ATTEMPT_M.json`: the six workflows of `1a1c588` successful |

The remote of the checkout of machine a had again come back as `HevisNico/kernel-r` after a restart of its
container; it was set to `https://github.com/HevisNico/kernel-R` before `prepare`, so no launch was refused.

## Measures

| Machine | Claim | Launch | Runs | Restart during the shard |
|---|---|---|---|---|
| a | `b64d051` | 14:07:38 | 30 of 30 complete, the last ended 15:09:34 | none |
| b | `47a801d` | 14:08:51 | 30 of 30 complete, the last ended 15:01:43 | none |

The container of machine b had restarted while idle before the launch; nothing was running, no resume applies.
Robust scans 307 to 526 s (limit 860), trains up to 625 s (730). No scan was contradictory; no round of repeats
ran. Waveforms in `HevisNico/kernel-R-circuit`: `network-campaign-3/measures-a` (`a2674e6`),
`network-campaign-3/measures-b` (`281aaca`), every file checked again in the pushed branch; every other file here
under [`evidence/`](evidence) (`f9355ba`, `1bd6c92`).

**Disk.** After the measures, the disk allowance of machine a was full while archiving `measures-a`. With the
owner's approval, three folders that were only copies of public branches (the clone and the pushing repository of
`evidence/network-circuit-ring-campaign-2-waveforms`, and a clone of `evidence/network-circuit-campaign-1-waveforms`)
were deleted, after checking that their heads were those of the branches on GitHub and every file against the
SHA-256 of their `SURVIVORS.json` and `PARTS.json`: 66, 66 and 132 files, all identical. No original evidence
folder was touched; no run was running. The first archive of `measures-a` had pushed its branch before the disk
filled; it was checked again in a fresh clone (276 files).

## Predictions

| Time | Commit | What |
|---|---|---|
| 15:26:29 | `35eeae7` | `PREDICTED.json` (SHA-256 `31bb3782c6f45ce5269c57a6ca5443c1dcf77fa8a4bf712bdce38c0de3559330`) and `MEASURES.json` |
| 15:27:21 | `302e5e3` | `Predicted.lean`, checked by `check.sh`: the source commit of the network runs |
| 15:27:47 | `1cf47eb` | manifest of the network runs (23 runs, kit bound 12 223 s) |
| 16:25:01 | `9163cd4` | `RUN_ATTEMPT_R.json`: the six workflows of `302e5e3` successful |

Measured: 11 of 12. **7402 is not measured**: its train without noise reads `sssFsFFFFF` on port `b1` (a FIRE, then
a silent read), and `constants.port` requires the train to be silent reads then FIRE. Eligible: 7401, 7403, 7404,
7405, 7410, 7411, 7412. Not eligible: 7406 (`b1`), 7407 (`a1`), 7408 (`a1`), 7409 (`a2`). Control instance: 7411.

## Network runs

| Machine | Claim | Launch | Runs | Restart during the shard |
|---|---|---|---|---|
| a | `49c3a2a` | 16:25:04 | 10 of 10 complete, the last ended 17:20:25 | none |
| b | `5b64b1a` | 16:25:57 | 13 of 13 complete, the last ended 17:38:28 | none |

The container of machine b had restarted while idle before the launch; no resume applies. Runs 871 to 1 280 s; no
run reached its limit. Waveforms in `HevisNico/kernel-R-circuit`: `network-campaign-3/runs-a` (`8f4a56b`) and
`network-campaign-3/runs-b` (`5f5edbe`), with the waveforms above 100 MiB as parts of 90 000 000 bytes; every
other file here under [`evidence/`](evidence) (`905ed9b`, `cf05970`). For the analysis, the folder of machine b
was rebuilt on machine a from its archive, every file checked against its `SURVIVORS.json`.

No word of a network run was read before the analysis: while the shards ran, only the status strings of the
launcher's state files were looked at.

## Analysis

Run once, at 17:44:51, on machine a, on the evidence of the two machines.

| | Verdict |
|---|---|
| `PREDICTED.json` is that of the measures | yes |
| Primary claim, P1 and P2, on the 7 eligible instances | holds |
| H, P4 | hold |
| N-own, 21 port-runs | holds |
| N-word, 11 port-runs | holds |
| N-own', 21 port-runs; N-word', 11 port-runs (campaign 3 only) | hold |
| C, on 7411 | holds: `a2` read `ssssF...` against `sssssF...` |

The generated files are committed as generated. Across campaigns 2 and 3, by the pooled rule of the commitment,
N-own stays refuted for the series (it failed in campaign 2).

Compute used, by the first launch and the last end of each shard: measures 62 and 53 minutes, network runs 55 and
73 minutes; 243 minutes for the two machines and the two stages.
