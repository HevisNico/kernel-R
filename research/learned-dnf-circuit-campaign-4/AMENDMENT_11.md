# Campaign 4, amendment 11: stage M, its collection, and the end of campaign 4

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 10 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`, `424f6f9`, `53d50f3`, `d380da6`, `184b595`,
`c8adeb4`), after stage M's runs and before its evidence is committed. It is the owner's decision. Nothing else in
`PREDICTION.md` or amendments 1 to 10 changes.

## 1. Stage M (2026-11-17, UTC)

Stage M ran through the launch kit, once per machine, on its protocol `STAGE_M.md` (commit `2822d5f`, SHA-256
`05c8416189d0ef18c83e65e8b77b44c573800470ce1b740c8277b3c3e3bfa7b1`), its runs `STAGE_M_RUNS.json` (commit
`5fab8a4`), its manifest `CAMPAIGN_M.json` (commit `bbaca11`, SHA-256
`0a33f5fd4996febb215127e1e8c86cda4bf0118781ca0356b0c9264c0a6f83d5`) and its attempt marker `RUN_ATTEMPT_M.json`
(commit `479acbd`, SHA-256 `4c24b4468f3508f539e24c4cd0f88bba035c323e5be0d30d1e9d07c9f395e05f`): the 24 calibration
decks of the 12 instances, each limited to 660 s by amendment 10's rule.

- **Machine `a`**: launched at 14:41:50, its claim at commit `d44ba21`; `uptime -s` read `2026-11-17 12:25:44` at the
  start and at the end (15:14:16), as in its inventory.
- **Machine `b`**: its inventory records the boot 14:11:18. The machine restarted while idle, before its launch; its
  boot at launch was 14:36:37 (`INVENTORY_AT_LAUNCH.json`), and nothing had run on it. After checking that only the
  boot had changed (CPU model, processors, memory, kernel, system and the pinned environment equal to its inventory),
  and setting its remote to `https://github.com/HevisNico/kernel-R`, it was launched on the published marker, by the
  owner's decision, at 14:54:45, its claim at commit `43265efc`; `uptime -s` read `2026-11-17 14:36:37` at the start
  and at the end (15:26:43).

Each run's status and wall time, as the kit's `STATE.json` records them ("limit": `time-limit-never-rerun`):

| Seed | Machine | `cal-on` | `cal-off` |
|---|---|---|---|
| 7501 | a | limit, 660 s | complete, 578 s |
| 7502 | a | limit, 660 s | complete, 576 s |
| 7503 | a | limit, 660 s | complete, 568 s |
| 7504 | a | limit, 660 s | complete, 574 s |
| 7505 | a | limit, 660 s | complete, 568 s |
| 7506 | a | limit, 660 s | complete, 595 s |
| 7507 | b | limit, 660 s | complete, 590 s |
| 7508 | b | limit, 660 s | complete, 577 s |
| 7509 | b | limit, 660 s | complete, 551 s |
| 7510 | b | limit, 660 s | complete, 563 s |
| 7511 | b | limit, 660 s | limit, 660 s |
| 7512 | b | limit, 660 s | complete, 572 s |

Eleven runs completed; the thirteen others reached their time limit and are missing, never rerun.

## 2. The collection

The kit's `collect` refused machine `a`'s evidence ("Evidence symlink cannot be silently copied or omitted"): each
run stopped at its limit left a symbolic link `evidence/pdk -> /home/user/campaign/pdk` in its folder (6 on `a`, 7 on
`b`). The refusal left a partial copy of 17 of the 90 files of `a`, which stays as it is and is not used. On `b`, the
kit's `collect` was not run.

The evidence is collected instead by `collect_with_links.py` (SHA-256
`e3b13277ff04bb0d0eb42321efb143e38d6e874de3eb99c0b81b7a2d1cbdcab2`, reviewed as a draft at commit `d073110` on
`research/learned-dnf-circuit-campaign-4-wip`), run once on each machine's evidence folder into a new destination.
It copies every regular file byte for byte with its SHA-256, records each link as text (its path and target) without
following it, writes `COLLECTED.json` in place of the kit's `SURVIVORS.json`, with its own SHA-256, and leaves the
evidence folder unchanged, which it checks before and after. The script is stored with the evidence it produces,
under `evidence/`; the waveforms of 10 MB and more are on an evidence branch.

## 3. The consequence

By `PREDICTION.md` (Definitions, Measures, each cell alone in its slot), an instance is measured only when both its
calibration runs count; otherwise it is not measured, has no prediction, gets no network run and enters no claim.
Every `cal-on` deck is missing, so **no instance of campaign 4 is measured**. There is therefore no `PREDICTED.json`,
no kernel gate on a prediction, and no stage Q, N1, N2 or N3. Nothing is relaunched; seeds 7501 to 7512 are spent.
This file interprets no cause.

## 4. What was known when this was decided

It was decided after stage M's runs, from the statuses and wall times of `STATE.json` only. No output of any run was
read, and no prediction was computed.
