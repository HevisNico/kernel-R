# The final dry run of the complete chain (item 4, 2026-11-26). Development only; nothing pushed; no fix applied

## Setup
- **Code.** Two fresh clones, A and B, of research/layered-campaign-int at the local commit 766c656c:
  - `git clone --depth 1 --single-branch` from the local repository;
  - in each, worktrees at the kit commit d599300d and the noise commit 458bc7a6, fetched by sha;
  - the PDK linked;
  - no file of the session's working trees was used.
- **Template and plans.**
  - The template is TEMPLATE_CAMPAIGN_2.json (c1219a54…), used through a rehearsal copy that differs in
    seal_push.remote alone. That remote is a local bare repository with both hooks (pre-receive: no deletion, no
    non-fast-forward; post-receive: push times).
  - The plans are plan_split2.py's own, m = 8, on NOT1 6212, 6213, 6217, 6218, 6219, 6220, XOR3 9803 and ANDOR3 9805
    (dev and yield-lot seeds, excluded from the campaign).
- **Machines,** run one after the other on this 4-core container, each through campaign_run14 launch.
  - **A** = K01 (XOR3 9803, U), K02 (ANDOR3 9805, U), K03 (NOT1 6220, the D4 audit), K07 and K08.
  - **B** = K04 (NOT1 6212, U, and the remote duplicate of XOR3 9803), K05 (NOT1 6213, and the duplicate of NOT1 6212)
    and K06 (NOT1 6217, and the duplicate of ANDOR3 9805).

## Checks (pass unless marked)
- **The template check.** It passed on all 8 plans, with each clone's own worktrees resolved from the commits alone.
  ENV.json's static part is identical on A and B (1 distinct value).
- **The kernel library.** It was built on every root, in 11.9–15.4 s, from the 12 pinned sources.
- **Stage D under the kernel.** On all 8 instances the kernel agrees with the mirror: XOR3 116 theorems, ANDOR3 112,
  NOT1 24 each, with 1.05–1.41 s of Lean per instance. No disagreement.
- **D4.** NOT1 6220 used "this run's solo scans" and the others d4_stage. D4\* = 0.003966 ≤ 0.005, so there is no
  regate.
- **Seals.** All 8 were pushed through the hooks (8 pushes in push_times.log, branches evidence/combined-seals-K01…K08).
  - In analysis, the seal log is ok on all 8 (the push precedes stage N).
  - The regeneration fails on all 8: see **defect D1**.
- **Stage N.** All steps were done on all 8; no job error; nothing was stopped for disk.
  - N0 ran on all 8. N1–N3 ran on XOR3 9803 and NOT1 6220, 6212, 6213 and 6218 (room_K3); ANDOR3 9805, NOT1 6217 and
    6219 have no room.
  - All 23 comparisons agree.
- **U.** It holds on XOR3, ANDOR3 and NOT1 (no R-cell fire), with its record's seal log read from the branch.
- **The remote duplicates.** XOR3 9803 on K04, NOT1 6212 on K05 and ANDOR3 9805 on K06 each fetched the seal folder by
  name (ok). check_duplicate gives **DUPLICATE IDENTICAL** for all three:
  - trace.raw data identical, input.spice and noisy_record identical;
  - the comparison agrees and equals the original's.
  - trace.digest.json differs between the machines (cross_machine_duplicates_v3), as before: its Date line.
- **The trace extract.** It was written in all 23 rounds, and all 23 SHA256SUMS check.
  - XOR3: N0 70 MB in 2 parts; each noisy round 100 MB in 3 parts (25 vectors, 500,137 points). `join` rebuilds an XOR3
    N2 extract that matches its whole sha256.
  - ANDOR3 N0: 43 MB, whole.
  - NOT1: 3.0 MB at N0 and 4.9 MB per noisy round.
  - Total 0.49 GB for these 8 instances.
- **keep_raw.** It keeps N0 only: XOR3_9803 (1.85 GB), ANDOR3_9805 (1.01 GB) and NOT1_6212 (19 MB). Their N1–N3 raws
  were deleted after agreement. The duplicates' raws are kept, as before.
- **Top-level SHA256SUMS.** They check on all 8 roots, and all 8 have DONE.
- **analyze9, twice on the 8 roots.** rc 0 both times, 13 s and 12 s, byte-identical. But see D1: every instance is
  not_sealed at K0, so nothing is counted.

## Defects (none fixed)
- **D1 (blocks the freeze): the analysis cannot verify a stage_d6 seal.**
  - analyze3.regenerate, used by analyze6 to analyze9, picks the stage-D script from the sealed prediction's `code`
    among SCRIPTS = (stage_d5.py, stage_d4.py, stage_d3.py). stage_d6's predictions also name stage_d5.py, so the
    regeneration runs stage_d5. Its prediction lacks `kernel` and differs in `code`.
  - Result: "regenerated prediction differs from the seal in ['code', 'kernel']", so every instance is not_sealed.
    That gives 0 counted at K0 and K3 in all three groups (K3: not_sealed or no_prediction).
  - **A fix needs a new analysis** (analyze10) that regenerates with stage_d6.py and the kernel library (built as
    campaign_run14 does), and a new pin. FREEZE.txt names the analysis, so the freeze waits on it.
- **D2 (procedure): a remote duplicate needs a manual plan edit.** plan_split2 writes `remote_duplicates` without
  `seal_log`. The duplicate machine needs [commit, branch] of the home machine's seal push. Here it was added by hand
  from the home's seal_push.json before launching K04, K05 and K06, as in the earlier dry runs.
  - campaign_run13/14 do not check this entry. Without it, the duplicate is refused at run time.
  - As it stands, a duplicate machine cannot be launched before its home machine has pushed its seal.
- **D3 (sizing, not a code defect): disk.** Free disk went from 29.2 GB at the start to 23.1 GB at its lowest (the end),
  against disk_guard_gb 20.
  - On this container the margin was 3 GB with one XOR3 instance and its N0 raw kept.
  - A machine that holds an XOR3 original with room, plus an ANDOR3 original, needs about 30 GB free at launch.
- Note: the earlier estimates of POSTCHECK_DATA.md were low for XOR3 N0 (70 MB measured against ~47 MB) and ANDOR3 N0
  (43 MB against ~33 MB). Noisy XOR3 rounds matched (100 MB).

## Cost
- **CPU.** 24,995 s over the 8 instances' steps, plus 4,427 s for the three duplicates and 332 s for the three U
  controls: about 8.3 core-h. plan_split2 expected 6.97.
- **Wall.** 6.13 h in total, one machine at a time: K01 9,219 s, K02 4,727 s, K03 751 s, K07 671 s, K08 506 s,
  K04 3,328 s, K05 696 s, K06 2,172 s.
- **Disk at the end.** 7.1 GB for the dry run folder: roots 6.0 GB, mostly the kept N0 raws and the duplicates' raws
  (2 × 1.85 GB XOR3, 2 × 1.01 GB ANDOR3); clones and worktrees 1.1 GB.
