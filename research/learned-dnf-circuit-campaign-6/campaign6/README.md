# Campaign 6's implementation: notes and the per-stage procedure

The code of `PREDICTION.md` section 8 (`df1a3cb`) and its amendment 1 (`a0d4ad3`), on
`research/learned-dnf-circuit-campaign-6-impl`. The batch's code (`../batch/`) and campaign 5's
(`../../learned-dnf-circuit-campaign-5/`) are imported unchanged.

## Declared behaviour

- **The batch's record key.** `batch6.cal` is unchanged, so every calibration deck's record keeps its own `batch` key:
  `batch6.run_header`'s development-batch label, with machine `None` for 7801 to 7805. The campaign's header is the
  record's `campaign6` key. `meas6.cal` also sets the record's `stage` to the stage check (`batch6.cal` writes `None`
  there).
- **The noise fingerprint of a scan.** `scan6.main` writes none. `meas6.scan_main` adds `noise.sha256`, campaign 5's
  `run4.trnoise_fingerprint` over the deck's three cells, because the kit requires one of every registered run.
- **The nominal cell and the kit.** `c6.guard_seed` does not require the nominal cell (the measure rehearsal and the
  tests) to run inside the kit. It carries no claim.
- **The machine of a run.** Since amendment 1, an M2 or M3 run may run on the other machine than its instance's. Each
  record's `campaign6.machine` is the machine that ran it, read from the kit's state file, and
  `campaign6.instance_machine` is its instance's assigned machine. Run ids name the instance by its seed alone
  (`7801-scan-a-pair`, or `none-a-...` / `none-b-...` for the two nominal instances of the rehearsal).

- **Amendment 1 in the stage files.** The stage files of M2, M3, RM2 and RM3 name `PREDICTION_AMENDMENT_1.md`
  (`a0d4ad3`, SHA-256 `14a5379e…9554`) as a second governing document, and every runner of those stages checks it,
  both as named and in the repository (`c6.stage_check`).
- **Campaign 5's smoke files.** M8's eligible path (`m8_case.py`, in CI) reads campaign 5's smoke run
  `smoke/nominal-quiet`. Its files besides the waveform are copied byte-identical from `f805c20`
  (`research/learned-dnf-circuit-campaign-5-wip`), and the waveform is fetched by CI from
  `evidence/learned-dnf-circuit-campaign-5-smoke`. The 7 files are in `stages6.frozen()`, so every manifest and the
  marker bind them.
- **CI before this commit.** The 3 earlier campaign-6 CI runs on `-wip` (44376104118, 44376622903, 44381740440) failed
  at M8's step, because these smoke files were missing; every unit test step before it had passed. So `check.sh`, the
  structural comparison and the audit had never run in campaign 6's CI until the commit that added the files. CI also
  never ran on `-impl` before `-impl` was added to the workflow's branches in that same commit.

## The per-stage procedure

For each stage, in the order of `PREDICTION.md` 10:

Each attempt of the stages has an id (`[a-z0-9][a-z0-9-]{0,31}`, e.g. `r3` for the rehearsal's third attempt) and its
own folder `research/learned-dnf-circuit-campaign-6/stages/<attempt>/` (`stages6.attempt_dir`); the id is written in each
of its stage files, so each attempt's claim refs are its own (the audit of 2026-11-19, finding 2). The earlier attempts'
files (the folder's top level, and `stages/STAGE_RM1.md`, `stages/RUNS_RM1.json` of attempt 2) belong to superseded code
and are kept unchanged.

0. **The prediction record**, for RN (`PREDICTED_RN.json`, `predicted6.py --rehearsal OUT BATCH_DIR`) and for Q (after
   M3, `PREDICTED.json`, `predicted6.py OUT STAGE_DIR...`): pushed alone, with its `Gate6_<seed>.lean` and
   `check_<seed>.log` files, in `stages/<attempt>/`, before the stage's stage file. The N stages use Q's record.
1. **The protocol commit.** On `-impl`, a commit adds only the stage file `stages/<attempt>/STAGE_<S>.md` (`stages6.py
   stage-file STAGE OUT ATTEMPT`). It is the launch kit's protocol of the stage (`protocol_path`), so each stage and
   attempt has its own claim ref (`launch.claim_ref` is keyed by the protocol's SHA-256 and the machine alone). It names
   `PREDICTION.md` (and amendment 1 for M2, M3, RM2, RM3) with their SHA-256, and the attempt, which every runner
   checks (safeguard i, `c6.stage_check`).
2. **The source commit**, a later, different commit, adds only:
   - the stage's run list `stages/<attempt>/RUNS_<S>.json` (`stages6.py runs STAGE OUT ATTEMPT [data]`), which the
     manifest must equal;
   - for M2 and M3 (RM2 and RM3), its inputs file `stages/<attempt>/INPUTS_<S>.json`, written by `inputs6.py` from the
     collected evidence of the stages before it.

   The stage's data file (its inputs, or its prediction record) is bound by the manifest (`stages6.data_path`). Not the
   inventories: `INVENTORY_a.json` and `INVENTORY_b.json` are written once, each after its machine's envcheck,
   and reused unchanged by every later stage (the coordinator's ruling of 2026-11-19; the kit compares only the
   published inventory with the local one, and its machine, environment and executor). Each launch's
   `INVENTORY_AT_LAUNCH.json` (and `INVENTORY_AT_RESUME`) records the machine at that stage, and envcheck runs before
   every launch. The manifest (`stages6.manifest`) takes `protocol_commit` as the one commit that adds the stage file,
   and binds the stage file, the run list, the data file and every frozen file by their SHA-256 at the source commit.
   **From the source commit until both machines' shards have ended, nothing is pushed to `-impl`** but the manifest, its
   attempt marker and the inventories: the kit refuses any other change at launch and at resume (`runtime_unchanged`,
   `allowed_after_freeze`). CI must be green on the source commit itself (the kit's live gate).
3. **The manifest**, `stages6.py manifest STAGE OUT SOURCE_COMMIT ATTEMPT [data]`, written OUTSIDE the checkout, is
   checked as the kit checks it (both shards, the round-robin order, the budget); then the marker check
   (`tools/marker_check.py STAGE ATTEMPT MANIFEST MARKER_COMMIT REPO`, outside the frozen set) runs in a clean checkout
   of the source commit, and refuses a manifest inside it. A refusal means no launch. On a pass, the manifest
   `stages/<attempt>/CAMPAIGN_<S>.json` and its attempt marker (`launch.py prepare`, `RUN_ATTEMPT_<S>.json`) are pushed
   together. `MARKER_CHECK_<S>.txt` goes onto the stage's evidence branch of machine a.
4. **The launch**, one per machine, detached, with the sessions active. A started run is never relaunched. Before it, on
   each machine (the audit of 2026-11-19, checked steps; a failed one means that machine does not launch):
   - both sessions are in active loops of at most 5 minutes (`PREDICTION.md` 6);
   - a machine that has restarted (`uptime -s` changed) passes envcheck again first;
   - `tools/diskcheck.py MANIFEST MACHINE OUT_PARENT` passes: free space above the stage's footprint on that machine
     (its runs' largest folder sizes per kind, measured for the measure runs and extrapolated for the network runs, twice
     for the collected copy) plus 500 MB; its report, with the df line,
     the uptime and the free memory, goes with the stage's evidence;
   - the pushed manifest is the one checked: the SHA-256 of `stages/<attempt>/CAMPAIGN_<S>.json` as pushed equals the
     `manifest … sha256` line of `MARKER_CHECK_<S>.txt` (the coordinator's review of the audit, M2);
   - while its shard runs, the machine stays quiet: no dry run, no Lean check, no CI simulation, no cleanup.
5. **The collection**, with campaign 5's `collect.py`, then the evidence branches. Once a machine's evidence branch is
   pushed and verified (every file against `COLLECTED.json`), its run folder is cleared before the next stage; never
   while its shard is unfinished (`resume-machine` needs it). Collected copies needed later (the next stage's inputs, the
   prediction, the analysis) are kept or fetched again from their evidence branches. Before the first stage, the dry-run
   tree and other scratch are removed, after the audit's logs are saved.
6. **The analysis** (`analyze6.py OUT PREDICTED.json --measures-a DIR... --measures-b DIR... --runs-a DIR... --runs-b
   DIR...`) takes the collected stage folders of this attempt only, named one by one; it refuses a run id seen twice or
   outside the record's runs (finding 7). RN's: `analyze6.py --rehearsal OUT PREDICTED_RN.json BATCH_DIR --runs-a ...
   --runs-b ...`.

**`check-noise`** (`launch.py check-noise`) is applied to the evidence of the **N stages only** (and RN's noisy runs),
where noise is drawn, and must report every fingerprint distinct. The runs without noise (decks, scans, the runs
without noise, the untrained run) share their fingerprint by design. That is expected and is not a failure. Campaign
5's code never called `check-noise`, so this is a stated choice of campaign 6, not a precedent.

**Before the campaign's marker.** RN's end-to-end analysis must show `predicted6_is_reproduced` true, and every check
of `PREDICTION.md` 7 must pass. Its verdicts are discarded.
- Its prediction record is `predicted6.predictions` for seeds 7701 and 7706 on the batch's merged evidence (`batch_dir`:
  machine a's `d9e431b` and machine b's `88a34de`, merged as the batch merged them), with its own Lean files.
- `analyze6` then reproduces that record byte for byte.

## REHEARSAL_RULES (fixed before RM1 is launched)

The rehearsal of `PREDICTION.md` 7: RM1, RM2, RM3 on the nominal cell (`none-a` on `a`, `none-b` on `b`), then RN on
7701 (`a`) and 7706 (`b`). These rules were set on 2026-11-19 at the coordinators' request (the previous coordinator's
points), before any rehearsal stage was launched.

**It passes only if all of these hold:**
1. **Every run completes**, in all four stages, with its required outputs collected (campaign 5's `collect.py`).
2. **The 0.75 rule** (`PREDICTION.md` 7, [C5 §11.4]) holds on every run. No run's wall time exceeds 0.75 of its campaign
   limit. That limit is the run's `timeout_s` in its stage's manifest, which is section 4's `10 × ceil(2 × expected / 10)`
   of its expected cost. For example, a noisy run at need 4 is held to 0.75 × 2 800 s = 2 100 s; at other needs its
   expected cost (1 400 s at need 4) is scaled by campaign 5's `plan.dcost` ratio. Measure runs are held to their own
   `timeout_s` the same way.
3. **Section 7's other checks** pass, each recorded with its output:
   - the seed guard's refusals: a campaign seed outside the kit, and a development seed in a campaign stage;
   - the noise-model guard;
   - the collection;
   - the prediction record reproduced byte for byte from the evidence (condition 5).
4. **`check-noise`** on RN's evidence from both machines: the two noisy runs (`7701-n1`, `7706-n1`) have fingerprints
   distinct from each other and from every run without noise; the runs without noise may share theirs, by design
   (rule change R1 of the audit).
5. **RN's end-to-end analysis** (`analyze6.py --rehearsal`) reproduces RN's prediction record byte for byte
   (`predicted6_is_reproduced` true) and every check of section 7 passes. RN's record is `predicted6.py --rehearsal` on the
   batch's merged evidence (7701 and 7706, round 1 only), pushed alone with its gate files before RN's stage file, its
   needs equal to `PREDICTIONS_BATCH.json`'s (rule change R2). The analysis covers RN's runs only (R3). Its verdicts are
   discarded, and none is a claim.
6. Every stage's `marker_check.py` passes before its launch. A refusal means that stage is not launched, and its
   `MARKER_CHECK_<stage>.txt` is committed with the evidence.

**If any condition fails:** no campaign stage (M1 onwards) is launched until an amendment. That amendment may change only
the limits and the stage split, never a rule, a claim or an instance (`PREDICTION.md` 7).

**Observed and reported if they occur** (not testable before the rehearsal; the audit of 2026-11-19): a restart of a
machine during a stage, and its `resume-machine` (each run started before it is lost, never rerun); a run stopped at its
limit, and the links `collect.py` records for it. Each is reported with its runs and times; none is a pass condition by
itself, but a lost run fails condition 1.

**Observed, not fixed** (the coordinator's review of the audit, N1): `stages6.py manifest` (frozen) checks that a data
path is given exactly when the stage takes one, but not, as `stages6.py runs` does, that it resolves to the stage's
`stages/<attempt>/` data file. Contained: the run list at the source commit must equal the runs computed from that path,
and the manifest binds the committed data file by its SHA-256 (`stages6.data_path`), which `marker_check` requires.

**Reported whatever they are:** the wall times of the first noisy runs on a mismatched cell, `7701-n1` (noise seed
77 011, machine `a`) and `7706-n1` (77 061, `b`). Each is reported against section 4's 1 400 s estimate, scaled to its
instance's needs. The two machines' measure records (RM1–RM3) are compared and reported, not required to match.

## Implementation incidents (running list for REPORT.md's table)

One line each: what happened, the fixing commit, and its effect on results. Implementation defects are fixed by reviewed
commits and listed here; `PREDICTION.md` amendments stay reserved for real rule changes (the owner's ruling,
2026-11-19).

| # | What happened | Fixing commit | Effect on results |
|---|---|---|---|
| 1 | Campaign 6's CI never passed before `55e5560`: the 3 runs on `-wip` failed at M8's step (campaign 5's smoke files missing), so `check.sh`, the structural comparison and the audit had never run in campaign 6's CI | `55e5560` (the smoke files added; `-impl` added to the workflow) | None: no run of the campaign or the rehearsal had been made |
| 2 | The kit's claim key is the protocol's SHA-256 and the machine alone; `stages6.manifest` named `PREDICTION.md` as every stage's protocol, so the first rehearsal's RM1 claims refused RM2 ("Machine already claimed") | `1758644` (each stage's kit protocol is its own `stages/STAGE_<S>.md`, as campaign 5 did) | The first rehearsal stopped after RM1; no RM2 run started. That RM1 (evidence `d59245d`, `6e0850c`) ran under the superseded manifest code and counts for nothing; the rehearsal restarts from RM1 |
| 3 | The ancestry check added to `stages6.manifest` in `1758644` (PREDICTION.md's commit before the stage's protocol commit) cannot run in CI's shallow checkout: CI run 44481345779 failed | `6f29fe6` (the check moved to `tools/marker_check.py`, which runs in a full clone) | None |
| 4 | `tools/marker_check.py` names the old layout (top-level `STAGE_<S>.md`, `INPUTS_<S>.json`) and does not check the new protocol fields | `0c061cc` (`marker_check` for marker 2 and the `stages/` layout, reviewed by both coordinators) | None: the script was not used between the first attempt and that commit |
| 5 | README step 3 said the manifest is pushed "with its MARKER_CHECK file"; a file pushed after the source commit other than the manifest, its attempt marker and the inventories makes the kit's launch refuse (`allowed_after_freeze`). Found before any harm: `MARKER_CHECK_<S>.txt` goes onto machine a's evidence branch | `1758644` (README procedure rewritten) | None |
| 6 | Machine b's RM1 evidence branch is an orphan commit with the path `evidence/rehearsal-RM1/b/`, while machine a's is based on the prepared commit with `evidence/rehearsal/RM1/a/` | none (pushed files are never changed); later stages use a's layout | None: all 24 files checked against `COLLECTED.json`; that RM1 counts for nothing anyway (incident 2) |
| 7 | A line of `marker_check.py`'s report reads "the 91 frozen paths and the stage file" where it means 90 frozen paths plus the stage file (91 in all) | `0c061cc` | None: wording only; the check itself compared all 91 paths |
| 8 | While committing `1758644`, the director deleted the working copy of the pushed `CAMPAIGN_RM2.json` with `rm -f`, taking it for an untracked copy | none needed: the deletion was not staged, `1758644` holds only its 3 files, and the copy was restored byte-identical (`187c82fb…`) | None |
| 9 | Planned, before Q: for Q and the N stages `stages6.manifest` (frozen) binds the prediction record only through the run list, so `marker_check` only allows `stages/PREDICTIONS.json` and the gate files | a pre-Q `marker_check` commit (the previous coordinator's version): require `stages/PREDICTIONS.json` and the per-instance `Gate6_*.lean` at the source commit, byte-identical to the prediction record pushed under `PREDICTION.md` 10 at its own commit (an ancestor of the source commit), with both SHA-256s and that commit recorded in `MARKER_CHECK` | None so far: no Q or N stage has been prepared |
| 10 | The audit of 2026-11-19 (before freeze 3; a dry run of every stage through the kit with a fake simulator, and a CI simulation): test_c committed a fixture at a real stage path (CI failing after the first stage file); a stage could never be re-attempted, and attempts shared claim refs; a runner could crash on the kit's STATE.json mid-rewrite (a run lost); RN's record could not be produced (predicted6 crashed on rehearsal seeds) nor reproduced; analyze6 had no RN command line and read whatever folders it walked; marker_check named PREDICTIONS.json; Q/N manifests did not bind the prediction record; manifests or reports inside the checkout, and commits between a source commit and its launch, refused late | frozen commit 3 (findings 1 to 12 of the audit report) and the marker_check commit after marker 3 | None on any result: no rehearsal result that counts exists; attempt 1's RM1 counts for nothing |
| 11 | The coordinator's review of the audit's candidate (2026-11-19): `marker_check` required a gate file for every measured instance, while the frozen `predict6.gate_each` writes one only for a measured instance with an observation (in the batch 7705 and 7709 had none), so Q would have been refused whenever a measured instance has no observation; the dry run's cases had no such instance. Also: gate files not checked unchanged at the source commit; refusal tests dropped in the rewrite; the pushed manifest not checked equal to the checked one | the `marker_check` commit after marker 3 (a gate file exactly for each measured instance with an observation, refusing any other; gate files unchanged at the source commit; the refusal tests restored; README step 4's manifest check) | None: found before marker 3 and before any Q |
| 12 | The supervising session's review of the candidate: analyze6's mapping 5 created the M8 second-test fields `start` and `emissions` when absent, so a malformed record would have given a silent `None` instead of campaign 5's KeyError | freeze 3 (`222cfaf`: each field converted only where present, with a test through campaign 5's real `assumption_on_c`) | None: found before freeze 3; `predicted.rd` always writes both fields |
| 13 | The CI short path, tested on `-wip` only (the owner's go): the first version's decide step passed relative gate-file paths, which campaign 5's `check.sh` resolves after changing directory, so the gate file was never audited (runs 44536895037, 44536954202). The gate-file branch was removed, not repaired, and the simplified workflow was tested green (44541675989 full, 44541744254 short, 44541813625 fallback) | freeze 3 (`7eaf94c`, the workflow byte-identical to the one tested) | None: the defective version was never on `-impl` |
| 14 | The local candidate chain (seven commits with a throwaway author and local-only messages) was not pushed; freeze 3 was rebuilt as two commits with the owner's identity and byte-identical trees | `222cfaf` (tree equal to the reviewed candidate F) and `7eaf94c` (the workflow only) | None |
| 15 | On machine a, after the audit, 11 finished worktrees were removed with `git worktree remove --force` without a prior `git status` check; their commits and branches are intact, and any uncommitted changes in 9 older ones (campaign 5's rehearsal and chain tests, `-wip` drafts, evidence checkouts) were lost unverified | none | None known on any result: the code under test and the evidence are pushed; whatever was uncommitted in those worktrees can no longer be checked |

## Rule changes of the audit (2026-11-19)

Made before any RN result and before any rehearsal result that counts. Attempt 1's RM1 ran, counts for nothing, and
none of R1 to R4 depends on it. No `PREDICTION.md` amendment; no rule, claim, instance or limit of the preregistration
changes (R5).

- **R1. REHEARSAL_RULES condition 4.** Old: "check-noise on RN's evidence from both machines reports every fingerprint
  distinct." New: the two noisy runs distinct from each other and from every run without noise; the runs without noise
  may share theirs. The kit's check-noise on RN's whole evidence exits 2 by design (the dry run), as the runs without
  noise share a fingerprint. The N stages keep "all distinct", over all their evidence together.
- **R2. RN's record.** Old: "predicted6 for 7701 and 7706 on the batch's merged evidence, then analyze6" (which crashed,
  and compared with PREDICTIONS_BATCH.json, a record of another structure). New: RN's record `PREDICTED_RN.json`, written
  by `predicted6.py --rehearsal` (round 1 only), pushed alone with its gate files before RN's stage file, its needs
  equal to the batch's; RN's analysis reproduces it.
- **R3. RN's analysis** covers RN's runs only (the quiet runs, `n1`, the untrained run); no `n2`/`n3` exist in its record.
- **R4. The procedure.** Each attempt of the stages is in its own `stages/<attempt>/` with its id in every stage file;
  manifests and marker-check reports stay outside the checkout; nothing is pushed to `-impl` from a stage's source commit
  until both machines' shards have ended; the analysis takes explicit lists of collected stage folders.
