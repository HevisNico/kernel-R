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

Every stage's files are under `research/learned-dnf-circuit-campaign-6/stages/` (`stages6.STAGES_DIR`). The files at
the folder's top level from the first rehearsal attempt (`STAGE_RM1.md`, `STAGE_RM2.md`, `INPUTS_RM2.json`,
`CAMPAIGN_RM1/RM2.json`, `RUN_ATTEMPT_RM1/RM2.json`) belong to the superseded manifest code and are kept unchanged.

1. **The protocol commit.** On `-impl`, a commit adds only the stage file `stages/STAGE_<S>.md` (`stages6.py
   stage-file`). It is the launch kit's protocol of the stage (`protocol_path`), so each stage has its own claim ref
   (`launch.claim_ref` is keyed by the protocol's SHA-256 and the machine alone), as campaign 5 did with `STAGE_RC.md`.
   It names `PREDICTION.md` (and amendment 1 for M2, M3, RM2, RM3) with their SHA-256, which every runner checks
   (safeguard i, `c6.stage_check`).
2. **The source commit**, a later, different commit, adds only:
   - the stage's run list `stages/RUNS_<S>.json` (`stages6.py runs STAGE OUT [input]`), which the manifest must equal;
   - for M2 and M3 (RM2 and RM3), its inputs file `stages/INPUTS_<S>.json`, written by `inputs6.py` from the collected
     evidence of the stages before it (pushed before the manifest);
   - for Q and the N stages, `PREDICTED.json` and the Lean files of the gate;
   - for RN and M1, RM1, nothing more than the run list (`rehearsal/PREDICTIONS_BATCH.json` is frozen).

   Not the inventories: `INVENTORY_a.json` and `INVENTORY_b.json` are written once, each after its machine's envcheck,
   and reused unchanged by every later stage (the coordinator's ruling of 2026-11-19; the kit compares only the
   published inventory with the local one, and its machine, environment and executor). Each launch's
   `INVENTORY_AT_LAUNCH.json` (and `INVENTORY_AT_RESUME`) records the machine at that stage, and envcheck runs before
   every launch. The manifest (`stages6.manifest`) takes `protocol_commit` as the one commit that adds the stage file,
   and binds the stage file, the run list, the inputs and every frozen file by their SHA-256 at the source commit. After
   the source commit, only the manifest, its attempt marker and the inventories may change (the kit's
   `allowed_after_freeze`), and CI must be green on the source commit itself (the kit's live gate).
3. **The manifest**, `stages6.py manifest STAGE OUT SOURCE_COMMIT [input]`, is checked as the kit checks it (both
   shards, the round-robin order, the budget), then the marker check (`tools/marker_check.py`, outside the frozen set)
   runs in a clean checkout of the source commit, with the manifest kept outside that checkout. A refusal means no
   launch. On a pass, the manifest `stages/CAMPAIGN_<S>.json` and its attempt marker (`launch.py prepare`,
   `stages/RUN_ATTEMPT_<S>.json`) are pushed together, and nothing else is pushed to `-impl` until both machines have
   launched. `MARKER_CHECK_<S>.txt` goes onto the stage's evidence branch of machine a (a file pushed after the source
   commit other than these would make the launch refuse).
4. **The launch**, one per machine, detached, with the sessions active. A started run is never relaunched.
5. **The collection**, with campaign 5's `collect.py`, then the evidence branches.

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
4. **`check-noise`** on RN's evidence from both machines reports every fingerprint distinct.
5. **RN's end-to-end analysis** (`predicted6` for 7701 and 7706 on the batch's merged evidence, then `analyze6`) shows
   `predicted6_is_reproduced` true and every check of section 7 passing. Its verdicts are discarded, and none is a
   claim.
6. Every stage's `marker_check.py` passes before its launch. A refusal means that stage is not launched, and its
   `MARKER_CHECK_<stage>.txt` is committed with the evidence.

**If any condition fails:** no campaign stage (M1 onwards) is launched until an amendment. That amendment may change only
the limits and the stage split, never a rule, a claim or an instance (`PREDICTION.md` 7).

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
| 4 | `tools/marker_check.py` names the old layout (top-level `STAGE_<S>.md`, `INPUTS_<S>.json`) and does not check the new protocol fields | the `marker_check` commit after `CAMPAIGN_MARKER_2.json` | None: the script is not used again before that commit |
| 5 | README step 3 said the manifest is pushed "with its MARKER_CHECK file"; a file pushed after the source commit other than the manifest, its attempt marker and the inventories makes the kit's launch refuse (`allowed_after_freeze`). Found before any harm: `MARKER_CHECK_<S>.txt` goes onto machine a's evidence branch | `1758644` (README procedure rewritten) | None |
| 6 | Machine b's RM1 evidence branch is an orphan commit with the path `evidence/rehearsal-RM1/b/`, while machine a's is based on the prepared commit with `evidence/rehearsal/RM1/a/` | none (pushed files are never changed); later stages use a's layout | None: all 24 files checked against `COLLECTED.json`; that RM1 counts for nothing anyway (incident 2) |
| 7 | A line of `marker_check.py`'s report reads "the 91 frozen paths and the stage file" where it means 90 frozen paths plus the stage file (91 in all) | the `marker_check` commit after `CAMPAIGN_MARKER_2.json` | None: wording only; the check itself compares all 91 paths |
| 8 | While committing `1758644`, the director deleted the working copy of the pushed `CAMPAIGN_RM2.json` with `rm -f`, taking it for an untracked copy | none needed: the deletion was not staged, `1758644` holds only its 3 files, and the copy was restored byte-identical (`187c82fb…`) | None |
