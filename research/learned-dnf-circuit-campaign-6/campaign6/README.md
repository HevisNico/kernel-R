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

1. **The source commit.** On `-impl`, a commit on top of the frozen implementation adds only this stage's files:
   - its stage file `STAGE_<name>.md` (`stages6.py stage-file`), whose governing protocol is `PREDICTION.md` with its
     SHA-256 (safeguard i);
   - for M2 and M3 (RM2 and RM3), its inputs file, written by `inputs6.py` from the collected evidence of the stages
     before it;
   - for Q and the N stages, `PREDICTED.json` and the Lean files of the gate;
   - for RN, nothing more: `rehearsal/PREDICTIONS_BATCH.json` is already in the implementation;
   - the two machines' inventories.

   **Each inputs file is pushed before its stage's manifest.** The manifest binds it, the stage file and every frozen
   file by their SHA-256 at that source commit (`stages6.manifest`). Nothing else may differ from the frozen
   implementation (the kit's `runtime_unchanged`, and the CI gate on that exact commit).
2. **The manifest**, `stages6.py manifest STAGE OUT SOURCE_COMMIT [input]`, is checked as the kit checks it (both
   shards, the round-robin order, the budget), then pushed with its attempt marker.
3. **The launch**, one per machine, detached, with the sessions active. A started run is never relaunched.
4. **The collection**, with campaign 5's `collect.py`, then the evidence branches.

**`check-noise`** (`launch.py check-noise`) is applied to the evidence of the **N stages only** (and RN's noisy runs),
where noise is drawn, and must report every fingerprint distinct. The runs without noise (decks, scans, the runs
without noise, the untrained run) share their fingerprint by design. That is expected and is not a failure. Campaign
5's code never called `check-noise`, so this is a stated choice of campaign 6, not a precedent.

**Before the campaign's marker.** RN's end-to-end analysis must show `predicted6_is_reproduced` true, and every check
of `PREDICTION.md` 7 must pass. Its verdicts are discarded.
- Its prediction record is `predicted6.predictions` for seeds 7701 and 7706 on the batch's merged evidence (`batch_dir`:
  machine a's `d9e431b` and machine b's `88a34de`, merged as the batch merged them), with its own Lean files.
- `analyze6` then reproduces that record byte for byte.
