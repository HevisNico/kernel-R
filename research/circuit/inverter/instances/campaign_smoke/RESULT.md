# Campaign kit smoke test: dev seeds 9711 and 9712

`python -m invinst.campaign OUTDIR --seeds 9711,9712` was run at commit 59a4832, with a clean package tree.

## Result

- 2 of 2 jobs ok.
- Both instances are eligible at K0 and have room at K3. `first_failing` is null for both.
- The K3 silence margin is 0.1527 for 9711 and 0.1564 for 9712.
- `campaign.load(OUTDIR)` verifies all of `OUTDIR_SHA256SUMS`.
- Both gate files are byte-identical in three runs: this run, a first smoke run made before the commit, and lot 2 at
  netopts (dev_lot_2/RESULT_LOT2_NETOPTS.md). The decks and traces are identical too.

## Cost

- 72.6 s and 71.7 s CPU per instance; `machine_minutes_jobs` is 2.45 for the 2 jobs.
- The wall time was 1 min 23 s in all, with a warm Lean build cache. The run made before the commit took 2 min 56 s,
  including a cold library build of about 1.6 min.

## Kept here

The traces are not kept here. They are listed with their hashes in `OUTDIR_SHA256SUMS`, which is the run folder's
SHA256SUMS. The folder kept the following:
- `INVERTERS.json`;
- `records/`;
- `JOBS`;
- `CAMPAIGN_INPUT.json`;
- `SUMMARY.json`.
