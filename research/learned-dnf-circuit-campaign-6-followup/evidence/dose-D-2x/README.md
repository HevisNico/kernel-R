# Step D of the dose experiment: the 8 noisy network runs at twice the dose

**Development runs on the nominal cell. Exploratory, not preregistered, no claim.** See
[`../README.md`](../README.md) and [`../../DOSE_PLAN.md`](../../DOSE_PLAN.md). The report of the experiment is
`DOSE_REPORT.md` on the branch `research/learned-dnf-circuit-campaign-6-followup` (commit `0dc1b807`); this evidence
branch does not hold it.

This folder holds 8 of the 16 noisy network runs of step D in full, as `dev/dosedev2.py` ran them: the nominal
cell at twice the dose (`vhi = 0.7`), needs 2, 2, 2, 2, no skew slots, the injected noise model. The other 8 are in
`../dose-D-1x/`.

- One folder per run, `none-2x-noisy-<seed>/`: `evidence/` (the deck as run, the simulator's log, its result, the
  waveform `trace.raw`), `record.json` and `noise.sha256`. Beside the folders, each run's own output `<run>.log`.
- **The noise seeds** are 5200001 to 5200008, declared in `NOISE_SEEDS_DEV.txt` before any noisy run and used once each.
  None is a seed of a campaign.
- `JOBS_D.json` is the list of the 16 runs as started and `STATE.json` the runner's state for the 16; both are in
  each of the two folders.
- [`COLLECTED.json`](COLLECTED.json) lists the 67 files with their size and SHA-256. It was written by campaign 5's
  `collect.py` (SHA-256 `62251b67…f432`), which copied each file byte for byte and read it back.
- **No file is split.** The eight waveforms are 103.6 to 103.9 million bytes each, 98.8 to 99.1 MiB: under the
  100 MiB above which campaign 6's tool splits a file, so each `trace.raw` is whole.
- **Two files are not the ones the runs wrote**: `STATE.json` and `JOBS_D.json` recorded full paths on the machine
  that ran them. Here they are the same two files as on the research branch (`dev/runsD/STATE.json`,
  `dev/JOBS_D.json`), with each path written from that branch's folder. [`REWRITTEN.sha256`](REWRITTEN.sha256) gives
  the SHA-256 of each as written and as here. The other 65 files are as written.
