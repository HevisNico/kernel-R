# Step C of the dose experiment: the quiet network runs, and three more scans

**Development runs on the nominal cell. Exploratory, not preregistered, no claim.** See
[`../README.md`](../README.md) and [`../../DOSE_PLAN.md`](../../DOSE_PLAN.md). The report of the experiment is
`DOSE_REPORT.md` on the branch `research/learned-dnf-circuit-campaign-6-followup` (commit `0dc1b807`); this evidence
branch does not hold it.

This folder holds the 5 runs of step C in full, as `dev/dosedev2.py` ran them, all without noise:

| Folder | What |
|---|---|
| `none-1x-quiet/` | the network run at the unchanged dose, needs 4, 4, 4, 4, with the two skew slots |
| `none-2x-quiet/` | the network run at twice the dose (`vhi = 0.7`), needs 2, 2, 2, 2, with the two skew slots |
| `none-2x-scan-a-pair-r2/`, `none-2x-scan-b-pair-r2/` | the two pair scans of step B run a second time (outside the plan) |
| `none-1x-scan-a-pair-here/` | the pair scan of a at the unchanged dose, run on this machine (outside the plan) |

- Each run's folder: `evidence/` (the deck as run, the simulator's log, its result or events, the waveform
  `trace.raw`), `record.json`, and `noise.sha256` or `DOSEDEV.json`. Beside the folders, each run's own output
  `<run>.log`, the list of runs as started (`JOBS_C.json`) and the runner's `STATE.json`.
- [`COLLECTED.json`](COLLECTED.json) lists the 42 files with their size and SHA-256. It was written by campaign 5's
  `collect.py` (SHA-256 `62251b67…f432`), which copied each file byte for byte and read it back.
- **Two files are not the ones the runs wrote**: `STATE.json` and `JOBS_C.json` recorded full paths on the machine
  that ran them. Here they are the same two files as on the research branch (`dev/runsC/STATE.json`,
  `dev/JOBS_C.json`), with each path written from that branch's folder. [`REWRITTEN.sha256`](REWRITTEN.sha256) gives
  the SHA-256 of each as written and as here. The other 40 files are as written.
- No file is above 100 MiB, so none is split. No noise source, no seed, no campaign instance.
