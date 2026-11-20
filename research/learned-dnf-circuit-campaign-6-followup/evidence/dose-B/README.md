# Step B of the dose experiment: the measures at twice the dose

**Development runs on the nominal cell. Exploratory, not preregistered, no claim.** See
[`../README.md`](../README.md) and [`../../DOSE_PLAN.md`](../../DOSE_PLAN.md). The report of the experiment is
`DOSE_REPORT.md` on the branch `research/learned-dnf-circuit-campaign-6-followup` (commit `0dc1b807`); this evidence
branch does not hold it.

This folder holds the 10 runs of step B in full, as `dev/step_b.py` started them through `dev/dosedev2.py`, all at
twice the dose (`vhi = 0.7`), without noise:

| Folder | What |
|---|---|
| `none-2x-cal-off/` | the guard-off calibration deck |
| `none-2x-scan-a-pair/`, `none-2x-scan-b-pair/` | the scans of the pairs of a and b |
| `none-2x-scan-c-line1/`, `none-2x-scan-c-line2/` | the scans of each line of c |
| `none-2x-bothfire-c/` | the check that both lines of c fire at the preset |
| `none-2x-onesided-a-s4/`, `none-2x-onesided-b-s4/` | the one-sided sets at the plan's bound (about 4 stages) |
| `none-2x-onesided-a-s8/`, `none-2x-onesided-b-s8/` | the one-sided sets at the frozen rule's bound (about 8 stages) |

- Each run's folder: `evidence/` (the deck as run, the simulator's log, its result or events, the waveform
  `trace.raw`), `record.json`, `DOSEDEV.json` (what the wrapper changed in the deck), and `noise.sha256` for the
  calibration deck.
- `B1/` and `B2/` hold the two waves' `STATE.json` and each run's own output `<run>.log`. `JOBS_B1.json` and
  `JOBS_B2.json` are the lists of runs as started; `BOUNDS.json` holds the one-sided bounds computed from the two
  pair scans.
- [`COLLECTED.json`](COLLECTED.json) lists the 86 files with their size and SHA-256. It was written by campaign 5's
  `collect.py` (SHA-256 `62251b67…f432`), which copied each file byte for byte and read it back.
- **Four files are not the ones the runs wrote**: `JOBS_B1.json`, `JOBS_B2.json`, `B1/STATE.json` and
  `B2/STATE.json` recorded full paths on the machine that ran them. Here they are the same four files as on the
  research branch (`dev/runs2x/`), with each path written from that branch's folder. The other 82 files are as
  written.
- No file is above 100 MiB, so none is split. No noise source, no seed, no campaign instance.
