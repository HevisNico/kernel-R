# The smoke before the batch: four runs on the nominal cell

**Development runs. Exploratory, not preregistered, no claim.** See [`../README.md`](../README.md). The plan,
the code and the batch's report are on the branch `research/learned-dnf-circuit-campaign-7-prep`; this evidence
branch does not hold them.

Four runs on the nominal cell (no mismatch, no seed), at twice the dose (`vhi = 0.7`) and `reltol = 1e-5`, made
before the batch to check the code and the cost of a run:

| Folder | What |
|---|---|
| `none-smoke-cal-on/` | the guard-on calibration deck |
| `none-smoke-cal-off/` | the guard-off calibration deck |
| `none-smoke-bothfire-c/` | the both-lines check of c |
| `none-smoke-onesided-a/` | the one-sided set of a |

- Each run's folder: `evidence/` (the deck as run, the simulator's log, the waveform `trace.raw`, and the run's
  result or events), `record.json` and `DOSEDEV.json` (what the wrapper changed in the deck). Beside them: the
  lists of runs as started (`JOBS_S1.json`, `JOBS_S2.json`), each step's `STATE.json` and each run's own output
  (`S1/`, `S2/`), and the doses read from the two decks (`DOSES.json`).
- [`COLLECTED.json`](COLLECTED.json) lists the files with their size and SHA-256. It was written by campaign 5's
  `collect.py`, which copied each file byte for byte and read it back.
- **Four files are not the ones the runs wrote**: the two `JOBS_*.json` and the two `STATE.json`, for the same
  reason and in the same way as in [`../lists/`](../lists/README.md). [`REWRITTEN.sha256`](REWRITTEN.sha256)
  gives the SHA-256 of each as written and as here. The other files are as written.
- 39 files, 208489645 bytes. No file is above 100 MiB, so none is split.
- No noise source, no seed, no campaign instance.
