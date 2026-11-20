# Three scans of the nominal cell at a tighter solver tolerance

**Development runs on the nominal cell. Exploratory, not preregistered, no claim.** See
[`../README.md`](../README.md). The account of these runs is section 3 of `DOSE_ADDENDUM.md` on the branch
`research/learned-dnf-circuit-campaign-6-followup`; this evidence branch does not hold it.

This folder holds three pair scans in full, as `dev/dosedev_tol.py` ran them, with the solver's relative tolerance
rewritten from `reltol=1e-4` to `reltol=1e-5` on the deck's `.option` line (`abstol`, `vntol` and `chgtol` kept),
without noise:

| Folder | What |
|---|---|
| `none-2x-scan-a-pair-tol5/` | the pair scan of a at twice the dose (`vhi = 0.7`), `reltol = 1e-5` |
| `none-2x-scan-b-pair-tol5/` | the pair scan of b at twice the dose, `reltol = 1e-5` |
| `none-1x-scan-a-pair-tol5/` | the pair scan of a at the unchanged dose, `reltol = 1e-5` |

- Each run's folder: `evidence/` (the deck as run, the simulator's log, its events, the waveform `trace.raw`),
  `record.json` and `DOSEDEV.json` (what the wrapper changed in the deck). Beside the folders, each run's own output
  `<run>.log`, the list of runs as started (`JOBS_T2.json`) and the runner's `STATE.json`.
- The same scans at `reltol=1e-4` are in `../dose-B/`, `../dose-C/` (the two scans at twice the dose, run twice, and
  the scan of a at the unchanged dose).
- [`COLLECTED.json`](COLLECTED.json) lists the files with their size and SHA-256. It was written by campaign 5's
  `collect.py` (SHA-256 `62251b67…f432`), which copied each file byte for byte and read it back.
- **Two files are not the ones the runs wrote**: `STATE.json` and `JOBS_T2.json` recorded full paths on the machine
  that ran them. Here they are the same two files as on the research branch (`dev/runsT2/STATE.json`,
  `dev/JOBS_T2.json`), with each path written from that branch's folder. [`REWRITTEN.sha256`](REWRITTEN.sha256) gives
  the SHA-256 of each as written and as here. The other files are as written.
- No file is above 100 MiB, so none is split. No noise source, no seed, no campaign instance.
