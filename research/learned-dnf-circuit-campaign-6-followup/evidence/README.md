# Evidence of the development work after campaign 6

**Development runs on the nominal cell. Exploratory, not preregistered, no claim.** See
[`../README.md`](../README.md).

`smokes/` holds the two guard-on calibration decks of [`../DOSE_PLAN.md`](../DOSE_PLAN.md) in full, as they were
run by [`../dev/dosedev.py`](../dev/dosedev.py):

| Folder | Dose | Deck as run (SHA-256 of `evidence/input.spice`) | Waveform (SHA-256 of `evidence/trace.raw`) |
|---|---|---|---|
| `smokes/none-1x-cal-on/` | unchanged | `a6700b4c8f495312e81dd6ff8536280ff70de59f0cb36756ee7d7ba181cc8d9b`, the frozen deck byte for byte | `4abff018863b9cbe02958b7bc7236b7ae65655dc281a2dc2e2d72da99349a81c` |
| `smokes/none-2x-cal-on/` | twice (`vhi = 0.7`) | `de3109247965def94c25cf16ac69766216682de1fba87663976a08c2b0b9fb8d` | `84b9f4202c0a4fc34e1246abd4ab231b65934692c596fa0e1ad75bb94c1edc6d` |

- Each folder: `evidence/` (the deck, the simulator's log, its result and the waveform), `record.json`,
  `DOSES.json`, `noise.sha256`; beside it, the run's own output `<run>.log`.
- [`smokes/COLLECTED.json`](smokes/COLLECTED.json) lists the 19 files with their size and SHA-256. It was written
  by campaign 5's `collect.py` (SHA-256 `62251b67…f432`), which copied each file byte for byte and read it back.
- `none-1x-cal-on/DOSES_as_run.json` is what the run itself wrote. `DOSES.json` beside it was written afterwards
  from the same waveform, by the version of `dosedev.py` that also reads the timing of a write; the doses, the
  moves and the reads are the same in both.
- In `smokes/`: no noise source, no seed, no campaign instance. The waveforms are under 100 MiB each, so none is
  split.

## The dose experiment, steps B to D

Four folders hold the 31 runs of steps B to D of [`../DOSE_PLAN.md`](../DOSE_PLAN.md) in full, one folder per
step, each with its own `README.md` and its own `COLLECTED.json`:

| Folder | Runs | Files in `COLLECTED.json` | Split files |
|---|---|---|---|
| [`dose-B/`](dose-B/README.md) | the 10 measure runs at twice the dose | 86 | none |
| [`dose-C/`](dose-C/README.md) | the two quiet network runs and three more scans | 42 | none |
| [`dose-D-1x/`](dose-D-1x/README.md) | the 8 noisy network runs at the unchanged dose | 67 | the 8 waveforms, two parts each |
| [`dose-D-2x/`](dose-D-2x/README.md) | the 8 noisy network runs at twice the dose | 67 | none (98.8 to 99.1 MiB each) |

- The report of the experiment is `DOSE_REPORT.md` on the branch `research/learned-dnf-circuit-campaign-6-followup`
  (commit `0dc1b807`), with the experiment's code (`dev/dosedev2.py` and the readers) and their outputs. This
  evidence branch was started from that branch's first commit (`691f714d`) and does not hold them.
- Every file was copied by campaign 5's `collect.py` and is listed in its folder's `COLLECTED.json` with its size
  and SHA-256. A file above 100 MiB is in consecutive parts of 90 000 000 bytes, listed in the folder's
  `PARTS.json`; `cat <file>.part-000 <file>.part-001 > <file>` rejoins it.
- In each folder, the lists of runs (`JOBS_*.json`) and the runner's `STATE.json` are not the files the runs wrote:
  they recorded full paths on the machine that ran them, and are here as on the research branch, with each path
  written from that branch's folder. Each folder's `REWRITTEN.sha256` gives their SHA-256 as written and as here.
  Every other file is as the runs wrote it.
- The 16 noisy runs use the development noise seeds 5100001 to 5100008 and 5200001 to 5200008, declared before any
  noisy run. No run here is a campaign's, and no seed here is a campaign's.
