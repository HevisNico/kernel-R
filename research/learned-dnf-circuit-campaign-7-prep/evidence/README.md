# Preparing a campaign 7: the evidence of the development batch at twice the dose

**Development runs. Exploratory, not preregistered, no claim.** No campaign 7 exists; no campaign seed has been
simulated. These are the files of a development batch of measures on ten development instances (seeds 8301 to
8310), and of a smoke on the nominal cell made before it. No network run and no noisy run was made.

The plan (`BATCH2X_PLAN.md`), the code, the record of each run and the batch's report are on the branch
`research/learned-dnf-circuit-campaign-7-prep`, in `research/learned-dnf-circuit-campaign-7-prep/`. This evidence
branch does not hold them. It starts from the evidence branch of the earlier development work
(`evidence/learned-dnf-circuit-campaign-6-followup`), whose folders it keeps unchanged.

## What is here

| Folder | What |
|---|---|
| [`lists/`](lists/README.md) | the lists of the batch's 90 runs as started, each wave's state, the doses and bounds the waves computed |
| [`smoke/`](smoke/README.md) | the four runs of the smoke on the nominal cell, in full |
| `batch-8301/` to `batch-8310/` | the nine measures of each instance, in full: decks, simulator logs, results or events, waveforms |

The instance folders are published one at a time. A folder that is not here yet has not been pushed yet; the README
of each folder that is here says what it holds.

## How to check a file

- Each folder has a `COLLECTED.json`: every file with its size and SHA-256, written by campaign 5's `collect.py`
  (SHA-256 `62251b67…f432`), which copied each file byte for byte and read it back.
- A file above 100 MiB is split into consecutive parts of 90 000 000 bytes by campaign 6's `publish_evidence.py`;
  the folder's `PARTS.json` lists the parts, and their concatenation in order is the file.
- On the research branch, `dev/batch2x/RUNS_SHA256SUMS` (750 files) and `dev/batch2x/SMOKE_SHA256SUMS` (39 files)
  list every file of the run folders as the runs wrote them, hashed before the batch's report ran. A path
  `./8301-cal-on/…` or `./W1/8301-cal-on.log` of the first list is here under `batch-8301/`; the lists of runs and
  the waves' states are under `lists/`.
- Ten files are not the ones the runs wrote: the lists of runs and the states, which recorded full paths on the
  machine that ran them. `lists/REWRITTEN.sha256` and `smoke/REWRITTEN.sha256` give each one's SHA-256 as written
  and as here. Every other file is as written.
