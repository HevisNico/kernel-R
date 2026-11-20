# The development batch at twice the dose: the lists of its runs

**Development runs. Exploratory, not preregistered, no claim.** See [`../README.md`](../README.md). The plan,
the code and the batch's report are on the branch `research/learned-dnf-circuit-campaign-7-prep`; this evidence
branch does not hold them.

The lists of the batch's 90 runs as they were started (`JOBS_W1.json` to `JOBS_W3.json`), each wave's state as
the runner left it (`W1/STATE.json` to `W3/STATE.json`), the doses wave 2 computed from each instance's two
calibration decks (`DOSES.json`), the bounds wave 3 computed from each instance's two pair scans
(`BOUNDS.json`), and what waves 2 and 3 did not start (`NOT_STARTED_W2.json`, `NOT_STARTED_W3.json`: nothing).

- [`COLLECTED.json`](COLLECTED.json) lists the files with their size and SHA-256. It was written by campaign 5's
  `collect.py`, which copied each file byte for byte and read it back.
- **Six files are not the ones the runs wrote**: the three `JOBS_*.json` and the three `STATE.json` recorded full
  paths on the machine that ran them. Here they are the same files as on the research branch, with each path
  written from that branch's folder. [`REWRITTEN.sha256`](REWRITTEN.sha256) gives the SHA-256 of each as written
  and as here. The other four files are as written.
- 10 files, 79184 bytes. No file is above 100 MiB, so none is split.
