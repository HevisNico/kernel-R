# The development batch at twice the dose: instance 8306

**Development runs. Exploratory, not preregistered, no claim.** See [`../README.md`](../README.md). The plan,
the code and the batch's report are on the branch `research/learned-dnf-circuit-campaign-7-prep`; this evidence
branch does not hold them.

The nine measures of development instance 8306 (mismatch on, the seed given to the simulator), at twice the
dose (`vhi = 0.7`) and `reltol = 1e-5`, without noise:

| Folder | What | Wave |
|---|---|---|
| `8306-cal-on/` | the guard-on calibration deck | 1 |
| `8306-cal-off/` | the guard-off calibration deck | 1 |
| `8306-scan-a-pair/` | the pair scan of a | 2 |
| `8306-scan-b-pair/` | the pair scan of b | 2 |
| `8306-scan-c-line1/` | the scan of line 1 of c | 2 |
| `8306-scan-c-line2/` | the scan of line 2 of c | 2 |
| `8306-bothfire-c/` | the both-lines check of c | 2 |
| `8306-onesided-a/` | the one-sided set of a | 3 |
| `8306-onesided-b/` | the one-sided set of b | 3 |

- Each run's folder: `evidence/` (the deck as run, the simulator's log, the waveform `trace.raw`, and the run's
  result or events), `record.json` and `DOSEDEV.json` (what the wrapper changed in the deck). `W1/`, `W2/` and
  `W3/` hold each run's own output. The lists of runs and the waves' states are in
  [`../lists/`](../lists/README.md).
- [`COLLECTED.json`](COLLECTED.json) lists the files with their size and SHA-256. It was written by campaign 5's
  `collect.py`, which copied each file byte for byte and read it back.
- Every file is as the runs wrote it.
- 74 files, 655770114 bytes. **2 files are above 100 MiB and split** by campaign 6's `publish_evidence.py` into consecutive parts of
  90 000 000 bytes (`<file>.part-000`, ...): `8306-cal-off/evidence/trace.raw`, `8306-cal-on/evidence/trace.raw`.
  [`PARTS.json`](PARTS.json) gives each part's size and SHA-256; their concatenation in order is the file.
- A development instance: it counts nothing for any campaign. No noise source.
