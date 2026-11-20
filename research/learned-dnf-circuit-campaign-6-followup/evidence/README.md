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
- No noise source, no seed, no campaign instance. The waveforms are under 100 MiB each, so none is split.
