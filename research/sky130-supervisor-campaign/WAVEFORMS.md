# The waveforms of whole runs are public

Added after the campaign. [`PREDICTION.md`](PREDICTION.md) and
[`CAMPAIGN_LOG.md`](CAMPAIGN_LOG.md) say that the waveforms of whole runs
(`trace.raw`, about 1.6 GB) are in the private repository only. They are now
also public, unchanged:

- branch `evidence/sky130-supervisor-campaign-1-waveforms` of this
  repository, commit `8c2e57cde3ee`. The branch holds nothing else and shares
  no history with `main`;
- 123 files, at `machine-a/<run>/evidence/trace.raw` and
  `machine-b/<run>/evidence/trace.raw`, with the `SURVIVORS.json` of each
  machine;
- every file was checked against the SHA-256 of
  [`evidence/machine-a/SURVIVORS.json`](evidence/machine-a/SURVIVORS.json)
  and
  [`evidence/machine-b/SURVIVORS.json`](evidence/machine-b/SURVIVORS.json)
  before the push: no difference.

The run `a55-main-tt27` has no waveform
([`FAILED_RUN_a55-main-tt27.md`](FAILED_RUN_a55-main-tt27.md)).

The raw waveforms of the two qualifications (about 7 GB) are in the private
repository `HevisNico/kernel-R-circuit`, branch `sim/core-loop`, under
`10-supervisor-qualification/`, with their SHA-256 lists; they are not
public.
