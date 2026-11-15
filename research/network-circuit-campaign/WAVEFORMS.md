# The waveforms of the campaign are public

Added after the campaign, after its one analysis. [`PREDICTION.md`](PREDICTION.md)
says that the waveforms (`trace.raw`) are committed to the private repository
`HevisNico/kernel-R-circuit` only, with their SHA-256 in this repository. They
are now also public, unchanged:

- branch `evidence/network-circuit-campaign-1-waveforms` of this repository,
  commit `34e68cc0be5d`. The branch holds nothing else and shares no history
  with `main`;
- 64 files, at `<stage>/<run>/evidence/trace.raw` for the four stages
  `measures-a`, `measures-b`, `runs-a` and `runs-b`, with the `SURVIVORS.json`
  of each stage (2.56 GB in all);
- every file was checked against the SHA-256 of
  [`evidence/measures-a/SURVIVORS.json`](evidence/measures-a/SURVIVORS.json),
  [`evidence/measures-b/SURVIVORS.json`](evidence/measures-b/SURVIVORS.json),
  [`evidence/runs-a/SURVIVORS.json`](evidence/runs-a/SURVIVORS.json) and
  [`evidence/runs-b/SURVIVORS.json`](evidence/runs-b/SURVIVORS.json)
  before the push, and again in the pushed branch: 64 of 64 identical. Each
  `SURVIVORS.json` of the branch is byte-identical to the one in `evidence/`.

The source is the four branches `network-campaign-1/measures-a`,
`network-campaign-1/measures-b`, `network-campaign-1/runs-a` and
`network-campaign-1/runs-b` of the private repository, at commits
`38bf109e6738`, `ddeb822a0626`, `c3c6032a976e` and `4a30d5a4260d`.

Nothing in this folder was changed for the publication; no rule, prediction or
result depends on it. The runs without noise give the same waveform when made
again from the decks in `evidence/`.
