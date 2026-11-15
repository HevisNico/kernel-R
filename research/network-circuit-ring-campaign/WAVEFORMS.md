# The waveforms of the campaign are public

Added after the campaign, after its one analysis, as [`PREDICTION.md`](PREDICTION.md) says ("after the one
analysis to an evidence branch of this repository with no shared history"):

- branch `evidence/network-circuit-ring-campaign-2-waveforms` of this repository, four commits, one per stage
  (`ed15290`, `49298da`, `c46338d`, `1e54a5710518`). The branch holds nothing else and shares no history with
  `main`;
- 46 waveforms, at `<stage>/<run>/evidence/trace.raw` for the four stages `measures-a`, `measures-b`, `runs-a` and
  `runs-b` (3.01 GB in all), with the `SURVIVORS.json` of each stage, byte-identical to the one in `evidence/`;
- the 14 waveforms above 100 MiB (every network run except `a-7303-ring-quiet`, `b-7304-ring-quiet` and
  `b-7306-ring-control`; no measure run) are stored as consecutive parts of 90 000 000 bytes,
  `trace.raw.part-000`, ..., whose concatenation in order is the file; `<stage>/PARTS.json` gives the SHA-256 of
  every part and of the whole file;
- every waveform, joined from its parts where it was split, was checked against the SHA-256 of
  [`evidence/measures-a/SURVIVORS.json`](evidence/measures-a/SURVIVORS.json),
  [`evidence/measures-b/SURVIVORS.json`](evidence/measures-b/SURVIVORS.json),
  [`evidence/runs-a/SURVIVORS.json`](evidence/runs-a/SURVIVORS.json) and
  [`evidence/runs-b/SURVIVORS.json`](evidence/runs-b/SURVIVORS.json) before the push, and again in a fresh clone of
  the pushed branch: 46 of 46 identical.

The source is the four branches `network-campaign-2/measures-a`, `network-campaign-2/measures-b`,
`network-campaign-2/runs-a` and `network-campaign-2/runs-b` of the private repository `HevisNico/kernel-R-circuit`,
at commits `4dd0826`, `92df8f5`, `5277d54` and `515c126`.

Nothing in this folder was changed for the publication; no rule, prediction or result depends on it. The runs
without noise give the same waveform when made again from the decks in `evidence/`.
