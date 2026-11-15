# The waveforms of the campaign are public

Added after the campaign, after its one analysis, as [`PREDICTION.md`](PREDICTION.md) says ("after the one
analysis to an evidence branch of this repository with no shared history"):

- branch `evidence/network-circuit-ring-campaign-3-waveforms` of this repository, four commits, one per stage
  (`1ad1097`, `50aa65e`, `7fc0ddd`, `c0338bd457ab`). The branch holds nothing else and shares no history with
  `main`;
- 83 waveforms, at `<stage>/<run>/evidence/trace.raw` for the four stages `measures-a` (30), `measures-b` (30),
  `runs-a` (10) and `runs-b` (13), 5.4 GB in all, with the `SURVIVORS.json` of each stage, byte-identical to the one
  in `evidence/`;
- the 14 waveforms above 100 MiB (every network run except `a-7401-ring-quiet`, `a-7401-ring-noisy1`,
  `a-7403-ring-quiet`, `a-7403-ring-noisy1`, `a-7404-ring-quiet`, `a-7405-ring-quiet`, `b-7407-ring-quiet`,
  `b-7410-ring-quiet` and `b-7411-ring-control`; no measure run) are stored as consecutive parts of 90 000 000
  bytes, `trace.raw.part-000`, ..., whose concatenation in order is the file; `<stage>/PARTS.json` gives the SHA-256
  of every part and of the whole file;
- every waveform, joined from its parts where it was split, was checked against the SHA-256 of
  [`evidence/measures-a/SURVIVORS.json`](evidence/measures-a/SURVIVORS.json),
  [`evidence/measures-b/SURVIVORS.json`](evidence/measures-b/SURVIVORS.json),
  [`evidence/runs-a/SURVIVORS.json`](evidence/runs-a/SURVIVORS.json) and
  [`evidence/runs-b/SURVIVORS.json`](evidence/runs-b/SURVIVORS.json) before the push, and again in the pushed
  branch, stage by stage: 83 of 83 identical.

The source is the four branches `network-campaign-3/measures-a`, `network-campaign-3/measures-b`,
`network-campaign-3/runs-a` and `network-campaign-3/runs-b` of the private repository `HevisNico/kernel-R-circuit`,
at commits `a2674e6`, `281aaca`, `8f4a56b` and `5f5edbe`.

Nothing in this folder was changed for the publication; no rule, prediction or result depends on it. The runs
without noise give the same waveform when made again from the decks in `evidence/`.
