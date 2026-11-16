# Campaign 4, amendment 6: what two runs of one noise seed may differ in

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 5 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`), after the implementation was frozen and
before its rehearsal. It is the owner's decision. Nothing else in `PREDICTION.md` or amendments 1 to 5 changes.

**No campaign seed (7501 and up) has been simulated, and nothing here depends on campaign-4 data or on any result of
the noise study's validation.** Every run below is on the nominal cell (model section `tt`, no mismatch, no seed).

## 1. The rule this states

`PREDICTION.md` (Noise model, "Every noisy run is reproducible from its seed") asks that two noisy runs with the
same noise seed give "byte-identical records (the field `wall_s` aside) and byte-identical waveforms (the date line
of the raw file aside)". A run's record also holds its name, the peak memory of its simulator, and the SHA-256 of its
evidence files, some of which carry the time of day or the timing of the simulator. This amendment lists those
fields and says how their content is still compared. It was written after the runs of section 4 showed them.

## 2. The differences allowed, and why none of them carries data

Between the records of two runs with the same deck, instance seed and noise seed, only these fields may differ:

1. `id`: the run's name, given by its run list. Two runs need two names.
2. `wall_s`: the run's wall time, as `PREDICTION.md` already allows.
3. `peak_rss_MB`: the peak memory of the simulator process, as measured by the runner. It depends on the operating
   system and not on the simulation.
4. `files.trace.raw`: the SHA-256 of the waveform file. Its `Date:` line is the simulator's wall-clock time at the
   start of the run, which `PREDICTION.md` already sets aside.
5. `files.result.json`: the SHA-256 of the run's result file. That file holds the run's own `wall_s`.
6. `files.session.log`: the SHA-256 of the simulator's log. During a transient, ngspice 42 prints a progress line,
   ` Reference value : ` followed by the simulated time reached, at wall-clock intervals. The number and values of
   those lines depend on timing. They report no computed value, and no measure is read from the log: the launch kit
   only scans it for the simulator's fatal markers.

Every other field of the record must be equal: among them the deck's SHA-256 (`files.input.spice`), the noise
(model, sources, noise seed, samples' SHA-256), the noise fingerprint, the points, the slots, the horizon, and the
waveform ends.

## 3. The strict comparisons that remain

The three files of items 4 to 6 are compared apart, by the frozen rehearsal:

1. the waveforms: `trace.raw` byte for byte, with its `Date:` line removed;
2. the result: `result.json` equal as data, with its `wall_s` field removed;
3. the log: `session.log` line for line, with the lines that begin with ` Reference value : ` removed.

The other checks of `PREDICTION.md` (two noise seeds give two noises; the same operating point; the samples file
regenerated to the same SHA-256) are unchanged. The rehearsal keeps both `session.log` files of each pair in its
collected evidence.

## 4. What the smoke runs showed (2026-11-16)

After the first freeze of the implementation (commit `c69e21d`), and before any rehearsal run, a smoke run found that
the device model's deck named its samples file by an absolute path; the fix is commit `3e63391`. On that commit, two
smoke runs, Dev-None-A and Dev-None-B, both started at 17:28 UTC: the device model, the nominal cell, one noise seed
(90951), the same deck (SHA-256 `31eef017d74de686398e691911d940835e4fa21fd21e78ebfdff1bc46e3e0f7e`). Their records
differed in exactly five fields:

- `id`: Dev-None-A, Dev-None-B;
- `wall_s`: 777.8 s, 758.7 s;
- `peak_rss_MB`: 611.49, 611.69;
- `files.result.json`: the two files differ only in their `wall_s`;
- `files.session.log`: the two logs differ only in their progress lines (2912 and 2841 of them). Without those lines
  they are identical, 4775 lines each.

Their `trace.raw` files were byte-identical, including their date line, because both runs started within the same
second. No other field differed. The noise fingerprint was the same in both:
`be0c89510573ed1fe7c5636f8b4275fcc25962911aa2cb2f7337ed43717012f1`.

## 5. Later amendments and safeguard (ii)

A stage's source commit on this branch contains this file, which is not in the closed list of amendment 5
(section 1, item 3). So that list now also has **the amendments pushed after the freeze** (`AMENDMENT_6.md` and
later). Amendments 1 to 5 stay frozen files: a source commit that changes one of them is still refused.
