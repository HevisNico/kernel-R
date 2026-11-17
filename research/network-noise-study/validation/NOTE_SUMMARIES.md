# Noise study, validation: verifiable summaries, and no look before the end

The owner's two additions, pushed before `GO`.

1. **Verifiable summaries.** Waveforms do not travel between machines, so every per-draw result records what it
   was computed from:
   - its noise seed and run position;
   - the SHA-256 of each samples file;
   - the SHA-256 of the simulator's raw waveform (`raw_sha256`) and of the linearized waveform the summary is
     computed from (`y_sha256`).

   Frozen draws record all of these. V6 records the seed, the position, the samples files and the raw waveform.
   V8 records the raw waveform and carries its stored voltages. Each train's `result.json` has the raw waveform,
   and its `meta.json` has the seed, the position and the samples files.

   Any draw can then be regenerated from its seed and position, and checked hash by hash.

2. **No look before the end.** The summaries are computed on each machine, as each run ends, by the code
   committed on this branch at `GO`: `vrun.summarize` for the frozen draws, `vrun.preset` and `vrun.seeding` for
   V6 and V8, and the router for the trains. Before all four machines have finished:
   - no summary is compared with a criterion, pooled, or inspected for a verdict;
   - the progress reports give only run counts, exit codes and wall times.

   The verdict comes from one final analysis (`vanalyze.py`, `vextract.py`) over all machines, as in the campaigns.

3. **The released code.** `GO` states the full hash of the commit C whose code it releases (`vrun.summarize` and
   every run). The commit that adds `GO` changes nothing else, and its only parent is C (a commit cannot hold its
   own hash). Each machine, after its `merge --ff-only` and before its first run, checks that its HEAD is that
   commit, with nothing changed but `GO` and a clean tree (`vplan.released`). It records C and its HEAD in
   `MACHINE_K.json`. A machine on another commit runs nothing.

The extractions (V2, V2b, V2c and their equality with phase 0) are deterministic and gate `GO`. They are checked
before it, as the protocol says.
