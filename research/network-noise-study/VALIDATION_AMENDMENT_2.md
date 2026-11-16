# Noise study: amendment 2 to the validation criteria

The owner's decision on the out-of-memory failures of the first attempt. Pushed alone, before anything else runs.
It changes no criterion and no tolerance of [`VALIDATION_CRITERIA.md`](VALIDATION_CRITERIA.md) (5a24d10), as amended
by [`VALIDATION_AMENDMENT_1.md`](VALIDATION_AMENDMENT_1.md) (4169e91).

## 1. Attempt 1 is abandoned

Attempt 1 ran the code released by `GO` (04e139f, releasing 31c8a40) from 08:34 UTC. It was stopped on the owner's
order at about 09:38 UTC: no new run started after that, and the runs already running were left to end.

**Cause.** `vrun.py` runs `tran` without a prior `save`, so ngspice keeps every node and branch vector at every
time point for the whole draw (80 ms at `hold`). That, not the simulation, fills the 16 GB of a machine running four
runs at a time.

**Exit codes**, from each machine's `plan.log`:

| Machine | Exit 0 | Exit 1 | OOM kills in `dmesg` | ngspice anon-rss when killed |
|---|---|---|---|---|
| 2 | 14 | 11 | 13 | 3.6 to 6.2 GB |
| 3 | 14 | 11 | 13 | 3.5 to 6.2 GB |
| 4 | 14 | 9 | 11 | 3.6 to 6.0 GB |

Every machine has 16 087 MB of memory and no swap. The runs that ended with exit 0 were V8 (27 to 32 s), the `hold`
draws of the nominal cell (one cell, 80 ms) and the `pulse` draws. Those with exit 1 were the two-cell `hold` draws
of 7101–7103 and every `window` and `fire` draw that had started.

Examples from `dmesg`:

    machine 2  [Mon Nov 16 08:53:00 2026] Memory cgroup out of memory: Killed process 2248 (ngspice) total-vm:6455624kB, anon-rss:3619888kB, file-rss:2700kB, shmem-rss:0kB, UID:0 pgtables:12672kB oom_score_adj:0
    machine 3  [Mon Nov 16 08:54:34 2026] Memory cgroup out of memory: Killed process 2313 (ngspice) total-vm:6455624kB, anon-rss:4306836kB, file-rss:2552kB, shmem-rss:0kB, UID:0 pgtables:12672kB oom_score_adj:0
    machine 4  [Mon Nov 16 08:57:28 2026] Memory cgroup out of memory: Killed process 2547 (ngspice) total-vm:6455628kB, anon-rss:4311060kB, file-rss:2616kB, shmem-rss:0kB, UID:0 pgtables:12676kB oom_score_adj:0

The full lines, memory snapshots and lists of runs without a result are in `validation/m<K>/SYSTEM.txt` on the
branches `research/network-noise-study-validation-m2` (edb314a), `-m3` (d7cef82) and `-m4` (e3efaea).

Machine 1 made no noisy draw: its share was waiting for the V2c references. Its container restarted between 09:25
and 09:37 UTC, which cut those two references (`validation/m1/SYSTEM.txt`, 3511a95). The kernel log of the earlier
boot is lost, so the cause of the restart is not known.

**No summary of attempt 1 has been looked at.** This decision depends on exit codes and the kernel log only. The
runs of attempt 1 are kept as they are, on their branches. They are reported separately, after the verdict, and
are never compared with a criterion.

## 2. One code change

A `save` of exactly the vectors each analysis reads, before every `tran`:
- V3, V4 and V5: the outputs of the frozen deck;
- V6: the stored and summing nodes of each port;
- V8: the stored voltages;
- the trains: their signals.

The trains run through the router, whose session already saves its signals (`net.Session`) and is unchanged, so
for them nothing changes. Nothing else changes. The proof below adds two things, both test-only and neither
changing a draw: a switch to omit the save (test only), and the recording of each run's peak memory.

## 3. Its proof, before the new GO

The proof uses test rounds from 910, which belong to no criterion and are never analysed as validation draws.
- **Identity.** For one draw of each kind (V3 `hold` on a two-cell instance, `window`, `fire`, `pulse`, V6, V8,
  and a train), the same draw is made with and without the save. The saved vectors must be byte-identical: the
  same `raw_sha256` (the raw file written holds exactly those vectors in both cases) and the same `y_sha256`.

  Without the save a full-length draw is what ran out of memory, so the identity draws of `hold` (10 ms) and of
  `window`, `fire` and `pulse` (2 ms) are shorter than the plan's. V6 (50 µs) and V8 (1 ms) are at their length.
  The train, whose save is the router's and unchanged, is made twice to show it repeats exactly.
- **Memory.** One full-length draw of each kind with the save, four at a time, records its peak memory.

If any pair differs, the proof stops and is reported.

## 4. What stands

V1 and the four extractions stand: they ran no noisy transient. So do the V2c references and the conditioning
check, which are extractions too; the two cut references are run again in attempt 2.

## 5. Attempt 2

- **The whole plan again, with new draws.** Every round is shifted by a fixed offset of **+200**:
  - the nominal cell runs rounds 201 to 288;
  - 7101–7103 run rounds 203 to 297.

  So no noise seed of attempt 1 (rounds 1 to 97) or of the tests (900 and up) is reused, nominal cell included.
  The noise seed rule of amendment 1 and the position rule of `validation/PROTOCOL.md` (k = round − 3, or − 1 for the
  nominal cell) are unchanged. The positions, and so the virtual times, follow the shifted rounds.
- **Eight machines.** Run i of the plan's list goes to machine 1 + (i mod 8), fixed here, four runs at a time on
  each. Each machine records its peak memory (per run, and for the whole machine).
- **V7's "no aborted run in the whole validation" applies to attempt 2.**
- **A new `GO`** releases the corrected code commit. Every machine makes the same checks as before: its HEAD adds
  only `GO`, its parent is the released commit, and its tree is equal to that commit's. It also makes the same
  environment checks, and records both. Each machine pushes its results to
  `research/network-noise-study-validation-a2-m<K>`, into `validation/a2/m<K>/`.
