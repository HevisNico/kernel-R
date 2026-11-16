# Noise study, validation: amendment 3's 33 runs, one queue

Fixed before any of them runs. The owner's point 4, sent after [`../VALIDATION_AMENDMENT_3.md`](../VALIDATION_AMENDMENT_3.md)
(59bf911) was pushed, replaces that file's point 4. It reads:

> Where they run, fixed now.
> - The 33 runs form one queue, in the order of the plan's list. Each machine that is free takes the next run of
>   the queue, at most four at a time.
> - The machines are 3, 6, 7 and 8 at once; 5 after its restart; 2 and 4 when their own share is done. Machine 1
>   takes none while it runs the two V2c references.
> - Which machine runs which draw cannot change it: every draw is fixed by its seed (V8), and every machine runs
>   the same released code and environment.
> - Before its first run, each machine makes amendment 2's checks again: HEAD adds only `GO`, parent `74e93b4`,
>   tree equal to it, and the environment checks. It records them.
> - Each rerun records its machine, its start and end times, its hashes, its peak memory, and the restart evidence
>   it relies on. The final analysis lists them all.

**The 33 runs.** Machine 5's share of attempt 2 (`SPLIT_A2.md`) has 58 runs. Its `plan.log` (branch
`research/network-noise-study-validation-a2-m5`, 44293c5) lists 25 that ended, all with exit 0; they stand. The
other 33 are the 4 cut runs (orders 0 to 3) and the 29 unstarted ones, in the order of the plan's list.

**How the queue works** (`vdeal.py`).
- The queue is the file `QUEUE.md` on the branch `research/network-noise-study-validation-a3-queue`.
- A machine takes a run by pushing, without force, a commit that adds `claims/<order>.json`, holding the run, the
  machine and the UTC time. A refused push means another machine took that run first; the local commit is then
  dropped and the next run is taken. No run can be taken twice.
- Each machine runs from a checkout of `341aac1`, attempt 2's `GO`, after amendment 2's checks, recorded in
  `MACHINE_K_A3.json`. It runs exactly the plan's command for the run, so the run keeps its noise seed, round and
  position.
- It logs each run's exit code, wall time, peak memory, and start and end times.

**The restart evidence** these reruns rely on is machine 5's `SYSTEM_RESTART.txt`, on its branch:
- its boot time and uptime;
- the plan process gone;
- a search of the cut runs' simulator logs for error lines (counts only, nothing else read);
- the kernel log's out-of-memory lines, where the current boot's log has any.

| Order | Run |
|---|---|
| 0 | `v3_7103_window_a1_r213` |
| 1 | `v3_7103_fire_b_r237` |
| 2 | `v3_7103_pulse_a1_r245` |
| 3 | `v3_7103_pulse_b2_r253` |
| 4 | `v6_nominal_zero` |
| 5 | `v6_nominal_r264` |
| 6 | `v6_nominal_r272` |
| 7 | `v6_nominal_r280` |
| 8 | `v6_nominal_r288` |
| 9 | `v6_7101_r267` |
| 10 | `v6_7101_r275` |
| 11 | `v6_7101_r283` |
| 12 | `v6_7101_r291` |
| 13 | `v6_7102_r266` |
| 14 | `v6_7102_r274` |
| 15 | `v6_7102_r282` |
| 16 | `v6_7102_r290` |
| 17 | `v6_7103_r265` |
| 18 | `v6_7103_r273` |
| 19 | `v6_7103_r281` |
| 20 | `v6_7103_r289` |
| 21 | `tr_7101_r294` |
| 22 | `tr_7102_r294` |
| 23 | `tr_7103_r294` |
| 24 | `v5_nominal_hold_inj4` |
| 25 | `v5_nominal_hold_inj12` |
| 26 | `v5_nominal_hold_inj20` |
| 27 | `v5_nominal_hold_inj28` |
| 28 | `v5_7101_hold_inj4` |
| 29 | `tr_7101_inj4` |
| 30 | `v5_7102_hold_inj7` |
| 31 | `v5_7103_hold_inj2` |
| 32 | `tr_7103_inj2` |
