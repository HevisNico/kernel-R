# Noise study: amendment 3 to the validation criteria

The owner's decision on machine 5's restart. Pushed alone, before any of the runs below and before any summary is
looked at. It changes no criterion and no tolerance of [`VALIDATION_CRITERIA.md`](VALIDATION_CRITERIA.md), as
amended by [`VALIDATION_AMENDMENT_1.md`](VALIDATION_AMENDMENT_1.md) and
[`VALIDATION_AMENDMENT_2.md`](VALIDATION_AMENDMENT_2.md).

1. **Rule for container restarts.**
   - A run is killed by a restart of its container when four things show it:
     - the boot time or uptime;
     - the plan process gone;
     - no simulator error in its log;
     - no out-of-memory line in the kernel log, where one exists.
   - Such a run is run once more, with the same noise seed, round and position, under the same released code
     (`74e93b4`, `GO` at `341aac1`). Every draw is fixed by its seed (V8), so the rerun gives the run that would have
     been made, and no draw can be selected.
   - A run killed a second time is missing.
   - A run killed with an out-of-memory line in the kernel log is not covered by this rule: it is an aborted run.
2. **V7's "no aborted run" means a simulator abort:** an ngspice error, a "timestep too small", a non-zero exit of a
   run that ran to its end, or an out-of-memory kill. A run killed by a documented container restart is not an
   aborted run once it has been rerun under rule 1.
3. **Machine 5.**
   - What is known: the container restarted between 15:15 and 16:10 UTC. The machine's recorded peak memory was
     2 300 MB of 16 087 MB at its last record (15:15). Its 25 completed runs all exited 0. Amendment 2's proof
     measured 364 to 480 MB per run, four at a time.
   - The kernel log of the earlier boot is lost, so the cause of the restart is not known, and this decision does not
     claim it.
   - Its 25 completed runs stand. Its 4 cut runs (`v3_7103_window_a1_r213`, `v3_7103_fire_b_r237`,
     `v3_7103_pulse_a1_r245`, `v3_7103_pulse_b2_r253`) and its 29 unstarted runs are run under rule 1. Any partial
     output of the cut runs is discarded unread.
4. **Where they run, fixed now.**
   - The 33 runs, in the order of the plan's list, are dealt in turn to the machines that have finished their share,
     in order of machine number, four at a time on each.
   - Before its first run, each receiving machine makes amendment 2's checks again: HEAD adds only `GO`, parent
     `74e93b4`, tree equal to it, and the environment checks. It records them.
   - Each rerun records its machine, its hashes, its peak memory, and the restart evidence it relies on. The final
     analysis lists them all.
5. **A run still missing after rule 1:** every criterion that uses it is not established, and the model is then not
   validated. This is fixed now, before any result is looked at.

Nothing else changes. The no-look rule still holds until every run of attempt 2 is done.
