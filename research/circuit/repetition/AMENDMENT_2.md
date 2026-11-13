# Amendment 2: a restart of machine A during repetition 6

Pushed before any run is started again. `PREDICTION.md` and amendment 1
are not edited.

## What happened

On 2026-11-13, a little after 10:30 UTC, the container of machine A was
restarted by its host while it was running repetition 6. Nothing in the
campaign caused it. Repetitions 0, 2 and 4 were already pushed. Of the
52 runs of repetition 6, 21 had ended, with their rows, charges,
metadata and reduced trace on the disk of the machine, which survived
the restart. The runs that were in progress were killed in the
simulator. They left no result and no failure file: `rep_run.py` writes
the files of a run only after the simulator has ended.

## What is done

The 21 runs that ended are kept as they are. The 31 others of repetition
6 are run by the same script. A killed run is not a failed run: it gave
no result. And running it again is not a second draw: each run has its
own noise number, which fixes the noise that the simulator draws
(`PREDICTION.md`, preflight of both machines), so the run that is
started again is the run that was killed, with the same noise.

The same holds for any later restart of either machine, and will be
reported in the same way: which repetition, how many runs had ended.
A run that ended with a failure stays failed and is never run again.

The even repetitions 6 to 18 continue on machine A in the same order.
