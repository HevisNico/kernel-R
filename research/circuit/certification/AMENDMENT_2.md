# Amendment 2: the compact traces go to the private repository after all

Pushed after stage 1 and before stages 2 and 3. `PREDICTION.md` and
`AMENDMENT_1.md` are not edited.

Amendment 1 is withdrawn. The rule of `PREDICTION.md` applies again: the
compact trace of every run goes to the private repository, and its
SHA-256 is in the public metadata of the run. This holds for the runs of
stage 1, whose traces were still on the machine, and for all later runs.

Reason: a noisy run cannot be computed again. Without its trace, nobody
could check its extraction afterwards.

The SHA-256 recorded for a run is that of its compact trace, the points
that `cert_run.py` keeps. The full output of the solver is read once and
not kept. `cert_run.py` is the script pushed with the rules and is not
modified.

No run, measure, constant, margin or criterion changes.
