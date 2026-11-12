# Amendment 1: where the compact traces go

Pushed while stage 1 is running and before stages 2 and 3. `PREDICTION.md`
is not edited.

`PREDICTION.md` says that the compact traces go to the private repository.
They do not. Only the five traces of the preflight were put there, before
this amendment. From now on a compact trace stays on the machine of the
session and is not kept after it.

What stays public is unchanged: for each run, its row of measures per
pulse, its metadata, and the SHA-256 of its compact trace. Every number of
the analysis comes from these rows. What is lost is the possibility of
measuring something else on these runs later: a noisy run cannot be
computed again.

No run, measure, constant, margin or criterion changes.
