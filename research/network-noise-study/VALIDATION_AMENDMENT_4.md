# Noise study: amendment 4 to the validation criteria

The owner's decision. It is pushed alone, after the queue of amendment 3 started and before any summary of attempt
2 is looked at. The runs of the queue go on.

1. **What amendment 3 overrides.** `validation/SPLIT_A2.md` was pushed at 09:45:37 UTC, before attempt 2's first
   noisy draw. It says: "No run is moved or repeated afterwards; a run that fails or is cut is missing, never run
   again elsewhere."

   [`VALIDATION_AMENDMENT_3.md`](VALIDATION_AMENDMENT_3.md) (`59bf911`) and `validation/DEAL_A3.md` (`1d44f60`)
   override this rule for machine 5's 33 runs only: the 4 cut runs are run again, and all 33 run on other machines.

   Amendment 3 should have named this rule, and did not. Its sentence "It changes no criterion and no tolerance" is
   true of the criteria, but amendment 3 changes this rule of the split.
2. **Why it is lifted.** The rule exists so that no draw can be selected. Here every draw is fixed by its seed (V8),
   so a rerun gives the run that would have been made. The decision was taken after the restart and before any
   result was looked at. A simulator abort or an out-of-memory kill is still never rerun (amendment 3, rules 1
   and 2).
3. **When.** This correction is written after the queue's first runs started: the first claim, of run 0, is commit
   `1f98294` at 16:29:06 UTC on `research/network-noise-study-validation-a3-queue`, and the four cut runs were
   claimed between 16:29:06 and 16:29:14 UTC. It is written before any summary of attempt 2 is looked at.
4. **Both verdicts are reported.** The final analysis gives two verdicts side by side:
   - the verdict under amendments 3 and 4;
   - the verdict under `SPLIT_A2.md` as first written, where machine 5's 33 runs count as missing and amendment 3's
     point 5 applies to them.

   It names every criterion that changes between the two.

Nothing else changes. The no-look rule still holds until every run of attempt 2 is done.
