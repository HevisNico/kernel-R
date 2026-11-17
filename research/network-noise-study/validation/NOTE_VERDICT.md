# Noise study, validation: which verdict governs, and missing runs that enter only V5

The owner's decision. Pushed alone, before any summary of attempt 2 is looked at.

1. **Which verdict governs.** The verdict that governs any use of the model, campaign 4 included, is the one under
   [`../VALIDATION_CRITERIA.md`](../VALIDATION_CRITERIA.md) with its amendments 1 to 4. All of them were pushed
   before any summary was looked at:
   - [`../VALIDATION_AMENDMENT_1.md`](../VALIDATION_AMENDMENT_1.md) (`4169e91`);
   - [`../VALIDATION_AMENDMENT_2.md`](../VALIDATION_AMENDMENT_2.md) (`771e8b7`);
   - [`../VALIDATION_AMENDMENT_3.md`](../VALIDATION_AMENDMENT_3.md) (`59bf911`);
   - [`../VALIDATION_AMENDMENT_4.md`](../VALIDATION_AMENDMENT_4.md) (`dcec16d`).

   The verdict under `SPLIT_A2.md` as first written, with machine 5's 33 runs counted as missing (amendment 4,
   point 4), is reported beside it for transparency only.
2. **Amendment 3's point 5, clarified.** "The model is then not validated" applies when a missing run leaves a
   criterion of the verdict not established: V1, V2, V2b, V2c, V3, V4, V6, V7 or V8.
   - **A missing run that enters only V5.** V5 is reported whatever happens, so the run makes V5's report
     incomplete. The report says so, and the run does not by itself decide the verdict.
   - **A missing run that also feeds the section 3 constants or any criterion of the verdict.** The general rule
     applies.

   This is fixed now, before any result is looked at.
