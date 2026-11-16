# Noise study, amendment 2: the noise-model choice may follow campaign 4's preregistration

Fixed by the owner on 2026-11-16 and pushed alone on the branch `research/network-noise-study-amendment-2`, **while the
device model's validation runs (attempt 2) and before its verdict is known**, and before campaign 4's
`PREDICTION.md` is pushed. No run of campaign 4 has started, and none of its seeds has been simulated. It changes
only the timing in point 6 of [`AMENDMENT_1.md`](AMENDMENT_1.md); points 1 to 5 are unchanged.

1. **Campaign 4's preregistration may be pushed before the validation's verdict.** It then fixes, as rules, what the
   verdict decides: the device model if it is validated; otherwise the choice of point 6 of amendment 1.
2. **Point 6 of amendment 1, as amended:** if the model is not validated, the default is the simulator's built-in
   noise, and a corrected model is allowed only with an independent justification and without looking at any
   campaign-4 data. Whichever is chosen is pushed alone **before the first run of campaign 4** (its stage M), in
   place of "before any preregistration of campaign 4".
3. **Why.** Freezing campaign 4 before the verdict means it cannot be fitted to the validation's outcome, and its
   implementation and rehearsal can proceed while the validation runs. The choice of point 6 still depends on no
   campaign-4 data, since no campaign-4 run exists before stage M.
