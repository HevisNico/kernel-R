# Noise study, amendment 1: the campaign of point 3 is campaign 4

Fixed by the owner on 2026-11-15 and pushed alone on the branch `research/network-noise-study-amendment-1`,
**before the noise model is validated and before any preregistration of campaign 4** (the learned AND–OR circuit,
`research/learned-dnf-circuit/`). When this file is pushed, no run of campaign 4 has started and its `PREDICTION.md`
is not pushed. It changes nothing in points 1, 2 and 4 of [`COMMITMENT.md`](COMMITMENT.md).

1. **The validation of point 2 stays separate and comes first.** Its criteria are pushed alone, before any
   validation run. No campaign uses the model before it is validated.
2. **The preregistered campaign of point 3 is campaign 4**, on the learned AND–OR circuit, run under the validated
   model. It keeps every condition of point 3: new instances, 3 to 5 noisy runs per instance, and the per-port
   claims N-own and N-word. Its claims on the learned function are added to these.
3. **Campaign 4 also has a noise-free primary claim** on the learned function: the learned function and the 16
   read-only outputs, predicted exactly. This claim has its own verdict.
4. **The verdicts are separate**, and each is fixed in the preregistration. A failure of the learned-function
   claims does not change the verdicts of N-own and N-word; a failure of N-own or N-word does not change the
   verdicts on the learned function, with or without noise.
5. **The number of noisy runs per instance follows point 3.** It replaces the single noisy run per instance of
   `research/learned-dnf-circuit/DECISIONS.md`. The preregistration states the expected compute with 3 to 5 noisy
   runs per instance and the expected number of eligible instances. **If this exceeds 4 h**, the owner either
   accepts the longer budget or reduces the number of noisy runs per instance, and does so **before the
   preregistration** is pushed.
6. **If the model is not validated**, there is no campaign under it, and **the default is the simulator's built-in
   noise**. A corrected model is allowed only with an independent justification, and only **without looking at any
   campaign-4 data**. Whichever is chosen is pushed alone, before any preregistration of campaign 4.
