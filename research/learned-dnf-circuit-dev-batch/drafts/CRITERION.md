# The development batch after campaign 5: its stopping criterion

Pushed alone on `research/learned-dnf-circuit-dev-batch`, after the closure of campaign 5 (its `AMENDMENT_2.md`, on
`research/learned-dnf-circuit-campaign-5`) and before any code of the batch runs. It is the owner's decision of
2026-11-18. When it was written, no instance of the batch had been simulated. It cites only campaign 5's development
instances (seeds 7691 to 7693) and its rehearsal, which enter no claim.

## 1. What it decides

Whether a sixth campaign of the learned `(A and B) or (C and D)` circuit goes ahead, with which definition of the
measures and with how many instances; or whether the circuit campaigns stop and the diagnostic is published as the
result. The decision follows from the batch by the rules below, with nothing chosen after the batch.

## 2. The batch

- **n = 10 development instances, seeds 7701 to 7710**, each built as in campaign 5 (`net.deck`, model section
  `tt_mm`, 27 C, the junction areas of stage J, `setseed` with the seed). These seeds are disjoint from every seed
  used so far (campaigns 1 to 3, 7501 to 7512, 7601 to 7612, 7691 to 7693). On `main` at `8bcd3d7`, the numbers
  7701 to 7710 appear only as `noise_id` values of `research/circuit/repetition/manifest.json`, which are noise
  numbers and not mismatch seeds. The batch runs no noise. **The next campaign's seeds start at 7801.** The batch
  is never extended, and no deck of it is ever rerun.
- Each instance gets **campaign 5's two calibration decks (guard on, guard off), exactly as campaign 5 runs them**,
  and a **third deck, the trip deck**, on the same instance. The trip deck holds only **trip reads**: reads whose only
  purpose is to measure the level of `q` at which each cell's latch trips. A trip read that fires can change a cell's
  state, so no trip read is placed in the two calibration decks, and no read of the trip deck is ever classified.
- The trip deck covers, for each cell, every read kind of campaign 5's section 4.1 (port 1, port 2, both; for `c`,
  also the 0.3-late pair), with **at least 5 trip reads per cell and read kind**. Their rates of rise `dq/dt` at the
  crossing span **at least from half the smallest to twice the largest** `dq/dt` at the guard-on FIRE crossing among
  the firing reads of campaign 5's development instances (rehearsal stage RM, machine `a`). The batch's code computes
  that range from that evidence and writes it in its output before any deck of the batch runs. The design of the trip
  deck is fixed by the batch's code, which is committed and pushed before it runs.
- The pinned toolchain of campaign 5's section 10.2. Every output is pushed as it is. A deck that does not complete
  makes its instance not measured under both definitions.

## 3. The two definitions

- **D_nom**: campaign 5's `PREDICTION.md` (commit `a2d8bad`), sections 4.1 and 4.2, unchanged: the threshold
  `theta = 100 000` is the nominal FIRE level `q = 1`.
- **D_cell**: the same rules, except two things.
  1. Each read's score is expressed in units of its cell's estimated trip level: `Z = 100 000 x q_peak / q_trip`,
     where `q_trip` is the chosen estimator's value for that cell and read (section 4). `theta` stays 100 000. For
     E3, a classified read's `dq/dt` is taken from its guard-off trace where `q` first reaches the cell's E1 level, or
     at its peak of `q` if it never does. For the empty read, which no trip read matches, `q_trip` is the cell's E1
     level under every estimator.
  2. Every budget of section 4.2 (`beta_0`, `beta_3`) of a read is widened by the error bound `e` of its cell and read
     kind (section 4).

## 4. The trip estimator of D_cell, chosen on measurement quality only

The observed trip level of a trip read is `q` at its FIRE crossing in the trip deck. Three estimators are fitted, by
least squares, on the trip reads only:

- **E1, static**: one level per cell, `q_trip = q0`.
- **E2, same kind**: one level per cell and read kind, `q_trip = q0(kind)`.
- **E3, slope**: per cell, `q_trip = q0 + tau x dq/dt`, with `dq/dt` taken at the crossing.

A trip read's residual is **out of sample**: its observed level minus the value of the estimator fitted to the same
cell's trip reads **without that read** (leave-one-out), in integer units (`x 100 000`). For each estimator, `R` is the
largest absolute leave-one-out residual over every trip read of the batch. **The estimator chosen is the one
with the smallest `R`; on equal `R`, the simplest, in the order E1, E2, E3.** It is chosen before anything is classified
under D_cell, and the eligible rate never enters the choice.

The **error bound** `e` of a cell and read kind is the largest absolute leave-one-out residual of the chosen estimator
on that cell's trip reads of that kind, rounded up to the next integer unit. A cell with fewer than 5 trip reads of a
kind (a trip deck that did not complete included) makes its instance not measured under D_cell.

Under D_cell, a guard-on FIRE bit that disagrees with `Z >= theta` still makes the instance not measured (campaign 5,
section 4.1), **even when `|Z - theta| <= e`**. This is the conservative choice.

## 5. The rates

For each definition D: `j_D` instances measured and `k_D` eligible, of the 10, by campaign 5's sections 4.1 and 4.2
under D. **`p_D = k_D / 10`** and `m_D = j_D / 10`. `m_D` is reported and enters no rule.

## 6. The size and the expected compute

For each definition D with `k_D >= 2`:

- **`I_D = ceil(3 / p_D)`** instances.
- **`E_D`, the expected compute in seconds** of a campaign of `I_D` instances, by campaign 5's rules:
  - **Stage M**, on all `I_D` instances. Under D_nom: each instance's two calibration decks, each at the mean wall
    time of its kind (guard on, guard off) in campaign 5's rehearsal stage RM (both machines, 12 decks). Under D_cell:
    each instance's three decks (guard on, guard off, trip deck), each at the mean wall time of its kind in this batch.
  - **Network runs**, on `ceil(p_D x I_D)` instances only: one run without noise at need 4 with the skew slots and
    three noisy runs at need 4 each, plus **one untrained control run**. Expected costs are the mean wall times, over
    both machines, of campaign 5's rehearsal: RQ's runs without noise at need 4, RN's noisy runs, RQ's untrained run.
    A duration measured at another calendar is scaled to need 4 by the ratio of `dnf.cost` (campaign 5, section 10.3).
  - Instances in seed order, the first `ceil(I_D / 2)` on machine `a` and the rest on `b`. Each run's limit is
    `10 x ceil(2 x expected / 10)` and its kit cap that limit plus 10 s. Stages are split by campaign 5's rule of section
    10.5: each machine's runs, in seed order, in the fewest consecutive parts such that each pair of `j`-th parts fits
    the kit's bound (`sum(caps) / 4 + max(caps)` per machine, summed over both machines, at most 14 400 s).
  - `E_D` is the sum over every stage and both machines of `sum(expected) / 4 + 3/4 x max(expected)` (campaign 5,
    section 10.3).

## 7. The decision

1. **A definition D is considered only if `k_D >= 2`**, so that no campaign rests on one eligible development
   instance. It **passes** if also `I_D <= 40` and `E_D <= 28 800 s`.
2. **D\*** is the passing definition with the smaller `E_D`; on equal `E_D`, D_nom.
3. **A sixth campaign goes ahead only if a definition passes.** If neither does (in particular if neither has
   `k_D >= 2`), the circuit campaigns stop, and the diagnostic (campaign 5's development data, this batch, the rates and
   this computation) is published as the result.
4. For information only, deciding nothing: the number of kit stages that D\*'s campaign would need, and an indicative
   wall time under a stated CI duration per stage.

## 8. What a sixth campaign must then do

- Use D\* exactly, and, if D\* is D_cell, the chosen estimator with its error bounds.
- Use `I = I_D*` instances, seeds from 7801.
- Run the network only on the eligible instances. A measured but not eligible instance gets no network run and enters
  no claim.
- State its scope: the noise claims (N-own, N-word) and the M2 comparisons hold on eligible instances only. These are
  selected by clearing the budgets, from per-cell measures alone and before any network run, so they may be more
  robust to noise than mismatched cells in general. The claims are not claims about mismatched cells at large.
- State that the per-cell normalisation was motivated by campaign 5's development seeds, which enter no claim, and
  justify it by circuit physics: under mismatch, each cell's latch trips at its own level of `q`.
- The batch's seeds 7701 to 7710 never enter a claim.

## 9. What was known when this was written

From campaign 5's development instances (rehearsal stage RM, machine `a`, its development `PREDICTED.json`, commit
`f59f6f8`):

- 1 of 3 instances was measured;
- the measured one (7692) was not eligible;
- every disagreement between a guard-on FIRE bit and `Z >= theta` was a read whose `Z` lay between the nominal level
  and its cell's own trip level;
- the trip levels, estimated from the guard-on decks' reads, spread about plus or minus 2 % across cells (from 0.981 to
  1.022 of the nominal level), and by up to about 0.4 % within the cell `c`;
- the guard-on and guard-off decks agreed within 0.15 % on every read that did not fire.

No instance of this batch, and no seed from 7701, had been simulated.
