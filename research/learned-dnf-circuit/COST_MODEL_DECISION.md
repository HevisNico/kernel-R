# Campaign 4: the owner's cost-model decision

Fixed by the owner on 2026-11-16 and pushed alone on the branch `research/learned-dnf-circuit-cost-model-decision`,
**before any preregistration of campaign 4 and before any of its runs**: its `PREDICTION.md` is not pushed, and none
of its seeds has been simulated. It completes the owner's budget decision ([`BUDGET_DECISION.md`](BUDGET_DECISION.md),
commit `db4638b`), whose budget of up to 8 h is "measured with the cost model the preregistration states". This file
fixes that cost model.

1. **A measured cost model.** The expected compute of campaign 4 is computed from wall times **measured on the
   nominal cell**, on decks of three cells, four runs at a time, and not from the cost model of phase 0 (`dnf.cost`),
   which overstates the measured times by a factor of about 1.6 to 1.8 on decks of three cells
   (`research/network-noise-study/phase0/COST_C4_need4.json`).
2. **The measured times:**
   - a run without noise on the need-4 calendar: **814 s**
     (`research/network-noise-study/phase0/COST_C4_need4.json`, commit `4d3b5a1`);
   - a noisy run on the same calendar under the device noise model, as `filesource` sources: **1 033 s**
     (`research/network-noise-study/phase0/COST_C4_need4_sources.json`, commit `c2cb677`), to be replaced by the cost
     the noise study's validation report fixes for the validated model, cited by its commit;
   - a calibration deck, the untrained control run and an extraction: measured in the same conditions on the nominal
     cell, before the preregistration is pushed, and cited by commit.
3. **Scaling to an instance.** The measured time of a run kind is scaled to the calendar of each run by the ratio of
   `dnf.cost` for that calendar to `dnf.cost` for the measured calendar. Only the structure of `dnf.cost` is used, not
   its absolute values.
4. **Unchanged:** `R = 3`, up to 8 h of expected compute, `I` the largest instance count that fits, the kit's cap of
   14 400 s per stage, the time limits of 1.3 times the wall time measured in the rehearsal, and the rule that the
   rehearsal can only lower `I`, never raise it. The bound "never above 1.3 times the cost model" on the time limits
   now refers to this measured model.
5. **Why.** With the phase 0 model, 8 h of expected compute fits 5 instances, about 3 eligible, for about 4 to 5 h of
   real time. The measured model uses the 8 h the owner accepted as real time, for more instances. More instances
   give more chances to refute the claims, and the choice depends on no campaign-4 data. The cost of the choice is a
   tighter margin: a run that exceeds 1.3 times its measured time is missing.
