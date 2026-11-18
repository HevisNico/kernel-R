# Campaign 6 of the learned AND-OR circuit: the stopping rule

Pushed alone on `research/learned-dnf-circuit-campaign-6`, before any code of the development batch runs. It is the
owner's decision of 2026-11-18, and it is binding. The design note (`research/learned-dnf-circuit-campaign-6/drafts/DESIGN_NOTE.md`
at commit `659d3a2`, SHA-256 `e1803c1712795771430420136241e030ea8c8bbc1321c56388a4b17b6bc3a18d`) explains the
design. This file sets only the rule. When it was written, no seed from 7701 had been simulated.

## The batch

Exactly **10 development instances, seeds 7701 to 7710**. The batch is never extended, and no run of it is ever
repeated. **`k`** is the number of them that are eligible. A run that does not complete makes its instance not
eligible.

**`k` is computed by the batch's code exactly as pushed before any batch run**, named in the batch's report by its
commit and the SHA-256 of each of its files. That code is never changed after the first batch run. A defect found
afterwards is reported, and changes neither `k` nor the decision.

## The size

When `k >= 2`: **`I = ceil(30 / k)`** instances, so that 3 eligible instances are expected.

## The expected compute

`E`, in seconds, is that of a campaign of `I` instances, counted by campaign 5's rules (its `PREDICTION.md`, commit
`a2d8bad`, sections 10.3 to 10.5):

- **Measures**, on all `I` instances: each run of the batch's measures (scans and calibration decks), each at the
  mean wall time of its kind in the batch.
- **Network runs**, on `ceil(k x I / 10)` instances: per instance, one run without noise with the skew slots and three
  noisy runs, at need 4, plus one untrained control run for the campaign. Their expected costs are fixed now, since the
  batch runs no network:
  - **718 s** for the run without noise: the mean of campaign 5's rehearsal stage RQ, six runs at need 4 on development
    instance 7692;
  - **132 s** for the untrained run: the mean of RQ's two;
  - **1 400 s** for a noisy run. No noisy run on a mismatched cell was ever measured, so this cost is set on the
    conservative side: under the same load, mismatch slowed campaign 5's calibration decks by up to 734 / 485 = 1.51
    (RM's mismatched guard-on decks against RC's nominal ones) and its runs without noise by about 1.25. RC's nominal
    noisy run took about 925 s, and 925 x 734 / 485 = 1 400 s, above the cost model's 1 316 s.
- Each run's limit is `10 x ceil(2 x expected / 10)`. Instances in seed order, the first `ceil(I / 2)` on machine `a`.
  Stages are split as in campaign 5's section 10.5, within the kit's bound of 14 400 s.
- **`E` is the sum, over every stage and both machines, of `sum(expected) / 4 + 3/4 x max(expected)`.**

## The decision

**Campaign 6 is preregistered, with seeds from 7801, only if `k >= 2`, `I <= 40` and `E <= 28 800 s`.** Otherwise the
circuit campaigns stop, and the diagnostic (the batch's report, with the record of campaigns 4 and 5) is published as
the result.

The batch's report gives `k`, `I` and `E` with every input of this computation, and answers the design note's five
questions. It decides nothing beyond this rule.
