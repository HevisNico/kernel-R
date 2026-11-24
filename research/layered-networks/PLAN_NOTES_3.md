# Notes for PREDICTION.md after DECISIONS_3.md (the either cell's one-port testError)

**Draft, nothing frozen.** CAMPAIGN_PLAN_DRAFT.md is pushed and is not modified. These notes amend it for the
writing of PREDICTION.md (plan step 4). Owner's conditions 3a and 3b, relayed on 2026-11-24.

## The rule for the claims

- The either cell's testError is the **one-port rule**: the larger of its two lines' one-port read budgets at [n_p],
  plus H + H_drift + H_D4. This is campaign (a)'s family rule for c.
- It is implemented by `fit3.rule("one-port")`.
- Eligibility at K0, room at K3, the predictions and the "established" counts of plan §4 all use this rule.
- It supersedes the max rule (DECISIONS_3.md). It was adopted after the development failures were seen (9802, 9803)
  and before the freeze.

## (a) A declared comparison that counts for nothing: room under the max rule

- **What is reported**, per group and level, beside the claim counts:
  - the number of instances that would have room at K3 under the superseded max rule (`fit3.rule("max")`, fit.py as
    pushed);
  - the number of instances eligible at K0 under it.
- **How it is computed.** From the same stage-D records, by the frozen analysis script, after the campaign. It needs no
  simulation.
- **It decides nothing.**
  - It is not a prediction. It neither makes nor removes a counted instance, and it refutes nothing.
  - Its only use is to show how many K3 claims depend on the rule change: the instances with room under the one-port
    rule and not under the max rule.
- The noisy runs of those instances are still counted under the one-port rule like any other, and are listed
  separately in the report.

## (b) An expectation stated in advance

- **If a noisy (K3) run refutes**, the first suspect is the either cell's two-port read.
  - The one-port rule no longer budgets the both-lines score Z₍₁,₂₎. A noisy two-port read below θ would make the
    either cell silent on a pattern with both inputs present.
  - The read calibration's monotonicity (`FiringSlot`: scoreAt y ≤ scoreAt input) would then fail, and the observed
    output would differ from the prediction.
- **The report checks it first.** For every refuting difference it states:
  - whether the differing cell is an either cell;
  - whether the differing pattern presents both of its inputs;
  - whether the instance is one with room under the one-port rule and not under the max rule (the comparison of (a)).
- **This expectation is a diagnostic, not a claim.** It changes no verdict: a refutation refutes, whatever its cause.

## Stated with the change

- The one-port rule makes the test riskier:
  - more instances get a noisy prediction (room at K3);
  - each of them has a thinner margin, because the both-lines term no longer stands between the two-port read and the
    threshold.
- The expected K3 counts of plan §3 rise from about 10 to about 16 for ANDOR3 and for XOR3 [G, K3_EITHER_ANALYSIS.md].
  - The K3 threshold for "established" (≥ 5 counted) is unchanged.
  - The rehearsal fixes the sizes, as before (plan §7).
