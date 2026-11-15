# Campaign 3 of the periodic ring: commitment

Fixed by the owner on 2026-11-15 and pushed alone on the branch `research/network-circuit-ring-campaign-3-commitment`,
**after the measure stage of campaign 2 and before its network runs**: when this file is pushed, no attempt marker
of the network runs of campaign 2 exists and none of its network runs has started. It rests on the measures of
campaign 2 only, through
[`../network-circuit-ring-campaign/LESSONS_FROM_THE_MEASURES.md`](../network-circuit-ring-campaign/LESSONS_FROM_THE_MEASURES.md)
(commit `453966e`) and
[`../network-circuit-ring-campaign/CAMPAIGN_3_DECISIONS.md`](../network-circuit-ring-campaign/CAMPAIGN_3_DECISIONS.md)
(commit `49c5d96`). It changes nothing in campaign 2, whose `PREDICTION.md` is not edited.

## 1. Campaign 3 runs whatever campaign 2 gives

Whether the claims of campaign 2 hold, fail or are not established, campaign 3 is run. It starts after campaign 2
has ended and been analyzed and reported as it is.

## 2. Instances

Twelve new instances, seeds **7401 to 7412**, never simulated and none reused (none of 7101 to 7103, 7201 to 7206,
7301 to 7306).

## 3. The protocol

The protocol of campaign 2
([`../network-circuit-ring-campaign/PREDICTION.md`](../network-circuit-ring-campaign/PREDICTION.md), commit
`7ae9710`, SHA-256 `cc16b94e6aa4eca8f065724db3d7a32a3640c90e4eaaf4c73fe250e9ea6208e7`), with exactly these
corrections from `LESSONS_FROM_THE_MEASURES.md`, and no other:

1. **Scan time limit 640 s.**
2. **A robust scan.** After the first FIRE, two more isolated reads at one and at two further doses, so that every
   port has at least three fired states. A change to `../network-circuit/phase1/cellscan.py`, rehearsed on the
   nominal cell before the implementation is frozen.
3. **Contradictory states** (the case of 7206 in campaign 1: a state that fired is not stronger than a state that
   stayed silent): the isolated reads at the two disputed states are repeated, and the majority is taken.
4. **Size:** one run without noise and one shortened noisy run (three laps after the predicted freeze) per measured
   instance; one control run.

Everything else is unchanged: N = 3; the ring and its calendars; both budgets; the fixed noise constants (0.090,
0.064 and 0.009 mV, for the noisy budget only); the predictor; N-own and N-word, with the same exclusions reported;
the rule of the control instance; the analysis; the launch kit, one launch per machine per stage. **Any further
change only by an amendment pushed before the preregistration of campaign 3.**

## 4. Budget

4 h of expected machine time on two machines, counted as in campaign 2 (each stage on each machine: the sum of the
expected times divided by four, plus three quarters of the largest).

The figures, with the scan of campaign 2 (313 s on average, 495 s for a train) and the cost model of phase 0 for
the network runs (needs of 4.3 on average), before the two extra reads of the robust scan:

- expected: **229 minutes** if 9 of the 12 instances are measured (the rate of campaigns 1 and 2 together);
  **260 minutes**, above 4 h, if all 12 are measured. The two extra reads per scan add about 45 s to a scan, about
  9 minutes in all at four runs at a time;
- **the kit's worst case**, every run taking its whole limit, at five doses per port: 5 750 s per machine for the
  measures (scans 640 s, trains 730 s) and 7 280 s and 6 885 s for the network runs (runs without noise 1 730 s,
  shortened noisy runs 1 680 s, control 1 570 s): **25 665 s in all**, 7.1 h. The network manifest stays under the
  14 400 s that the kit allows one manifest (14 165 s); above it, the rule of campaign 2 removes the last noisy
  runs.

## 5. Reporting

Each campaign is reported separately, with its own verdicts. Pooled figures are sums of counts only. **A pooled
claim holds only if it holds in each campaign; one failure in either refutes it.**

## 6. The last campaign

Campaign 3 is the last campaign of this series for this claim.
