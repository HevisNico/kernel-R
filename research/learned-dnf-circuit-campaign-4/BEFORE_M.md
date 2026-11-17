# Campaign 4: the record before stage M

Written by `plan.py before-m` (the frozen code), pushed alone before the first launch of stage M
(PREDICTION.md, The record before stage M). Nothing in it is chosen by hand: it follows from the decisions file
below, which cites its sources.

1. **The noise model applied**: injected (the injected default (PREDICTION.md, Noise model, second item): the device model is not validated (research/network-noise-study/validation/REPORT_A2.md, commit fd25955, under the criteria with amendments 1 to 4), and the owner chose the injected default by amendment 7 (commit 53d50f3); amendment 9 (commit 184b595) states the rehearsal's zero-amplitude failure does not apply to it).
2. **The noise constants**: b = 0.111 mV between runs, w = 0.094 mV within a run, d = 0.009 mV per dose (decision 5, as PREDICTION.md (Noisy budget) sets them under the injected default (amendment 7, section 2, item 1)).
3. **The costs**: {"calibration_deck_s": 925.0, "extraction_s": {"fire": 290.0, "hold": 100.0, "pulse": 95.0, "window": 260.0}, "isolation_per_instance_s": 40.0, "noisy_need4_s": {"device": 1033.0, "injected": 1316.0}, "quiet_need4_s": 814.0, "untrained_s": 369.2} (the cost model of PREDICTION.md (Execution), with the noisy run at the measured 1 316 s of the injected model on the need-4 calendar (research/network-noise-study/phase0/COST_C4_need4.json, commit 4d3b5a1) and no extraction (PREDICTION.md, The record before stage M, item 3); the rehearsal's time limits (REHEARSAL.json, commit 9d96744) enter each stage's runs).
4. **I = 12** (machine a: seeds [7501, 7502, 7503, 7504, 7505, 7506]; machine b: seeds [7507, 7508, 7509, 7510, 7511, 7512]), expected compute 7.61 h, stage caps {"M": 9700, "N1": 8174, "N2": 8174, "N3": 8174, "Q": 5390} s; expected {"eligible": 7.2, "measured": 11, "noisy_runs": 33}.
5. **The reuse of the trip value**: False (not applicable: no extraction under the injected default (PREDICTION.md, Noise model; amendment 7, section 2, item 2)).

```json before-m
{
 "I": 12,
 "constants": {
  "between_mV": 0.111,
  "per_dose_mV": 0.009,
  "within_mV": 0.094
 },
 "constants_source": "decision 5, as PREDICTION.md (Noisy budget) sets them under the injected default (amendment 7, section 2, item 1)",
 "costs": {
  "calibration_deck_s": 925.0,
  "extraction_s": {
   "fire": 290.0,
   "hold": 100.0,
   "pulse": 95.0,
   "window": 260.0
  },
  "isolation_per_instance_s": 40.0,
  "noisy_need4_s": {
   "device": 1033.0,
   "injected": 1316.0
  },
  "quiet_need4_s": 814.0,
  "untrained_s": 369.2
 },
 "costs_source": "the cost model of PREDICTION.md (Execution), with the noisy run at the measured 1 316 s of the injected model on the need-4 calendar (research/network-noise-study/phase0/COST_C4_need4.json, commit 4d3b5a1) and no extraction (PREDICTION.md, The record before stage M, item 3); the rehearsal's time limits (REHEARSAL.json, commit 9d96744) enter each stage's runs",
 "expected": {
  "eligible": 7.2,
  "measured": 11,
  "noisy_runs": 33
 },
 "expected_compute_h": 7.611496702194091,
 "noise_model": "injected",
 "noise_model_source": "the injected default (PREDICTION.md, Noise model, second item): the device model is not validated (research/network-noise-study/validation/REPORT_A2.md, commit fd25955, under the criteria with amendments 1 to 4), and the owner chose the injected default by amendment 7 (commit 53d50f3); amendment 9 (commit 184b595) states the rehearsal's zero-amplitude failure does not apply to it",
 "reuse_trip": false,
 "reuse_trip_source": "not applicable: no extraction under the injected default (PREDICTION.md, Noise model; amendment 7, section 2, item 2)",
 "seeds": {
  "a": [
   7501,
   7502,
   7503,
   7504,
   7505,
   7506
  ],
  "b": [
   7507,
   7508,
   7509,
   7510,
   7511,
   7512
  ]
 },
 "stage_caps_s": {
  "M": 9700,
  "N1": 8174,
  "N2": 8174,
  "N3": 8174,
  "Q": 5390
 },
 "what": "the record before stage M of campaign 4 (PREDICTION.md, The record before stage M), written by plan.py"
}
```
