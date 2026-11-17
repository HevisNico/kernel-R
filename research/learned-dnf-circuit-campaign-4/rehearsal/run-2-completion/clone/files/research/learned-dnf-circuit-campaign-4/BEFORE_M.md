# Campaign 4: the record before stage M

Written by `plan.py before-m` (the frozen code), pushed alone before the first launch of stage M
(PREDICTION.md, The record before stage M). Nothing in it is chosen by hand: it follows from the decisions file
below, which cites its sources.

1. **The noise model applied**: device (rehearsal: the device model, before the validation's verdict).
2. **The noise constants**: b = 0.111 mV between runs, w = 0.094 mV within a run, d = 0.009 mV per dose (decision 5 (the rehearsal has no validated value)).
3. **The costs**: {"calibration_deck_s": 925.0, "extraction_s": {"fire": 290.0, "hold": 100.0, "pulse": 95.0, "window": 260.0}, "isolation_per_instance_s": 40.0, "noisy_need4_s": {"device": 1033.0, "injected": 1316.0}, "quiet_need4_s": 814.0, "untrained_s": 369.2} (the cost model of PREDICTION.md).
4. **I = 1** (machine a: seeds [None]; machine b: seeds []), expected compute 7.55 h, stage caps {"E1": 10658, "M": 7881, "N1": 5412, "N2": 5412, "N3": 5412, "Q": 4558} s; expected {"eligible": 5.4, "measured": 8, "noisy_runs": 24}.
5. **The reuse of the trip value**: True (rehearsal: the trip value reused (amendment 5, section 5)).

```json before-m
{
 "I": 1,
 "constants": {
  "between_mV": 0.111,
  "per_dose_mV": 0.009,
  "within_mV": 0.094
 },
 "constants_source": "decision 5 (the rehearsal has no validated value)",
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
 "costs_source": "the cost model of PREDICTION.md",
 "expected": {
  "eligible": 5.4,
  "measured": 8,
  "noisy_runs": 24
 },
 "expected_compute_h": 7.545111663244808,
 "machine_of": {
  "None": "a"
 },
 "noise_model": "device",
 "noise_model_source": "rehearsal: the device model, before the validation's verdict",
 "rehearsal": "the nominal cell only; not the campaign's BEFORE_M.md",
 "reuse_trip": true,
 "reuse_trip_source": "rehearsal: the trip value reused (amendment 5, section 5)",
 "seeds": {
  "a": [
   null
  ],
  "b": []
 },
 "stage_caps_s": {
  "E1": 10658,
  "M": 7881,
  "N1": 5412,
  "N2": 5412,
  "N3": 5412,
  "Q": 4558
 },
 "what": "the record before stage M of campaign 4 (PREDICTION.md, The record before stage M), written by plan.py"
}
```
