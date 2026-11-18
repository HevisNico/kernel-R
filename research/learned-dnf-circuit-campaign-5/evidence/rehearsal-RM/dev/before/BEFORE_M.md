# Campaign 5: the record before stage M

Written by `plan.py before-m` (the frozen code), pushed alone after the rehearsal's record and before the first launch
of M1 (PREDICTION.md, 10.8). Nothing in it is chosen by hand.

1. **The noise model**: injected (PREDICTION.md, section 6).
2. **The noise constants**: b = 0.111 mV between runs, w = 0.094 mV within a run, d = 0.009 mV per dose (decision 5).
3. **The costs**: {"calibration_deck_s": 925.0, "extraction_s": {"fire": 290.0, "hold": 100.0, "pulse": 95.0, "window": 260.0}, "isolation_per_instance_s": 40.0, "noisy_need4_s": {"device": 1033.0, "injected": 1316.0}, "quiet_need4_s": 814.0, "untrained_s": 369.2} (PREDICTION.md, 10.3).
4. **I = 0** (machine a: seeds [7691, 7692, 7693]; machine b: seeds []), expected compute 0.00 s = 0.0000 h; expected {}.
5. **The time limits**: a run's time limit is 10 x ceil(2 x expected / 10), its expected cost computed on its own calendar (PREDICTION.md, 10.4). At need 4: {"calibration_deck": 1850, "noisy": 2640, "quiet_with_skew": 1700, "untrained": 740} s; at need 7: {"calibration_deck": 1850, "noisy": 3340, "quiet_with_skew": 2130, "untrained": 740} s. The exact limits and caps of the stages of M, which depend on no need and are those their manifests hold: {}. The caps of Q and N1 to N3 at need 4, which the frozen code recomputes from the needs of PREDICTED.json (and splits by the rule of 10.5 if they exceed 14 400 s): {} s.
6. **The rehearsal's record**: `(the rehearsal itself)` at commit `-`, SHA-256 `-`, verdict: -.

```json before-m
{
 "I": 0,
 "constants": {
  "between_mV": 0.111,
  "per_dose_mV": 0.009,
  "within_mV": 0.094
 },
 "constants_source": "decision 5",
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
 "costs_source": "PREDICTION.md, 10.3",
 "expected": {},
 "expected_compute_h": 0.0,
 "expected_compute_s": 0.0,
 "limits": {
  "need4_s": {
   "calibration_deck": 1850,
   "noisy": 2640,
   "quiet_with_skew": 1700,
   "untrained": 740
  },
  "need7_s": {
   "calibration_deck": 1850,
   "noisy": 3340,
   "quiet_with_skew": 2130,
   "untrained": 740
  },
  "rule": "a run's time limit is 10 x ceil(2 x expected / 10), its expected cost computed on its own calendar (PREDICTION.md, 10.4)"
 },
 "machine_of": {
  "7691": "a",
  "7692": "a",
  "7693": "a"
 },
 "measure_stages": {},
 "network_stage_caps_need4_s": {},
 "noise_model": "injected",
 "noise_model_source": "PREDICTION.md, section 6",
 "rehearsal": {
  "commit": "-",
  "path": "(the rehearsal itself)",
  "sha256": "-",
  "verdict": "-"
 },
 "seeds": {
  "a": [
   7691,
   7692,
   7693
  ],
  "b": []
 },
 "what": "the rehearsal's record (dev), not the campaign's BEFORE_M.md"
}
```
