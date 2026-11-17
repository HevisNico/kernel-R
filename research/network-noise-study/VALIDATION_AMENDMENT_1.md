# Noise study: amendment 1 to the validation criteria

The owner's decisions on two points of [`VALIDATION_CRITERIA.md`](VALIDATION_CRITERIA.md) (5a24d10), pushed alone,
**before any noisy validation draw**. The extractions and V1 do not use noise seeds; V1 was run before this push.
Nothing else in the criteria changes.

1. **Noise seeds of the validation.** For 7101, 7102 and 7103: noise_seed = 1000 × instance seed + round, the
   rounds from 3 (7101003, 7101004, …). The nominal cell keeps noise_seed = 90000 + round.

   Why: the written rule, 10 × instance seed + round, makes two instances share a seed from round 10 on (7101
   round 13 = 71023 = 7102 round 3). The validation needs about 95 noisy runs per development instance. Two
   instances would then share the same noise realization, source by source, which would correlate the constants
   pooled over the three instances.

   Campaign 4's rule (10 × S + n, n = 1 to 3) is unaffected.

2. **The shot terms.** The two 2qI terms per cell (item 3 of section 1) are part of the model. They are in the
   draws, and their Σ S|H|², from the same AC as the device transfers, is added to the reference density of V3
   and V4.
