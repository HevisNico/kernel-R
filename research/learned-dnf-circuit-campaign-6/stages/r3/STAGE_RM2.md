# Campaign 6: the protocol of stage RM2, attempt r3

Written by `stages6.py stage-file` and pushed alone before the stage's source commit. It is the launch
kit's protocol file of this stage (the manifest's `protocol_path`), so each stage has its own claim.
Its governing protocol is
`research/learned-dnf-circuit-campaign-6/PREDICTION.md` at commit `df1a3cbcf73ed0ad71e04ded987f756a466e3902`, SHA-256 `8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240`; every runner of
the stage refuses its run if that file has another SHA-256 in the repository (c6.stage_check).

```json stage
{
 "attempt": "r3",
 "governing_amendment": {
  "commit": "a0d4ad3cfd4ab5b669070c499385c2f5fdd06110",
  "path": "research/learned-dnf-circuit-campaign-6/PREDICTION_AMENDMENT_1.md",
  "sha256": "14a5379e8ec78fea5d137cecfbb3614b439fa227e5939c7653d6be518ddc9554"
 },
 "governing_protocol": {
  "commit": "df1a3cbcf73ed0ad71e04ded987f756a466e3902",
  "path": "research/learned-dnf-circuit-campaign-6/PREDICTION.md",
  "sha256": "8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240"
 },
 "stage": "RM2"
}
```
