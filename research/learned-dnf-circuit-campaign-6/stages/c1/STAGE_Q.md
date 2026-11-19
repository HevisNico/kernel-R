# Campaign 6: the protocol of stage Q, attempt c1

Written by `stages6.py stage-file` and pushed alone before the stage's source commit. It is the launch
kit's protocol file of this stage (the manifest's `protocol_path`), so each stage has its own claim.
Its governing protocol is
`research/learned-dnf-circuit-campaign-6/PREDICTION.md` at commit `df1a3cbcf73ed0ad71e04ded987f756a466e3902`, SHA-256 `8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240`; every runner of
the stage refuses its run if that file has another SHA-256 in the repository (c6.stage_check).

```json stage
{
 "attempt": "c1",
 "governing_protocol": {
  "commit": "df1a3cbcf73ed0ad71e04ded987f756a466e3902",
  "path": "research/learned-dnf-circuit-campaign-6/PREDICTION.md",
  "sha256": "8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240"
 },
 "stage": "Q"
}
```
