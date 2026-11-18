# Campaign 5: the protocol of stage RQ

Written by `plan.py stage-file` (the frozen code) and pushed alone before the stage's launch (PREDICTION.md,
10.6). Its governing protocol is `research/learned-dnf-circuit-campaign-5/PREDICTED.json` at commit `f59f6f8d11cca80776a3fe2dfd062b2123e32d60`, SHA-256 `28ffbd138b43f84761a5d0ead6fd9448f4918465ee7d5cf63ffe499e2ae5c3be`;
`run4.py` refuses every run of the stage if that file has another SHA-256 in the repository.

```json stage
{
 "governing_protocol": {
  "commit": "f59f6f8d11cca80776a3fe2dfd062b2123e32d60",
  "path": "research/learned-dnf-circuit-campaign-5/PREDICTED.json",
  "sha256": "28ffbd138b43f84761a5d0ead6fd9448f4918465ee7d5cf63ffe499e2ae5c3be"
 },
 "stage": "RQ"
}
```
