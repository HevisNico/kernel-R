# K03 local archive lot (combined campaign stop, 2026-11-28)

Files that existed only on machine K03 and are not regenerable, copied unchanged (`cp -p`) on 2026-11-28.
Nothing at the source was changed, moved or deleted. Approved by the owner through the campaign coordinator
(session_01TzF7ZUoTUj44AGYGuEFzHA, "ok pr les petits lots locaux").

## Provenance

- Machine: K03 (cloud container; session session_01TzF7ZUPRcc3ZzvdVDiqphM).
- Every path below is relative to this folder: `<source dir name>/...`, where `<source dir name>` is the folder under `$HOME` on K03.

| Source dir on K03 | Run | Related published branch and tip | Files here |
|---|---|---|---|
| `~/yieldK03/out` | Yield lot, stage D only (YIELD_LOT_RULE_2, code at research/layered-stage-d 70a0f66b): ANDOR3 6106, 6143; NOT1 6217; XOR3 6159, 6182. Completed (ENDED DONE). Dev seeds, they count for nothing. | `evidence/yield-lot-K03` = 8c535fe4a291987fb9980f81dcf725fd21dcc305 | 26 |
| `~/devtest_b_discarded_a8303e8e/out_K03` | Equivalence test (b), run 1, at a8303e8e (ANDOR3 6104 with room, plus U). **DISCARDED**: stopped by SIGTERM on the coordinator's order at 2026-11-26T22:16:07Z (see SIGNALS.json), with N1–N3 interrupted. TEST mode; counts for nothing. | only its seal: `evidence/devtest-seals-K03` = 248189347319bf6a6d1e88ecfad09633939b0449 (the replacing run 2 is `evidence/devtest-run2-K03` = a08d88d) | 80 |

## Items and why they were never published

- **Yield lot**, the 26 files not on `evidence/yield-lot-K03`. They are raw records of a completed run.
  - The yield-lot runbook's copy rule (step 10) published only `*.json`, `SHA256SUMS`, `INVENTORY_*`, `DONE` and `*.log`. It excluded `session.log` and anything under `runs/`.
  - A later addition published every file listed in some SHA256SUMS. None of these 26 is listed in any SHA256SUMS.
  - The files:
    - `<instance>/D/session.log`: ngspice's whole pipe output of the stage-D session, one per instance and unique.
    - `<instance>/deck.spice`, `<instance>/D/input.spice`, `<instance>/D/blocks.spice`, `<instance>/D/.spiceinit`: the inputs the logs came from, kept beside them.
    - `DRIVER_PID`.
- **Devtest (b) run 1**: the whole output, except the exclusions below.
  - It is a DISCARDED partial run.
  - Its runbook pushes the root only at step 6, which was never reached because the run was stopped and discarded.
  - Only campaign.py's own seal push reached GitHub.

## Excluded (not archived)

- **Lean `.olean` build products** (39 files): `*/inv/lean_build/*.olean` (yield lot) and `kernel_build/*.olean` (run 1). These are regenerable: the campaign driver rebuilds them from the pinned Lean sources with Lean 4.35.0.
- **`pdk` symlinks** (6, run 1). Each points to /home/user/kernel-R/research/circuit/pdk, the SKY130 PDK at 1232782c, which is regenerable with research/circuit/fetch_pdk.sh.
- **Run 1's `.seal_log_work/.git`** (31 files). This is git metadata of the seal-log working repository, and its reflogs contain the committer e-mail. Its only content, the seal commit 24818934, is already on `evidence/devtest-seals-K03`.

Every excluded file is listed below as path, size and sha256. For a symlink, the size column holds the link target and the sha256 is that of the target string. All are marked "regenerable, not archived", or "git metadata, content published" for the 31 metadata files.

```
yieldK03/out/NOT1_6217/inv/lean_build/CircuitInverterGate.olean 274296 d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/InverterInstanceTiming.olean 137424 f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/InverterTarget.olean 124416 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/MonotoneOneSidedTarget.olean 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/MonotoneSupport.olean 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/MonotoneTarget.olean 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/Target.olean 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/TwoLayerTarget.olean 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267  regenerable, not archived
yieldK03/out/NOT1_6217/inv/lean_build/TwoRailsTarget.olean 48208 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/CircuitInverterGate.olean 274296 d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/InverterInstanceTiming.olean 137424 f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/InverterTarget.olean 124416 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/MonotoneOneSidedTarget.olean 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/MonotoneSupport.olean 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/MonotoneTarget.olean 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/Target.olean 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/TwoLayerTarget.olean 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267  regenerable, not archived
yieldK03/out/XOR3_6159/inv/lean_build/TwoRailsTarget.olean 48208 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/CircuitInverterGate.olean 274296 d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/InverterInstanceTiming.olean 137424 f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/InverterTarget.olean 124416 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/MonotoneOneSidedTarget.olean 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/MonotoneSupport.olean 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/MonotoneTarget.olean 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/Target.olean 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/TwoLayerTarget.olean 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267  regenerable, not archived
yieldK03/out/XOR3_6182/inv/lean_build/TwoRailsTarget.olean 48208 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/COMMIT_EDITMSG 17 f8c375b95a32ba9c58267d427a914117565ccc17122fae5ced925ec717fc7f27  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/HEAD 43 1a647c089e85f6cff92f7586569d77b0e66141bb5473f7027eff4f303bd323fa  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/config 92 cfe7ba1238c9a78be7535d7c63bcaf5a4d5011d46b07c9b45d3bbf7d6c312dfe  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/description 73 85ab6c163d43a17ea9cf7788308bca1466f1b0a8d1cc92e26e9bf63da4062aee  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/applypatch-msg.sample 478 0223497a0b8b033aa58a3a521b8629869386cf7ab0e2f101963d328aa62193f7  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/commit-msg.sample 896 1f74d5e9292979b573ebd59741d46cb93ff391acdd083d340b94370753d92437  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/fsmonitor-watchman.sample 4726 e0549964e93897b519bd8e333c037e51fff0f88ba13e086a331592bf801fa1d0  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/post-update.sample 189 81765af2daef323061dcbc5e61fc16481cb74b3bac9ad8a174b186523586f6c5  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/pre-applypatch.sample 424 e15c5b469ea3e0a695bea6f2c82bcf8e62821074939ddd85b77e0007ff165475  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/pre-commit.sample 1643 f9af7d95eb1231ecf2eba9770fedfa8d4797a12b02d7240e98d568201251244a  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/pre-merge-commit.sample 416 d3825a70337940ebbd0a5c072984e13245920cdf8898bd225c8d27a6dfc9cb53  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/pre-push.sample 1374 ecce9c7e04d3f5dd9d8ada81753dd1d549a9634b26770042b58dda00217d086a  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/pre-rebase.sample 4898 4febce867790052338076f4e66cc47efb14879d18097d1d61c8261859eaaa7b3  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/pre-receive.sample 544 a4c3d2b9c7bb3fd8d1441c31bd4ee71a595d66b44fcf49ddb310252320169989  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/prepare-commit-msg.sample 1492 e9ddcaa4189fddd25ed97fc8c789eca7b6ca16390b2392ae3276f0c8e1aa4619  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/push-to-checkout.sample 2783 a53d0741798b287c6dd7afa64aee473f305e65d3f49463bb9d7408ec3b12bf5f  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/sendemail-validate.sample 2308 44ebfc923dc5466bc009602f0ecf067b9c65459abfe8868ddc49b78e6ced7a92  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/hooks/update.sample 3650 8d5f2fa83e103cf08b57eaa67521df9194f45cbdbcb37da52ad586097a14d106  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/index 499 f2898cf6aff33330995b0181163d1dd02e933ba1563555ac923d0ef363dba05c  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/info/exclude 240 6671fe83b7a07c8932ee89164d1f2793b2318058eb8b98dc5c06ee0a5a3b0ec1  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/logs/HEAD 183 55f5976570655ec46715cb52e6c414ac4d83fb868e8cca3343afe8bec4491c00  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/logs/refs/heads/evidence/devtest-seals-K03 183 55f5976570655ec46715cb52e6c414ac4d83fb868e8cca3343afe8bec4491c00  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/24/8189347319bf6a6d1e88ecfad09633939b0449 365 58f24ed5cfc4d9579cac21c1b41aacebd56ef8752a09fd1f2d5360196c104dc2  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/57/1bc809cb032f4e89ffa4147728126a0ad04c34 86 a63af8dabf757fd05770fb38f0fd61e8fbb51413d43c86b4a71022f9b7d42210  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/64/7ae13a121dbaefc7f4c4c3b8ddd7a8accff27b 105 11c539c90b6ad0b45df365ad9c54f8a4edd506a50b2712bed6941e697e131edb  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/68/2d4d73f1caafd4595071298763bbe05c2524d6 2937 4886e686ea0eb45ec1f8d176d21c3393ce724f4e923aaa9585543f2b9c77cc78  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/68/3c4aebc19c31bc0677e75133871b48947d8065 143 38f4632737d79ed643a2be8a8add8d77b1edad54f7df481a6778f2a9f972edee  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/82/8706354a39dd756642ee069542f1f0b5683e78 130 5a6ff7f49d59850d0af9d95b9f0328ff28ab5275690f55a27c1c8fdd581c3fad  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/ac/48759edc5ed20ac25bc59e36ed820d3d3cb336 233 365b06c0106b3acc8b32f39efb9982bc36caf9779d5ae553ce493db62d01aaea  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/objects/fb/34db6e2d0affc17f389fc741b3c97ac749716b 53 04c8d0f68e1e267bb33e01fcb09facd00d7c3e9315c9b1ee9333a703915a0209  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/.seal_log_work/.git/refs/heads/evidence/devtest-seals-K03 41 6c539fa027bbbdda215fb7e4f75b0cdfa0f32fc0b75fa6a44bab045fd0085a5a  git metadata, content published
devtest_b_discarded_a8303e8e/out_K03/ANDOR3_6104/D/pdk symlink->/home/user/kernel-R/research/circuit/pdk 3c8168af63e189c98425466df49e7798f0f468d981014ca7f79ace0ddbe5cdb3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/ANDOR3_6104/N0/pdk symlink->/home/user/kernel-R/research/circuit/pdk 3c8168af63e189c98425466df49e7798f0f468d981014ca7f79ace0ddbe5cdb3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/ANDOR3_6104/N1/pdk symlink->/home/user/kernel-R/research/circuit/pdk 3c8168af63e189c98425466df49e7798f0f468d981014ca7f79ace0ddbe5cdb3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/ANDOR3_6104/N2/pdk symlink->/home/user/kernel-R/research/circuit/pdk 3c8168af63e189c98425466df49e7798f0f468d981014ca7f79ace0ddbe5cdb3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/ANDOR3_6104/N3/pdk symlink->/home/user/kernel-R/research/circuit/pdk 3c8168af63e189c98425466df49e7798f0f468d981014ca7f79ace0ddbe5cdb3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/U_ANDOR3_6104/U/pdk symlink->/home/user/kernel-R/research/circuit/pdk 3c8168af63e189c98425466df49e7798f0f468d981014ca7f79ace0ddbe5cdb3  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/LayeredMonotoneCheckerProofs.olean 1017584 62fb815218748d771a046a11f74eb9924434df467c1927adaa6c124e2f1e05bd  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/LayeredMonotoneCheckerTargets.olean 481664 8e3c93d0fb2bba83a7906e7435e98b0151505fe2bda5d5f8f9c093b979f3c9fb  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/LayeredMonotoneTarget.olean 749848 3406d3f64766a16920aaa15c98efd92b763f9ebdbc695ba2c7a161509b644064  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotoneOneSidedTarget.olean 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotonePremiseCompleteness.olean 408040 b5cf3330546b6ef31776c905bd5dfc9cce95ad270d5cfa3036a71a20e114efcf  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotonePremiseCompletenessTargets.olean 11000 51fe8f393314b08d208c428ae8552f3385629ea36cb9b4569dcad5235fd8bf69  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotonePremiseSoundness.olean 476376 a6676498d337cd21d0242bc64719ca9237f90f041dc36dc55390de487f91ff88  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotonePremiseTargets.olean 753640 ee8b52fd699c717d6ee3f45156f0d5184ad239bebe0c201e27d579fa31e2fe17  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotoneSupport.olean 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/MonotoneTarget.olean 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/Target.olean 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72  regenerable, not archived
devtest_b_discarded_a8303e8e/out_K03/kernel_build/TwoLayerTarget.olean 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267  regenerable, not archived
```

## How to recover

- Fetch the branch by name, then check the files:
  ```
  git fetch https://github.com/HevisNico/kernel-R refs/heads/archive/combined-campaign-stop/K03-local
  git checkout FETCH_HEAD
  cd archive/combined-campaign-stop/K03-local
  sha256sum -c SHA256SUMS
  ```
- To rebuild a full run folder:
  1. Copy `<source dir name>/...` back under `$HOME`.
  2. Overlay the published files of the related evidence/ branch above.
  3. Rebuild the excluded `.olean` files and pdk links as described in the previous section.
- No file here is split: all are under 50,000,000 bytes, so there are no `.transport-part-NNN` files.
- SHA256SUMS covers every file in this folder except itself.
