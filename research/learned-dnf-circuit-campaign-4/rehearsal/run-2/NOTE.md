# Campaign 4, the rehearsal: attempt 2 (runs complete, record not yet written)

The rehearsal of the frozen implementation on the nominal cell only. It ran on commit `3156ee4` (tree `c19e4ef`),
from a clean clone at that commit (`/home/user/frozen-3156ee4`), in the work folder `/home/user/rehearsal2`,
detached from the director's session (`meta/run.sh`, `meta/uptime.sh`). Attempt 1 was interrupted
(`../run-1-interrupted/NOTE.md`).

## What happened

- Started 2026-11-17 at 05:48:47 UTC. Every stage of runs completed and was collected through the kit, on both machines
  (times of collection in `meta/uptime.log`): M 05:58:47 and 06:14:48; X 06:17:18 and 07:29:19; E 07:40:20 and
  07:51:50; N 08:06:51 and 08:17:51; MEMD and MEMI 08:35:23 to 08:58:56; GUARD 08:58:56.
- At 09:01:26 UTC `rehearsal.py` stopped with exit 1, in its last step: `check.sh` on the analysis's `M8.lean`
  refused `theorem no_eligible_instance : True := trivial`, which depends on no axiom, while `check.sh` required
  every theorem to depend on exactly `[propext, Classical.choice, Quot.sound]` (`meta/rehearsal.log`). The nominal
  cell is not eligible, so the analysis wrote that placeholder.
- **`REHEARSAL.json` was not written, and no check of the record was evaluated or looked at.** The analysis had written
  `analysis/RESULTS.json` and `analysis/M8.lean` before the failure; they are kept as they are.
- The owner decided to complete this attempt, not redo it (campaign-4 amendment 8).

## Checked before the completion (2026-11-17, by the campaign director)

- `uptime -s` read `2026-11-17 05:34:37` on all 35 lines of `meta/uptime.log`, from the start to the end: no restart.
- Every stage's `STATE.json` (M, X, E, N, MEMD, MEMI on both machines) reads `complete`, and its records are exactly
  the runs of its manifest (`clone/files/.../CAMPAIGN_<stage>.json`), each `complete`. GUARD's two records are its
  two refusals (`failed-never-rerun`), as the rehearsal designs them.
- Every stage was collected by the kit (`collected-*` with `SURVIVORS.json`); every file listed there has the SHA-256
  of the evidence folder's file, and the counts are equal.
- No seed of 7501 or above was simulated: the 46 decks of the rehearsal's runs have no `setseed`, the 92 run records
  have seed `None`, and their noise seeds are 90951 to 90953; GUARD's folders hold no deck.
- The clone the runs used was based on `3156ee4`, with no uncommitted change, and its 41 frozen files have the
  SHA-256 of `3156ee4`.

## What this folder holds

- `<stage>-<machine>`: the kit's evidence folders; `collected-*`: the kit's collected copies with `SURVIVORS.json`.
- `analysis/`: what the analysis wrote before the failure. `meta/`: the logs, the two scripts and `DONE`.
- `clone/`: the rehearsal clone's commits after `3156ee4` (`rehearsal-branch.bundle`, `rehearsal-branch.log`), the files
  they wrote (`files/`), and the claims of its local remote (`remote.bundle`, `remote-refs.txt`).

**Files of 10 MB and more** are on the branch `evidence/learned-dnf-circuit-campaign-4-rehearsal-run-2`
(commits, newest first: 83df0a3 78adc92 460c4ca eecfba1 517c019 2a7c6f9), at the same paths. They are all waveform files (`trace.raw`, `noise.raw`).
Files above 100 MiB are stored there in parts of 90 000 000 bytes, listed in `PARTS.json` on that branch. Their
SHA-256 (of the whole file), paths relative to this folder:

```
6e0ca97aef0f2f00589fc2eda96f7648fed974052abea582386913c5d78831ca  E-a/a-None-x-a-fire-cell/work/fire_a/dev/noise.raw
0cc7768240b2e3cfc2ed2a39d4068e7e83ab1ba903a8c32991008b74ea65e5a0  E-a/a-None-x-a-hold-1/work/hold_a1/dev/noise.raw
6a727c700d87ebf16f71757f918616fcd16b6d60decbb304fd449a5b19cb568b  E-a/a-None-x-a-pulse-2/work/pulse_a2/dev/noise.raw
d38018abde33f14d3e773f50e81796bcd3916da6bc591e85771fe65753bdd9b6  E-a/a-None-x-a-window-1/work/window_a1/dev/noise.raw
25896ca269217c2ba7c8d4ec46fde323a4a2d62ab414b2e85e2d7bfa1afaee75  E-a/a-None-x-b-hold-2/work/hold_b2/dev/noise.raw
8134c1b341e6cea2fa7636c29549b15251eb016d291b8f4e88cb1e9f87fd827a  E-a/a-None-x-b-pulse-1/work/pulse_b1/dev/noise.raw
1bb78cf2545b3ea27c566d1acdc98457ff8995c4e13a599c94b240e1eb0eaa0d  E-a/a-None-x-b-window-2/work/window_b2/dev/noise.raw
3a96dee79b8464cee6ed0dc2675db4b6029acf085371a375eb57abc0b7195458  E-a/a-None-x-c-fire-cell/work/fire_c/dev/noise.raw
64e72e8c1cdb17e0d6169b4f9402712bf8afae79185f6e327f64fc1a286c5827  E-a/a-None-x-c-hold-1/work/hold_c1/dev/noise.raw
baa9b022e82ce0485885caa243de8ea5691027c34b87379245caa58500d4ff4e  E-a/a-None-x-c-pulse-2/work/pulse_c2/dev/noise.raw
edaf24363240a964e9c286bf6073ee75ca251326b0cc2d1dfa2c2f3c38ccde7d  E-a/a-None-x-c-window-1/work/window_c1/dev/noise.raw
a47900d12de55139b0bba5db877083ce88c271ba81269f520973fdd5a8c670d8  E-b/a-None-x-a-hold-2/work/hold_a2/dev/noise.raw
a19081e652d6710c9d4014372101f77dfb54e8e7d9ec657fa7544ad53f2036e4  E-b/a-None-x-a-pulse-1/work/pulse_a1/dev/noise.raw
16ba8ce7d2e8ba9825a0be18a7e740450ae50e96e5af4785acbf22289dc92f9b  E-b/a-None-x-a-window-2/work/window_a2/dev/noise.raw
32ced4a8a70830589c6bbce0c7d6647a63f6f117f4db4553bb7748ff7ff17733  E-b/a-None-x-b-fire-cell/work/fire_b/dev/noise.raw
e8651c17e538713dd51bd02ea6c31f239edeaee7592bc001f2e9d3861712f89c  E-b/a-None-x-b-hold-1/work/hold_b1/dev/noise.raw
4d512adc074ac84e3fae5618bf2d457205a6000f56876d40977fccbea3f405c1  E-b/a-None-x-b-pulse-2/work/pulse_b2/dev/noise.raw
0cddd86e286ffbe7e3a17d330f1353998cebd6590819eb0b370d1e50285d932e  E-b/a-None-x-b-window-1/work/window_b1/dev/noise.raw
708a2fa110e4a30e5322955edc4a4be48f3abd0152dc2cb94f4d8a7d4f318046  E-b/a-None-x-c-hold-2/work/hold_c2/dev/noise.raw
2c706af8b4d4f4b36c4cded49c58bb3d0c7b3bd3bedbbefe00e60e7f8cf99c7e  E-b/a-None-x-c-pulse-1/work/pulse_c1/dev/noise.raw
f720c60ec732c535bdbb21db75ca60ed82f6bc34e8bad02b08c47a61e55dc8a6  E-b/a-None-x-c-window-2/work/window_c2/dev/noise.raw
e2be2f633ce8848440611eef4d1a6ee28bb58ab1ec2d2991e15e3a8d9c44b3e2  M-a/a-None-cal-off/evidence/trace.raw
83f7d9ddbd8f862f0bdb9c03ca82c23df6c8b04317c5363131852bddd1dfb2de  M-a/a-None-cal-on/evidence/trace.raw
8c38c64cbe769e70ceb4a2b9d06a6278d506fe787f6e9c63a4044ac9ba83b3de  M-a/a-None-quiet-nocontrol/evidence/trace.raw
dc389de57d7c7fc1c758c6a1c68f8168f55a7154342d409fcdf19108ded3a315  M-a/a-None-untrained-check/evidence/trace.raw
4710580c26f0c6e71f53edcd25e7c8b2d1ecc5fdc28a9cf0ea1b5b6c7d44f7a7  M-b/b-None-injected-r1-again/evidence/trace.raw
4710580c26f0c6e71f53edcd25e7c8b2d1ecc5fdc28a9cf0ea1b5b6c7d44f7a7  M-b/b-None-injected-r1/evidence/trace.raw
8f1c83e96fc158cb3de60da29c94a3c261212c68f48e983a66a834d316faf4a0  M-b/b-None-injected-r2/evidence/trace.raw
48ed309a7c66fb6b4b887c25eb6e178994be92bf7d9ace53687b53b8451a4534  MEMD-a/a-None-need7-device-0/evidence/trace.raw
4a7466ee2eda509baf6c4cf2ef432a657fa93e701264b6d70e2994f1a5d91ef9  MEMD-a/a-None-need7-device-1/evidence/trace.raw
95d6f48f676c474dc50a54a98b5f212d3d5375f16d513011f5afdb7a9186c6da  MEMD-a/a-None-need7-device-2/evidence/trace.raw
7f6c181f5c7f5fcbe95f554af2ab31da979d67948d41f7eeecba639c67328700  MEMD-a/a-None-need7-device-3/evidence/trace.raw
be5928ed31820085b6e5b348bc17e8d97e5f0fb64bf6b68c261aa324e116a472  MEMD-b/b-None-untrained-filler-d/evidence/trace.raw
4191e0f58ed1b15e0f04c880bbdbaa8c3c8ef1b0899f687cb7ecc60d19c90f73  MEMI-a/a-None-untrained-filler-i/evidence/trace.raw
cef5b9dc648ccb23260359ddeb8528c10d669eae2f6ee6215459f319d139950b  MEMI-b/b-None-need7-injected-0/evidence/trace.raw
d9366367fb29cc173f65894ab701db501c438e6ceb8bb38b6ed6d9a42f9d5a43  MEMI-b/b-None-need7-injected-1/evidence/trace.raw
193aae4a1dfeb2a9cfca064dc78780e8efc6f634caf457ef1fe8364441348455  MEMI-b/b-None-need7-injected-2/evidence/trace.raw
cef5b9dc648ccb23260359ddeb8528c10d669eae2f6ee6215459f319d139950b  MEMI-b/b-None-need7-injected-3/evidence/trace.raw
0b06926ef677d9da56250f86fe46717dc3cd5767bd8ee28e42e8ab46de34dde9  N-a/a-None-n1/evidence/trace.raw
987e6bdcafac7869eb095970c1a151fcc7377638643e100413b53f212174fdf6  N-a/a-None-n2/evidence/trace.raw
8eba42ac0199aee7549816fcebe4666c0a1283a5104d36ef6f68db4d63de3008  N-a/a-None-n3/evidence/trace.raw
4328b318a45d11466d6f1145f0692f9029e8c03226e49b2517f64245748b00e4  N-a/a-None-quiet/evidence/trace.raw
3024b8b004c00d45699b8d040879c57fef1402263f0de07a1a9332bde6d21c3d  N-b/b-None-n1-again/evidence/trace.raw
c24023bcf13b5f8ae008c7b5ed8ee8cef52154405d638db328e866e79d443442  N-b/b-None-zero-amplitude/evidence/trace.raw
84ca07fc364fc277ee5be5ad7bcfd65af8eae4e55fbae92a063ce3a6e544337a  X-a/a-None-xcheck-a-hold-1/work/hold_a1/dev/noise.raw
05df36432ba8915bc95c332be4562ea00cfce640d2430f3f9e9e79ecaa07097f  X-b/b-None-extract-single/work/fire_a/dev/noise.raw
48c020cd26cceea03a493571827b5e2cf7178051c0accc23ef3cf433653f0dcb  X-b/b-None-extract-single/work/fire_b/dev/noise.raw
16674eaf33ca67f3bfbc604d198891a1a9bf01a05192d8b998e3fe052a8e5a9e  X-b/b-None-extract-single/work/fire_c/dev/noise.raw
8463608151a9781282d6c3b18c8e5dd74c9cc0abc77642b204b9899178ff3831  X-b/b-None-extract-single/work/hold_a1/dev/noise.raw
1dabaeffe9eb651289ec4615f0c44b285e75de70fb7588f0825ab6a82e29f5d0  X-b/b-None-extract-single/work/hold_a2/dev/noise.raw
150418bea42d4d475ad3987a394fa398bf78e5735ff5103cf3b795d694debd9c  X-b/b-None-extract-single/work/hold_b1/dev/noise.raw
068a7fc1fb344e59bf7142b4430ef83de24c892a18d496e851aa2997c3fbb52d  X-b/b-None-extract-single/work/hold_b2/dev/noise.raw
f923a04dc64540d65898ef919a86c8a239c41867c95a20678bd2a0d16f3636c7  X-b/b-None-extract-single/work/hold_c1/dev/noise.raw
d867478ddb73a5dd44cc106d629a363f8914c7998a7dfec5b3044829cf9be3fd  X-b/b-None-extract-single/work/hold_c2/dev/noise.raw
9df7b0ed9da6b02480457af4c13047ade32a6386b062cdb25275b92a533885b7  X-b/b-None-extract-single/work/pulse_a1/dev/noise.raw
c18c8a0b91d7e00389f54b7229f5b0a2b633ae91dfd3b2c90f271f110e4056da  X-b/b-None-extract-single/work/pulse_a2/dev/noise.raw
73df37b91add5b79420ec0469e160b19dc0ec0b006c9e430509408b936730d0b  X-b/b-None-extract-single/work/pulse_b1/dev/noise.raw
0002fe0f9ceebbd7efb2bc2b2778b5d3919a5a3b7f661945321d4b40f3905b06  X-b/b-None-extract-single/work/pulse_b2/dev/noise.raw
92873ef8c4601ac963bbdb084375e9ff47e0bd96ae1f7165cad767e27699e191  X-b/b-None-extract-single/work/pulse_c1/dev/noise.raw
25c6278b6faa9a3beae179c20726316f3e18e44f5389bae58a8e5813ed97a7ed  X-b/b-None-extract-single/work/pulse_c2/dev/noise.raw
c4a0b52b4a68526635fb53f5bfd74419f06b6bac79911ec0d5c19e6bed7324bb  X-b/b-None-extract-single/work/window_a1/dev/noise.raw
bd917e6a40a229787a9dcce50a736018ff3d217483fbc773df08b073d06bf4d4  X-b/b-None-extract-single/work/window_a2/dev/noise.raw
e15ff8088e13e1bdd1cfd792b74f42ca1b3aeb3ba7a7af87eefb5002f012d517  X-b/b-None-extract-single/work/window_b1/dev/noise.raw
d6d126d08a53d8a36f1aab2545c20e03e549cbc43898ad3c39b1165a091f8611  X-b/b-None-extract-single/work/window_b2/dev/noise.raw
1507a503cfe953ae1c8decd4267295b33ddf99e0f68939b71ac805801590be6b  X-b/b-None-extract-single/work/window_c1/dev/noise.raw
42a1764648f589f643ecc6a4655b085386674a87dbc3724eb5ad6b016eb01f2f  X-b/b-None-extract-single/work/window_c2/dev/noise.raw
6e0ca97aef0f2f00589fc2eda96f7648fed974052abea582386913c5d78831ca  collected-E-a/a-None-x-a-fire-cell/work/fire_a/dev/noise.raw
0cc7768240b2e3cfc2ed2a39d4068e7e83ab1ba903a8c32991008b74ea65e5a0  collected-E-a/a-None-x-a-hold-1/work/hold_a1/dev/noise.raw
6a727c700d87ebf16f71757f918616fcd16b6d60decbb304fd449a5b19cb568b  collected-E-a/a-None-x-a-pulse-2/work/pulse_a2/dev/noise.raw
d38018abde33f14d3e773f50e81796bcd3916da6bc591e85771fe65753bdd9b6  collected-E-a/a-None-x-a-window-1/work/window_a1/dev/noise.raw
25896ca269217c2ba7c8d4ec46fde323a4a2d62ab414b2e85e2d7bfa1afaee75  collected-E-a/a-None-x-b-hold-2/work/hold_b2/dev/noise.raw
8134c1b341e6cea2fa7636c29549b15251eb016d291b8f4e88cb1e9f87fd827a  collected-E-a/a-None-x-b-pulse-1/work/pulse_b1/dev/noise.raw
1bb78cf2545b3ea27c566d1acdc98457ff8995c4e13a599c94b240e1eb0eaa0d  collected-E-a/a-None-x-b-window-2/work/window_b2/dev/noise.raw
3a96dee79b8464cee6ed0dc2675db4b6029acf085371a375eb57abc0b7195458  collected-E-a/a-None-x-c-fire-cell/work/fire_c/dev/noise.raw
64e72e8c1cdb17e0d6169b4f9402712bf8afae79185f6e327f64fc1a286c5827  collected-E-a/a-None-x-c-hold-1/work/hold_c1/dev/noise.raw
baa9b022e82ce0485885caa243de8ea5691027c34b87379245caa58500d4ff4e  collected-E-a/a-None-x-c-pulse-2/work/pulse_c2/dev/noise.raw
edaf24363240a964e9c286bf6073ee75ca251326b0cc2d1dfa2c2f3c38ccde7d  collected-E-a/a-None-x-c-window-1/work/window_c1/dev/noise.raw
a47900d12de55139b0bba5db877083ce88c271ba81269f520973fdd5a8c670d8  collected-E-b/a-None-x-a-hold-2/work/hold_a2/dev/noise.raw
a19081e652d6710c9d4014372101f77dfb54e8e7d9ec657fa7544ad53f2036e4  collected-E-b/a-None-x-a-pulse-1/work/pulse_a1/dev/noise.raw
16ba8ce7d2e8ba9825a0be18a7e740450ae50e96e5af4785acbf22289dc92f9b  collected-E-b/a-None-x-a-window-2/work/window_a2/dev/noise.raw
32ced4a8a70830589c6bbce0c7d6647a63f6f117f4db4553bb7748ff7ff17733  collected-E-b/a-None-x-b-fire-cell/work/fire_b/dev/noise.raw
e8651c17e538713dd51bd02ea6c31f239edeaee7592bc001f2e9d3861712f89c  collected-E-b/a-None-x-b-hold-1/work/hold_b1/dev/noise.raw
4d512adc074ac84e3fae5618bf2d457205a6000f56876d40977fccbea3f405c1  collected-E-b/a-None-x-b-pulse-2/work/pulse_b2/dev/noise.raw
0cddd86e286ffbe7e3a17d330f1353998cebd6590819eb0b370d1e50285d932e  collected-E-b/a-None-x-b-window-1/work/window_b1/dev/noise.raw
708a2fa110e4a30e5322955edc4a4be48f3abd0152dc2cb94f4d8a7d4f318046  collected-E-b/a-None-x-c-hold-2/work/hold_c2/dev/noise.raw
2c706af8b4d4f4b36c4cded49c58bb3d0c7b3bd3bedbbefe00e60e7f8cf99c7e  collected-E-b/a-None-x-c-pulse-1/work/pulse_c1/dev/noise.raw
f720c60ec732c535bdbb21db75ca60ed82f6bc34e8bad02b08c47a61e55dc8a6  collected-E-b/a-None-x-c-window-2/work/window_c2/dev/noise.raw
e2be2f633ce8848440611eef4d1a6ee28bb58ab1ec2d2991e15e3a8d9c44b3e2  collected-M-a/a-None-cal-off/evidence/trace.raw
83f7d9ddbd8f862f0bdb9c03ca82c23df6c8b04317c5363131852bddd1dfb2de  collected-M-a/a-None-cal-on/evidence/trace.raw
8c38c64cbe769e70ceb4a2b9d06a6278d506fe787f6e9c63a4044ac9ba83b3de  collected-M-a/a-None-quiet-nocontrol/evidence/trace.raw
dc389de57d7c7fc1c758c6a1c68f8168f55a7154342d409fcdf19108ded3a315  collected-M-a/a-None-untrained-check/evidence/trace.raw
4710580c26f0c6e71f53edcd25e7c8b2d1ecc5fdc28a9cf0ea1b5b6c7d44f7a7  collected-M-b/b-None-injected-r1-again/evidence/trace.raw
4710580c26f0c6e71f53edcd25e7c8b2d1ecc5fdc28a9cf0ea1b5b6c7d44f7a7  collected-M-b/b-None-injected-r1/evidence/trace.raw
8f1c83e96fc158cb3de60da29c94a3c261212c68f48e983a66a834d316faf4a0  collected-M-b/b-None-injected-r2/evidence/trace.raw
48ed309a7c66fb6b4b887c25eb6e178994be92bf7d9ace53687b53b8451a4534  collected-MEMD-a/a-None-need7-device-0/evidence/trace.raw
4a7466ee2eda509baf6c4cf2ef432a657fa93e701264b6d70e2994f1a5d91ef9  collected-MEMD-a/a-None-need7-device-1/evidence/trace.raw
95d6f48f676c474dc50a54a98b5f212d3d5375f16d513011f5afdb7a9186c6da  collected-MEMD-a/a-None-need7-device-2/evidence/trace.raw
7f6c181f5c7f5fcbe95f554af2ab31da979d67948d41f7eeecba639c67328700  collected-MEMD-a/a-None-need7-device-3/evidence/trace.raw
be5928ed31820085b6e5b348bc17e8d97e5f0fb64bf6b68c261aa324e116a472  collected-MEMD-b/b-None-untrained-filler-d/evidence/trace.raw
4191e0f58ed1b15e0f04c880bbdbaa8c3c8ef1b0899f687cb7ecc60d19c90f73  collected-MEMI-a/a-None-untrained-filler-i/evidence/trace.raw
cef5b9dc648ccb23260359ddeb8528c10d669eae2f6ee6215459f319d139950b  collected-MEMI-b/b-None-need7-injected-0/evidence/trace.raw
d9366367fb29cc173f65894ab701db501c438e6ceb8bb38b6ed6d9a42f9d5a43  collected-MEMI-b/b-None-need7-injected-1/evidence/trace.raw
193aae4a1dfeb2a9cfca064dc78780e8efc6f634caf457ef1fe8364441348455  collected-MEMI-b/b-None-need7-injected-2/evidence/trace.raw
cef5b9dc648ccb23260359ddeb8528c10d669eae2f6ee6215459f319d139950b  collected-MEMI-b/b-None-need7-injected-3/evidence/trace.raw
0b06926ef677d9da56250f86fe46717dc3cd5767bd8ee28e42e8ab46de34dde9  collected-N-a/a-None-n1/evidence/trace.raw
987e6bdcafac7869eb095970c1a151fcc7377638643e100413b53f212174fdf6  collected-N-a/a-None-n2/evidence/trace.raw
8eba42ac0199aee7549816fcebe4666c0a1283a5104d36ef6f68db4d63de3008  collected-N-a/a-None-n3/evidence/trace.raw
4328b318a45d11466d6f1145f0692f9029e8c03226e49b2517f64245748b00e4  collected-N-a/a-None-quiet/evidence/trace.raw
3024b8b004c00d45699b8d040879c57fef1402263f0de07a1a9332bde6d21c3d  collected-N-b/b-None-n1-again/evidence/trace.raw
c24023bcf13b5f8ae008c7b5ed8ee8cef52154405d638db328e866e79d443442  collected-N-b/b-None-zero-amplitude/evidence/trace.raw
84ca07fc364fc277ee5be5ad7bcfd65af8eae4e55fbae92a063ce3a6e544337a  collected-X-a/a-None-xcheck-a-hold-1/work/hold_a1/dev/noise.raw
05df36432ba8915bc95c332be4562ea00cfce640d2430f3f9e9e79ecaa07097f  collected-X-b/b-None-extract-single/work/fire_a/dev/noise.raw
48c020cd26cceea03a493571827b5e2cf7178051c0accc23ef3cf433653f0dcb  collected-X-b/b-None-extract-single/work/fire_b/dev/noise.raw
16674eaf33ca67f3bfbc604d198891a1a9bf01a05192d8b998e3fe052a8e5a9e  collected-X-b/b-None-extract-single/work/fire_c/dev/noise.raw
8463608151a9781282d6c3b18c8e5dd74c9cc0abc77642b204b9899178ff3831  collected-X-b/b-None-extract-single/work/hold_a1/dev/noise.raw
1dabaeffe9eb651289ec4615f0c44b285e75de70fb7588f0825ab6a82e29f5d0  collected-X-b/b-None-extract-single/work/hold_a2/dev/noise.raw
150418bea42d4d475ad3987a394fa398bf78e5735ff5103cf3b795d694debd9c  collected-X-b/b-None-extract-single/work/hold_b1/dev/noise.raw
068a7fc1fb344e59bf7142b4430ef83de24c892a18d496e851aa2997c3fbb52d  collected-X-b/b-None-extract-single/work/hold_b2/dev/noise.raw
f923a04dc64540d65898ef919a86c8a239c41867c95a20678bd2a0d16f3636c7  collected-X-b/b-None-extract-single/work/hold_c1/dev/noise.raw
d867478ddb73a5dd44cc106d629a363f8914c7998a7dfec5b3044829cf9be3fd  collected-X-b/b-None-extract-single/work/hold_c2/dev/noise.raw
9df7b0ed9da6b02480457af4c13047ade32a6386b062cdb25275b92a533885b7  collected-X-b/b-None-extract-single/work/pulse_a1/dev/noise.raw
c18c8a0b91d7e00389f54b7229f5b0a2b633ae91dfd3b2c90f271f110e4056da  collected-X-b/b-None-extract-single/work/pulse_a2/dev/noise.raw
73df37b91add5b79420ec0469e160b19dc0ec0b006c9e430509408b936730d0b  collected-X-b/b-None-extract-single/work/pulse_b1/dev/noise.raw
0002fe0f9ceebbd7efb2bc2b2778b5d3919a5a3b7f661945321d4b40f3905b06  collected-X-b/b-None-extract-single/work/pulse_b2/dev/noise.raw
92873ef8c4601ac963bbdb084375e9ff47e0bd96ae1f7165cad767e27699e191  collected-X-b/b-None-extract-single/work/pulse_c1/dev/noise.raw
25c6278b6faa9a3beae179c20726316f3e18e44f5389bae58a8e5813ed97a7ed  collected-X-b/b-None-extract-single/work/pulse_c2/dev/noise.raw
c4a0b52b4a68526635fb53f5bfd74419f06b6bac79911ec0d5c19e6bed7324bb  collected-X-b/b-None-extract-single/work/window_a1/dev/noise.raw
bd917e6a40a229787a9dcce50a736018ff3d217483fbc773df08b073d06bf4d4  collected-X-b/b-None-extract-single/work/window_a2/dev/noise.raw
e15ff8088e13e1bdd1cfd792b74f42ca1b3aeb3ba7a7af87eefb5002f012d517  collected-X-b/b-None-extract-single/work/window_b1/dev/noise.raw
d6d126d08a53d8a36f1aab2545c20e03e549cbc43898ad3c39b1165a091f8611  collected-X-b/b-None-extract-single/work/window_b2/dev/noise.raw
1507a503cfe953ae1c8decd4267295b33ddf99e0f68939b71ac805801590be6b  collected-X-b/b-None-extract-single/work/window_c1/dev/noise.raw
42a1764648f589f643ecc6a4655b085386674a87dbc3724eb5ad6b016eb01f2f  collected-X-b/b-None-extract-single/work/window_c2/dev/noise.raw
```
