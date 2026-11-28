# Lot K02-local: files that existed only on machine K02, archived before closing

The combined campaign was stopped before its official draw (owner's decision, 2026-11-28). This lot copies the files
that existed only on machine K02's disk and nowhere on GitHub, as found by a read-only inventory that compared every
local file's sha256 with the blobs of the published branches. Nothing on the machine was changed, moved or deleted.
The companion lot is archive/combined-campaign-stop/K02 (db9aa43810bf705bf0165cbcb9ea721e55b06269: drafts bundle and
runner files).

## Provenance

- Machine K02 (cloud container), Claude Code session_01TzF7ZUzWF9YA9phr9ZxG8C; coordinator
  session_01TzF7ZUoTUj44AGYGuEFzHA.
- Repository: https://github.com/HevisNico/kernel-R.
- Toolchain on the machine: ngspice 42 (sha256 820658317b0b…b7fc45), SKY130 PDK sky130_fd_pr 1232782c at
  /home/user/pdk-sky130, Lean 4.35.0 (/opt/lean, binary bf8d54e4…), Python 3.13.18.
- Source directories and their related published branches:

| source directory (on K02) | archived under | related branch | tip |
|---|---|---|---|
| ~/yieldK02/out | yieldK02/out/ | evidence/yield-lot-K02 (results under research/layered-networks/dev/yield_lot/results/K02) | 9df6d11cf7945c2068e6188cf3ef1669dce0f233 |
| ~/devtest_b_discarded_a8303e8e/out_K02 | devtest_b_discarded_a8303e8e/out_K02/ | evidence/devtest-seals-K02 (its seal only) | c3c36431e7efdcd84810684c209d56165515773e |

This lot: 123 archived files plus FICHE.md and SHA256SUMS, 18388281 bytes of archived files. No file exceeds
50,000,000 bytes, so nothing is split. No secrets: the files were searched for tokens, keys, passwords and e-mail
addresses, with no match. ENV.json holds only tool paths, hashes and versions.

## Items

### 1. yieldK02/out/: the yield lot's local-only files (16 files)

State: complete outputs of the yield-lot run on K02. Its results were published on evidence/yield-lot-K02 9df6d11c and
verified there; these files are the inputs and logs that stayed behind.

- DRIVER_PID: the driver's process id at launch (a record).
- For ANDOR3_6104, ANDOR3_6137, NOT1_6213, XOR3_6158 and XOR3_6181: D/session.log (the full ngspice session log of the
  D stage), D/input.spice and deck.spice (the deck as run; byte-equal pairs per gate family).

Why never published: the runbook's copy rule for the results commit excluded */runs/*, session.log files and
lean_build/, to keep the results branch small. deck.spice and input.spice are copies of decks whose generators are on
GitHub, but their exact bytes were not committed.

Recover: fetch this branch by name and run `sha256sum -c SHA256SUMS`. To compare with the results, fetch
evidence/yield-lot-K02 by name; each gate's record there names the deck sha256 values these files carry.

### 2. devtest_b_discarded_a8303e8e/out_K02/: the discarded first devtest (b) run (107 files)

State: INCOMPLETE and DISCARDED. Run 1 of devtest (b), at stage-D tree a8303e8e, was stopped with SIGTERM on the
coordinator's STOP message. It was replaced by run 2 (evidence/devtest-seals2-K02 and evidence/devtest-run2-K02).
Its sealed log is on evidence/devtest-seals-K02 c3c36431. The local .seal_log_work/.git, whose HEAD is c3c36431, is
therefore on GitHub and not repeated here.

Contents: the top-level records (DISK_AT_LAUNCH.json, DRIVER_PID, DRIVER_PIDS.log, ENV.json, INVENTORY_START,
PLAN*.json, SIGNALS.json, TEMPLATE_CHECK.json, driver.log, trees.json); XOR3_9803/D and N0 (record.json,
session.log, decks); XOR3_9803/inv/n0 and n1 runs (trace.txt, ngspice.log, input.spice, blocks.spice, .spiceinit,
MEASURE.json, gates); and kernel_build/KERNEL_BUILD.json.

Why never published: the runbook publishes a run's root only when the run finishes. A stopped run publishes its seal
only, so this output was never copied to a branch.

Recover: fetch this branch by name and run `sha256sum -c SHA256SUMS`. Then fetch evidence/devtest-seals-K02 by name
to match the seal.

## Regenerable, not archived

### Lean .olean build products (48 files, 15608208 bytes)

Built by Lean 4.35.0 from the Lean sources on GitHub (lean_build: the inverter targets; kernel_build: the kernel).
Rebuild them with the same Lean binary from the tree each run's record names.

| path | size (bytes) | sha256 |
|---|---|---|
| yieldK02/out/NOT1_6213/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| yieldK02/out/NOT1_6213/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| yieldK02/out/NOT1_6213/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| yieldK02/out/NOT1_6213/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| yieldK02/out/NOT1_6213/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| yieldK02/out/NOT1_6213/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| yieldK02/out/NOT1_6213/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| yieldK02/out/NOT1_6213/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| yieldK02/out/NOT1_6213/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| yieldK02/out/XOR3_6158/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| yieldK02/out/XOR3_6158/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| yieldK02/out/XOR3_6158/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| yieldK02/out/XOR3_6158/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| yieldK02/out/XOR3_6158/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| yieldK02/out/XOR3_6158/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| yieldK02/out/XOR3_6158/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| yieldK02/out/XOR3_6158/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| yieldK02/out/XOR3_6158/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| yieldK02/out/XOR3_6181/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| yieldK02/out/XOR3_6181/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| yieldK02/out/XOR3_6181/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| yieldK02/out/XOR3_6181/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| yieldK02/out/XOR3_6181/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| yieldK02/out/XOR3_6181/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| yieldK02/out/XOR3_6181/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| yieldK02/out/XOR3_6181/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| yieldK02/out/XOR3_6181/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/LayeredMonotoneCheckerProofs.olean | 1017584 | 62fb815218748d771a046a11f74eb9924434df467c1927adaa6c124e2f1e05bd |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/LayeredMonotoneCheckerTargets.olean | 481664 | 8e3c93d0fb2bba83a7906e7435e98b0151505fe2bda5d5f8f9c093b979f3c9fb |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/LayeredMonotoneTarget.olean | 749848 | 3406d3f64766a16920aaa15c98efd92b763f9ebdbc695ba2c7a161509b644064 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotonePremiseCompleteness.olean | 408040 | b5cf3330546b6ef31776c905bd5dfc9cce95ad270d5cfa3036a71a20e114efcf |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotonePremiseCompletenessTargets.olean | 11000 | 51fe8f393314b08d208c428ae8552f3385629ea36cb9b4569dcad5235fd8bf69 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotonePremiseSoundness.olean | 476376 | a6676498d337cd21d0242bc64719ca9237f90f041dc36dc55390de487f91ff88 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotonePremiseTargets.olean | 753640 | ee8b52fd699c717d6ee3f45156f0d5184ad239bebe0c201e27d579fa31e2fe17 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| devtest_b_discarded_a8303e8e/out_K02/kernel_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |

### pdk symlinks (46 links)

They point to the SKY130 PDK checkout (sky130_fd_pr 1232782c) or to the kit's research/circuit/pdk. They hold no data.
Recreate each with `ln -s <target> <path>` after installing the PDK at the same commit. A symlink has no content
sha256; the target is listed.

| path | target |
|---|---|
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/D/pdk | /home/user/pdk-sky130 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/N0/pdk | /home/user/pdk-sky130 |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n0/runs/9803/R1_absent/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n0/runs/9803/R2_present/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n0/runs/9803/R3_leak_above/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n0/runs/9803/R4_leak_below/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n0/runs/9803/R5_static/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n1/runs/9803/R1_absent/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n1/runs/9803/R2_present/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n1/runs/9803/R3_leak_above/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n1/runs/9803/R4_leak_below/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/n1/runs/9803/R5_static/pdk | /root/devtest_b/kit/research/circuit/pdk |
| devtest_b_discarded_a8303e8e/out_K02/XOR3_9803/inv/network_op/pdk | /root/devtest_b/kit/research/circuit/pdk |
| yieldK02/out/ANDOR3_6104/D/pdk | /home/user/pdk-sky130 |
| yieldK02/out/ANDOR3_6137/D/pdk | /home/user/pdk-sky130 |
| yieldK02/out/NOT1_6213/D/pdk | /home/user/pdk-sky130 |
| yieldK02/out/NOT1_6213/inv/n0/runs/6213/R1_absent/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/NOT1_6213/inv/n0/runs/6213/R2_present/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/NOT1_6213/inv/n0/runs/6213/R3_leak_above/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/NOT1_6213/inv/n0/runs/6213/R4_leak_below/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/NOT1_6213/inv/n0/runs/6213/R5_static/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/NOT1_6213/inv/network_op/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/D/pdk | /home/user/pdk-sky130 |
| yieldK02/out/XOR3_6158/inv/n0/runs/6158/R1_absent/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n0/runs/6158/R2_present/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n0/runs/6158/R3_leak_above/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n0/runs/6158/R4_leak_below/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n0/runs/6158/R5_static/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n1/runs/6158/R1_absent/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n1/runs/6158/R2_present/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n1/runs/6158/R3_leak_above/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n1/runs/6158/R4_leak_below/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/n1/runs/6158/R5_static/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6158/inv/network_op/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/D/pdk | /home/user/pdk-sky130 |
| yieldK02/out/XOR3_6181/inv/n0/runs/6181/R1_absent/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n0/runs/6181/R2_present/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n0/runs/6181/R3_leak_above/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n0/runs/6181/R4_leak_below/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n0/runs/6181/R5_static/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n1/runs/6181/R1_absent/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n1/runs/6181/R2_present/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n1/runs/6181/R3_leak_above/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n1/runs/6181/R4_leak_below/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/n1/runs/6181/R5_static/pdk | /root/yieldK02/kit/research/circuit/pdk |
| yieldK02/out/XOR3_6181/inv/network_op/pdk | /root/yieldK02/kit/research/circuit/pdk |

### Also left out

- ~/devtest_b_discarded_a8303e8e/kernel-R, kit and noise: worktrees of commits on GitHub.
- ~/reh/out_K02: kept on the machine; its root is on evidence/combined-rehearsal-K02 and its seal log on
  evidence/combined-seals-K02.
