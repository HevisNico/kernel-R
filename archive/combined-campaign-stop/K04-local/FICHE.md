# K04 local-only files of the yield lot

## Provenance
- Machine: K04
- Session: session_01TzF7ZWhX6ao8foJQBLth8Y
- Source directory: ~/yieldK04/out on K04 (the yield-lot OUTROOT of YIELD_LOT_RULE_2, code at research/layered-stage-d 70a0f66)
- Published counterpart: evidence/yield-lot-K04 at ec4adfe996d49431b2b456dd75987277f10393f6 (results under research/layered-networks/dev/yield_lot/results/K04)

## Archived items (26 files, under yieldK04/out/ with their original relative paths)
- State: raw logs and decks of a completed yield-lot run (5/5 stage D done, 0 failed).
- Why never published: the runbook's copy rule for the results branch copied only *.json, SHA256SUMS, INVENTORY_*, DONE and *.log under 2 MB, excluding session.log, pdk/, lean_build and runs/; the later second commit added only the files listed in a SHA256SUMS. None of these 26 files is listed in a SHA256SUMS, so none was copied.
- Recovery: copy yieldK04/out/<path> back to <OUTROOT>/<path>; check with SHA256SUMS in this folder.

| path | bytes | sha256 |
|---|---|---|
| yieldK04/out/ANDOR3_6108/D/.spiceinit | 71 | ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1 |
| yieldK04/out/ANDOR3_6108/D/blocks.spice | 2212 | 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd |
| yieldK04/out/ANDOR3_6108/D/input.spice | 134862 | 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b |
| yieldK04/out/ANDOR3_6108/D/session.log | 759701 | 03d56d3aca69105e49be8c78399a9ad961e200205070b653b0d32c0fcccee53c |
| yieldK04/out/ANDOR3_6108/deck.spice | 134862 | 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b |
| yieldK04/out/ANDOR3_6144/D/.spiceinit | 71 | ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1 |
| yieldK04/out/ANDOR3_6144/D/blocks.spice | 2212 | 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd |
| yieldK04/out/ANDOR3_6144/D/input.spice | 134862 | 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b |
| yieldK04/out/ANDOR3_6144/D/session.log | 866045 | f35eb3ea4f9e406f6116d9782fb0aceb391431096973b239b9f73beba16e9eec |
| yieldK04/out/ANDOR3_6144/deck.spice | 134862 | 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b |
| yieldK04/out/DRIVER_PID | 4 | 04c8b68027a1d9c2135cace31d40e1be86c4de790ae292fa20b0c937918d5141 |
| yieldK04/out/NOT1_6218/D/.spiceinit | 71 | ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1 |
| yieldK04/out/NOT1_6218/D/blocks.spice | 2212 | 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd |
| yieldK04/out/NOT1_6218/D/input.spice | 39616 | 519a6ce2db19bb6cf7b454f7b9fc6d86b0bf2ad8a4fdb8c6cfd09587272a4c02 |
| yieldK04/out/NOT1_6218/D/session.log | 105597 | 6e9480ca55a33139866d04a93fc4c8f71c83ba680fbdca9134cfa8293255699e |
| yieldK04/out/NOT1_6218/deck.spice | 39616 | 519a6ce2db19bb6cf7b454f7b9fc6d86b0bf2ad8a4fdb8c6cfd09587272a4c02 |
| yieldK04/out/XOR3_6164/D/.spiceinit | 71 | ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1 |
| yieldK04/out/XOR3_6164/D/blocks.spice | 2212 | 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd |
| yieldK04/out/XOR3_6164/D/input.spice | 144904 | 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e |
| yieldK04/out/XOR3_6164/D/session.log | 844921 | 1345ff8b062744cd74aff585b1ca70ff5fc8961058a5326c23bbc19fe03f0277 |
| yieldK04/out/XOR3_6164/deck.spice | 144904 | 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e |
| yieldK04/out/XOR3_6185/D/.spiceinit | 71 | ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1 |
| yieldK04/out/XOR3_6185/D/blocks.spice | 2212 | 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd |
| yieldK04/out/XOR3_6185/D/input.spice | 144904 | 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e |
| yieldK04/out/XOR3_6185/D/session.log | 856296 | ab2b4a03cff6e0efb3fb3a613e45fc37ae9f9ce5bafa6227aae7910fc3650869 |
| yieldK04/out/XOR3_6185/deck.spice | 144904 | 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e |

## Regenerable, not archived
- 27 Lean .olean build files (7,376,640 bytes), rebuilt by the run's Lean step from the pinned Lean 4.35.0 and sources:
  - yieldK04/out/NOT1_6218/inv/lean_build/CircuitInverterGate.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/InverterInstanceTiming.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/InverterTarget.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/MonotoneOneSidedTarget.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/MonotoneSupport.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/MonotoneTarget.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/Target.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/TwoLayerTarget.olean
  - yieldK04/out/NOT1_6218/inv/lean_build/TwoRailsTarget.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/CircuitInverterGate.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/InverterInstanceTiming.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/InverterTarget.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/MonotoneOneSidedTarget.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/MonotoneSupport.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/MonotoneTarget.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/Target.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/TwoLayerTarget.olean
  - yieldK04/out/XOR3_6164/inv/lean_build/TwoRailsTarget.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/CircuitInverterGate.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/InverterInstanceTiming.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/InverterTarget.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/MonotoneOneSidedTarget.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/MonotoneSupport.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/MonotoneTarget.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/Target.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/TwoLayerTarget.olean
  - yieldK04/out/XOR3_6185/inv/lean_build/TwoRailsTarget.olean
- 33 pdk symlinks, pointing to the SKY130 PDK at 1232782c (research/circuit/pdk, fetched by research/circuit/fetch_pdk.sh):
  - yieldK04/out/ANDOR3_6108/D/pdk -> /home/user/kernel-R/research/circuit/pdk
  - yieldK04/out/ANDOR3_6144/D/pdk -> /home/user/kernel-R/research/circuit/pdk
  - yieldK04/out/NOT1_6218/D/pdk -> /home/user/kernel-R/research/circuit/pdk
  - yieldK04/out/NOT1_6218/inv/n0/runs/6218/R1_absent/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/NOT1_6218/inv/n0/runs/6218/R2_present/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/NOT1_6218/inv/n0/runs/6218/R3_leak_above/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/NOT1_6218/inv/n0/runs/6218/R4_leak_below/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/NOT1_6218/inv/n0/runs/6218/R5_static/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/NOT1_6218/inv/network_op/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/D/pdk -> /home/user/kernel-R/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n0/runs/6164/R1_absent/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n0/runs/6164/R2_present/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n0/runs/6164/R3_leak_above/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n0/runs/6164/R4_leak_below/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n0/runs/6164/R5_static/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n1/runs/6164/R1_absent/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n1/runs/6164/R2_present/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n1/runs/6164/R3_leak_above/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n1/runs/6164/R4_leak_below/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/n1/runs/6164/R5_static/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6164/inv/network_op/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/D/pdk -> /home/user/kernel-R/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n0/runs/6185/R1_absent/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n0/runs/6185/R2_present/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n0/runs/6185/R3_leak_above/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n0/runs/6185/R4_leak_below/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n0/runs/6185/R5_static/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n1/runs/6185/R1_absent/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n1/runs/6185/R2_present/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n1/runs/6185/R3_leak_above/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n1/runs/6185/R4_leak_below/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/n1/runs/6185/R5_static/pdk -> /root/yieldK04/kit/research/circuit/pdk
  - yieldK04/out/XOR3_6185/inv/network_op/pdk -> /root/yieldK04/kit/research/circuit/pdk

## Not archived: superseded draft commit
- ebd1f3a5160984f8263b7be838df6539eae3223c in ~/reh/push_K04.old1: superseded first draft of the root, not pushed; its content is on evidence/combined-rehearsal-K04 b90e814 and archive/combined-campaign-stop/raw-K04 e1777bc.
