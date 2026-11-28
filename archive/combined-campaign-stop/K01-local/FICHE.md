# Local-only files archive: K01, yield lot (stage D)

## Provenance
- Machine: K01 (Claude Code cloud session session_01TzF7ZWh8mrS7YeHvNvVjjd)
- Source directory: ~/yieldK01/out (the yield lot's OUTROOT, run by campaign_run3.py on 2026-11-25, code research/layered-stage-d 70a0f66b18ad5b7937eea6a7388a191055c68f97)
- Published results: evidence/yield-lot-K01 at 1d7af823826ed75c94e2b2d1b435a9b9ca3aead5 (research/layered-networks/dev/yield_lot/results/K01)
- Copied here unchanged under yieldK01/out/<same relative path>; the source files are left in place.

## State
Every archived item is a raw log or input of a completed yield-lot run (stage D, dev seeds, counts for nothing): five instances, ANDOR3_6102, ANDOR3_6136, NOT1_6212, XOR3_6157, XOR3_6180, all with stage D done and 0 failed.

## Why these files were never published
The runbook's copy rule (step 10) copied only *.json, SHA256SUMS, INVENTORY_*, DONE and *.log files under 2 MB, excluding session.log, pdk, lean_build and runs/. A second commit added every file listed in a SHA256SUMS. The files below match neither rule:
- <inst>/D/session.log: excluded by name (the ngspice session log of stage D);
- <inst>/D/input.spice, <inst>/D/blocks.spice, <inst>/D/.spiceinit, <inst>/deck.spice: not *.json or *.log, and listed in no SHA256SUMS;
- DRIVER_PID: no extension, and listed in no SHA256SUMS.

## Items (path under yieldK01/out, size in bytes, sha256)
- ANDOR3_6102/D/.spiceinit 71 ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1
- ANDOR3_6102/D/blocks.spice 2212 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd
- ANDOR3_6102/D/input.spice 134862 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b
- ANDOR3_6102/D/session.log 843569 0b3e9fb4bc3c4f0c2bca618c7c9fc8ddee6f5087e6f35b845e7ff874e9e753a2
- ANDOR3_6102/deck.spice 134862 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b
- ANDOR3_6136/D/.spiceinit 71 ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1
- ANDOR3_6136/D/blocks.spice 2212 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd
- ANDOR3_6136/D/input.spice 134862 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b
- ANDOR3_6136/D/session.log 823220 7ff9105fa312298d0c175b2cc54de3bfcd70e8b88504544e53c58c7d74eceb17
- ANDOR3_6136/deck.spice 134862 3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b
- DRIVER_PID 4 219171393cf5156afbec4cee42b978d3c7a25122e10651d7fb3332d87b7a19cf
- NOT1_6212/D/.spiceinit 71 ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1
- NOT1_6212/D/blocks.spice 2212 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd
- NOT1_6212/D/input.spice 39616 519a6ce2db19bb6cf7b454f7b9fc6d86b0bf2ad8a4fdb8c6cfd09587272a4c02
- NOT1_6212/D/session.log 105938 01ca3bbd97f3d1dd9391449e17f7f6217dbc35f477775f73f139b0a6d3ad9fbe
- NOT1_6212/deck.spice 39616 519a6ce2db19bb6cf7b454f7b9fc6d86b0bf2ad8a4fdb8c6cfd09587272a4c02
- XOR3_6157/D/.spiceinit 71 ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1
- XOR3_6157/D/blocks.spice 2212 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd
- XOR3_6157/D/input.spice 144904 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e
- XOR3_6157/D/session.log 892661 4f092c0c12e5cabf4a1944e7c3201b2e2b4853837fe36dd347795e69684b12b5
- XOR3_6157/deck.spice 144904 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e
- XOR3_6180/D/.spiceinit 71 ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1
- XOR3_6180/D/blocks.spice 2212 7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd
- XOR3_6180/D/input.spice 144904 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e
- XOR3_6180/D/session.log 862036 22afea51f140b3e3ef29f4f274199d498369a809582f97ff3018a6c614878727
- XOR3_6180/deck.spice 144904 28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e

input.spice is byte-identical to the same instance's deck.spice (same sha256); .spiceinit and blocks.spice are identical across instances.

## How to recover
Each file is the file at the same relative path under ~/yieldK01/out on K01. Check with `sha256sum -c SHA256SUMS` from this folder, then copy yieldK01/out/<path> back to <OUTROOT>/<path>.

## Regenerable, not archived
- 27 Lean build files (.olean), compiled from the pinned Lean modules by the inverter gate (research/learned-coincidence, Lean 4.35.0):
  - NOT1_6212/inv/lean_build/CircuitInverterGate.olean
  - NOT1_6212/inv/lean_build/InverterInstanceTiming.olean
  - NOT1_6212/inv/lean_build/InverterTarget.olean
  - NOT1_6212/inv/lean_build/MonotoneOneSidedTarget.olean
  - NOT1_6212/inv/lean_build/MonotoneSupport.olean
  - NOT1_6212/inv/lean_build/MonotoneTarget.olean
  - NOT1_6212/inv/lean_build/Target.olean
  - NOT1_6212/inv/lean_build/TwoLayerTarget.olean
  - NOT1_6212/inv/lean_build/TwoRailsTarget.olean
  - XOR3_6157/inv/lean_build/CircuitInverterGate.olean
  - XOR3_6157/inv/lean_build/InverterInstanceTiming.olean
  - XOR3_6157/inv/lean_build/InverterTarget.olean
  - XOR3_6157/inv/lean_build/MonotoneOneSidedTarget.olean
  - XOR3_6157/inv/lean_build/MonotoneSupport.olean
  - XOR3_6157/inv/lean_build/MonotoneTarget.olean
  - XOR3_6157/inv/lean_build/Target.olean
  - XOR3_6157/inv/lean_build/TwoLayerTarget.olean
  - XOR3_6157/inv/lean_build/TwoRailsTarget.olean
  - XOR3_6180/inv/lean_build/CircuitInverterGate.olean
  - XOR3_6180/inv/lean_build/InverterInstanceTiming.olean
  - XOR3_6180/inv/lean_build/InverterTarget.olean
  - XOR3_6180/inv/lean_build/MonotoneOneSidedTarget.olean
  - XOR3_6180/inv/lean_build/MonotoneSupport.olean
  - XOR3_6180/inv/lean_build/MonotoneTarget.olean
  - XOR3_6180/inv/lean_build/Target.olean
  - XOR3_6180/inv/lean_build/TwoLayerTarget.olean
  - XOR3_6180/inv/lean_build/TwoRailsTarget.olean
- 33 pdk symbolic links to the SKY130 PDK at 1232782c1b9fab3aacda74d67ce7c92bf7da8105 (research/circuit/fetch_pdk.sh):
  - NOT1_6212/inv/network_op/pdk
  - NOT1_6212/inv/n0/runs/6212/R2_present/pdk
  - NOT1_6212/inv/n0/runs/6212/R5_static/pdk
  - NOT1_6212/inv/n0/runs/6212/R1_absent/pdk
  - NOT1_6212/inv/n0/runs/6212/R3_leak_above/pdk
  - NOT1_6212/inv/n0/runs/6212/R4_leak_below/pdk
  - NOT1_6212/D/pdk
  - XOR3_6157/inv/network_op/pdk
  - XOR3_6157/inv/n1/runs/6157/R2_present/pdk
  - XOR3_6157/inv/n1/runs/6157/R5_static/pdk
  - XOR3_6157/inv/n1/runs/6157/R1_absent/pdk
  - XOR3_6157/inv/n1/runs/6157/R3_leak_above/pdk
  - XOR3_6157/inv/n1/runs/6157/R4_leak_below/pdk
  - XOR3_6157/inv/n0/runs/6157/R2_present/pdk
  - XOR3_6157/inv/n0/runs/6157/R5_static/pdk
  - XOR3_6157/inv/n0/runs/6157/R1_absent/pdk
  - XOR3_6157/inv/n0/runs/6157/R3_leak_above/pdk
  - XOR3_6157/inv/n0/runs/6157/R4_leak_below/pdk
  - XOR3_6157/D/pdk
  - XOR3_6180/inv/network_op/pdk
  - XOR3_6180/inv/n1/runs/6180/R2_present/pdk
  - XOR3_6180/inv/n1/runs/6180/R5_static/pdk
  - XOR3_6180/inv/n1/runs/6180/R1_absent/pdk
  - XOR3_6180/inv/n1/runs/6180/R3_leak_above/pdk
  - XOR3_6180/inv/n1/runs/6180/R4_leak_below/pdk
  - XOR3_6180/inv/n0/runs/6180/R2_present/pdk
  - XOR3_6180/inv/n0/runs/6180/R5_static/pdk
  - XOR3_6180/inv/n0/runs/6180/R1_absent/pdk
  - XOR3_6180/inv/n0/runs/6180/R3_leak_above/pdk
  - XOR3_6180/inv/n0/runs/6180/R4_leak_below/pdk
  - XOR3_6180/D/pdk
  - ANDOR3_6102/D/pdk
  - ANDOR3_6136/D/pdk
