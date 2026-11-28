# K06 local archive lot (combined campaign stop)

## Provenance

- Machine: K06 (cloud container; uptime -s 2026-11-28 13:37:55 at the time of writing; the yield lot ran 2026-11-25 06:07–07:26 UTC on the boot of 06:02:00).
- Session: session_01TzF7ZTyKHh2bwXyWKnqzvG (campaign machine K06; created by the former coordinator session_01TzF7ZYZVxJcErqniRxMQ4F).
- Requested by the coordinator of the combined campaign (session_01TzF7ZUoTUj44AGYGuEFzHA), on the owner's approval, 2026-11-28.
- Source directory: `~/yieldK06/out` (the OUTROOT of the yield lot, stage D only, YIELD_LOT_RULE_2, code at research/layered-stage-d 70a0f66b; plan PLAN_K06 seeds ANDOR3 6123/6150, NOT1 6220, XOR3 6166/6190).
- Related published branch: `evidence/yield-lot-K06`, tip `845caf71ff7b1f974257eda6c8fd2548cc7e2e3f` (path research/layered-networks/dev/yield_lot/results/K06).
- The other K06 roots (`~/reh/out_K06` → evidence/combined-rehearsal-K06 acd5cd57 and evidence/combined-seals-K06 faeb29ed; `~/devtest_b2/out_K06` → evidence/devtest-run2-K06 6931fd91; `~/devtest_b_discarded_a8303e8e/out_K06` → evidence/devtest-K06 90e87115) are fully on their evidence branches: nothing of them is here.

## Items (26 files, copies; paths kept relative to the OUTROOT under `yieldK06/out/`)

| item | state | why never published |
|---|---|---|
| `<instance>/D/session.log` (5) | raw ngspice session log of a completed yield-lot stage-D run (all 5 ended "done") | the yield-lot runbook's copy rule (step 10) excluded `session.log` |
| `<instance>/D/input.spice`, `<instance>/deck.spice` (10) | the stage-D deck each run simulated (deck.spice = D/input.spice byte for byte) | the copy rule kept only *.json, SHA256SUMS, INVENTORY_*, DONE and *.log |
| `<instance>/D/blocks.spice`, `<instance>/D/.spiceinit` (10) | the ngspice inputs beside each session.log | same copy rule |
| `DRIVER_PID` (1) | pid of the yield-lot driver (4 bytes) | same copy rule |

None is over 50,000,000 bytes, so nothing is split. No secrets.

## Excluded: regenerable, not archived

### Lean build products (27 .olean files; regenerable, not archived)

Rebuilt by the inverter kit's Lean check (research/circuit/inverter/instances, kit d599300d) with Lean 4.35.0.

| path (under ~/yieldK06/out) | size (bytes) | sha256 |
|---|---|---|
| NOT1_6220/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| NOT1_6220/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| NOT1_6220/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| NOT1_6220/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| NOT1_6220/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| NOT1_6220/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| NOT1_6220/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| NOT1_6220/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| NOT1_6220/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| XOR3_6166/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| XOR3_6166/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| XOR3_6166/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| XOR3_6166/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| XOR3_6166/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| XOR3_6166/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| XOR3_6166/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| XOR3_6166/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| XOR3_6166/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| XOR3_6190/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| XOR3_6190/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| XOR3_6190/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| XOR3_6190/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| XOR3_6190/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| XOR3_6190/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| XOR3_6190/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| XOR3_6190/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| XOR3_6190/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |

### pdk symlinks (33; regenerable, not archived)

Each points to the SKY130 primitive models checkout (skywater-pdk-libs-sky130_fd_pr at 1232782c1b9fab3aacda74d67ce7c92bf7da8105, from research/circuit/fetch_pdk.sh).

| path (under ~/yieldK06/out) | target |
|---|---|
| ANDOR3_6123/D/pdk | /home/user/kernel-R/research/circuit/pdk |
| ANDOR3_6150/D/pdk | /home/user/kernel-R/research/circuit/pdk |
| NOT1_6220/D/pdk | /home/user/kernel-R/research/circuit/pdk |
| NOT1_6220/inv/n0/runs/6220/R1_absent/pdk | /root/yieldK06/kit/research/circuit/pdk |
| NOT1_6220/inv/n0/runs/6220/R2_present/pdk | /root/yieldK06/kit/research/circuit/pdk |
| NOT1_6220/inv/n0/runs/6220/R3_leak_above/pdk | /root/yieldK06/kit/research/circuit/pdk |
| NOT1_6220/inv/n0/runs/6220/R4_leak_below/pdk | /root/yieldK06/kit/research/circuit/pdk |
| NOT1_6220/inv/n0/runs/6220/R5_static/pdk | /root/yieldK06/kit/research/circuit/pdk |
| NOT1_6220/inv/network_op/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/D/pdk | /home/user/kernel-R/research/circuit/pdk |
| XOR3_6166/inv/n0/runs/6166/R1_absent/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n0/runs/6166/R2_present/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n0/runs/6166/R3_leak_above/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n0/runs/6166/R4_leak_below/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n0/runs/6166/R5_static/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n1/runs/6166/R1_absent/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n1/runs/6166/R2_present/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n1/runs/6166/R3_leak_above/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n1/runs/6166/R4_leak_below/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/n1/runs/6166/R5_static/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6166/inv/network_op/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/D/pdk | /home/user/kernel-R/research/circuit/pdk |
| XOR3_6190/inv/n0/runs/6190/R1_absent/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n0/runs/6190/R2_present/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n0/runs/6190/R3_leak_above/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n0/runs/6190/R4_leak_below/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n0/runs/6190/R5_static/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n1/runs/6190/R1_absent/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n1/runs/6190/R2_present/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n1/runs/6190/R3_leak_above/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n1/runs/6190/R4_leak_below/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/n1/runs/6190/R5_static/pdk | /root/yieldK06/kit/research/circuit/pdk |
| XOR3_6190/inv/network_op/pdk | /root/yieldK06/kit/research/circuit/pdk |

## How to recover

```
git init -q x && cd x
git fetch -q https://github.com/HevisNico/kernel-R refs/heads/archive/combined-campaign-stop/K06-local
git checkout -q FETCH_HEAD
cd archive/combined-campaign-stop/K06-local && sha256sum -c SHA256SUMS
```
Merge `yieldK06/out/` over a checkout of evidence/yield-lot-K06's `research/layered-networks/dev/yield_lot/results/K06/` to get the OUTROOT back without its Lean build and pdk links; relink pdk and rerun the kit's Lean check to regenerate those.
