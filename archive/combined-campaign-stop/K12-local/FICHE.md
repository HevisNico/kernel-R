# K12 local archive lot (combined campaign stop, 2026-11-28)

## Provenance
- Machine: K12 (campaign machine of HevisNico/kernel-R). Claude Code session: session_01TzF7ZXJghFFkLtmKA2yktJ.
- Requested by the campaign coordinator (session_01TzF7ZUoTUj44AGYGuEFzHA) after the campaign stop of 2026-11-28.
- Source directory: `~/yieldK12/out` on K12 (the OUTROOT of the yield lot, stage D only, YIELD_LOT_RULE_2 at research/layered-stage-d 70a0f66b).
- Related evidence branch: `evidence/yield-lot-K12`, tip 2441dcc9f604dd9919c76cd59c7457418b68c219 (results under research/layered-networks/dev/yield_lot/results/K12).
- Other K12 branches, complete and not concerned by this lot: evidence/combined-rehearsal-K12 (c1a9cc66), evidence/combined-seals-K12 (3a8ca5e), evidence/devtest-K12 (a06f72b6), evidence/devtest-run2-K12 (a7118476), evidence/devtest-run3-K12 (9832c5a1), evidence/devtest-run4-K12 (636b5da6).

## Items archived (under `yieldK12_out/`, paths relative to the OUTROOT)
- `<inst>/D/session.log` (4 files): the raw ngspice session log of a COMPLETED stage-D run of the yield lot (instances ANDOR3_6135, ANDOR3_6156, XOR3_6179, XOR3_6204; all 4 runs ended DONE, 0 failed).
- `<inst>/D/input.spice`, `<inst>/D/blocks.spice`, `<inst>/D/.spiceinit`, `<inst>/deck.spice` (16 files): the exact simulator inputs of those runs, kept beside their logs.
- `DRIVER_PID` (1 file): the pid file of the yield-lot driver.
- Why never published: the yield-lot runbook's step 10 copy rule took only `*.json`, `SHA256SUMS`, `INVENTORY_*`, `DONE` and `*.log` under 2 MB, explicitly excluding `session.log`, `*/runs/*` and the PDK; the later "files listed in SHA256SUMS" addition (2441dcc) covered only files named in a SHA256SUMS. These files were in neither set.
- How to recover: fetch this branch by name (`git fetch origin refs/heads/archive/combined-campaign-stop/K12-local`), check out, then `cd archive/combined-campaign-stop/K12-local && sha256sum -c SHA256SUMS`. Each file maps one-to-one to `~/yieldK12/out/<same path>` on K12. No file was split (all are under 50,000,000 bytes).

## Excluded: regenerable, not archived
### Lean .olean build products (yield-lot inverter gates), path / size / sha256
| path | bytes | sha256 |
|---|---|---|
| yieldK12/out/XOR3_6179/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| yieldK12/out/XOR3_6179/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| yieldK12/out/XOR3_6179/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| yieldK12/out/XOR3_6179/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| yieldK12/out/XOR3_6179/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| yieldK12/out/XOR3_6179/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| yieldK12/out/XOR3_6179/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| yieldK12/out/XOR3_6179/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| yieldK12/out/XOR3_6179/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |
| yieldK12/out/XOR3_6204/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 |
| yieldK12/out/XOR3_6204/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 |
| yieldK12/out/XOR3_6204/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 |
| yieldK12/out/XOR3_6204/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 |
| yieldK12/out/XOR3_6204/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a |
| yieldK12/out/XOR3_6204/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 |
| yieldK12/out/XOR3_6204/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 |
| yieldK12/out/XOR3_6204/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 |
| yieldK12/out/XOR3_6204/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 |

### PDK symlinks (point to the SKY130 PDK at 1232782c; links, not data)
- yieldK12/out/ANDOR3_6135/D/pdk (symlink to the SKY130 PDK)
- yieldK12/out/ANDOR3_6156/D/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/network_op/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n1/runs/6179/R2_present/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n1/runs/6179/R5_static/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n1/runs/6179/R1_absent/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n1/runs/6179/R3_leak_above/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n1/runs/6179/R4_leak_below/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n0/runs/6179/R2_present/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n0/runs/6179/R5_static/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n0/runs/6179/R1_absent/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n0/runs/6179/R3_leak_above/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/inv/n0/runs/6179/R4_leak_below/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6179/D/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/network_op/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n1/runs/6204/R2_present/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n1/runs/6204/R5_static/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n1/runs/6204/R1_absent/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n1/runs/6204/R3_leak_above/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n1/runs/6204/R4_leak_below/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n0/runs/6204/R2_present/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n0/runs/6204/R5_static/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n0/runs/6204/R1_absent/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n0/runs/6204/R3_leak_above/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/inv/n0/runs/6204/R4_leak_below/pdk (symlink to the SKY130 PDK)
- yieldK12/out/XOR3_6204/D/pdk (symlink to the SKY130 PDK)

### Test (c) scratch folders (by design only TEST_C.json, c.log and envcheck.out were published, on the devtest branches)
| path | size |
|---|---|
| devtest_c/c | 507054823 bytes, 35695 files |
| devtest_c_run2/c | 1267990037 bytes, 71898 files |
| devtest_c3/c | 1268636784 bytes, 71922 files |
| devtest_c4/c | 1268701662 bytes, 71922 files |
