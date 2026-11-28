# Archive lot K05-local (combined campaign stop, 2026-11-28)

## Provenance
- Machine: K05 (cloud container), Claude Code session session_01TzF7ZVvhaVoFBq55SMmF5F.
- Source directory: `/root/yieldK05/out` (the YIELD LOT run, stage D only, under research/layered-networks/YIELD_LOT_RULE_2.md; code at 70a0f66b18ad5b7937eea6a7388a191055c68f97, kit d599300d, controls e15b494a; 5 dev seeds: ANDOR3 6110, 6147; NOT1 6219; XOR3 6165, 6187; run 2026-11-25 06:07 to 07:19 UTC, ENDED DONE, 0 failed).
- Related evidence branch: `evidence/yield-lot-K05`, tip 7f891314af0e489bcaba140120f7ae7b73ae95fd (commits 411e9dca results, 7f891314 inverter run files listed in SHA256SUMS).
- Copied here as `yieldK05_out/`: every regular file of that directory except the Lean build products (relative paths kept). Copies only; nothing was moved or deleted on the machine.
- Other K05 work directories are fully published and are not repeated here: `/root/reh/out_K05` (evidence/combined-rehearsal-K05 a89a60b1, evidence/combined-seals-K05 93572ab5), `/root/devtest_b2/out_K05` (evidence/devtest-run2-K05 a4cbddc8, evidence/devtest-seals2-K05 80f2c0f5), `/root/devtest_b_discarded_a8303e8e/out_K05` (evidence/devtest-K05 7b13a91b, evidence/devtest-seals-K05 86377a55). `/root/reh/inputs` holds DRAW.json (same bytes as evidence/combined-rehearsal-draw-result) and the 12 plans plan_split3.py derives from it: regenerable, not archived.

## Items
- **Only here before this lot** (never on any evidence branch): `XOR3_6165/D/session.log`, `XOR3_6187/D/session.log`, `ANDOR3_6110/D/session.log`, `ANDOR3_6147/D/session.log`, `NOT1_6219/D/session.log`, `ANDOR3_6110/deck.spice`, `ANDOR3_6110/D/input.spice`, `ANDOR3_6147/deck.spice`, `ANDOR3_6147/D/input.spice`, `DRIVER_PID`.
  - State: raw logs (ngspice session transcripts) and SPICE inputs of completed yield-lot stage-D runs; DRIVER_PID is the driver's process id.
  - Why never published: the yield-lot runbook's copy rule (step 10) kept only `*.json`, `SHA256SUMS`, `INVENTORY_*`, `DONE` and `*.log` under 2 MB, explicitly excluding `session.log` and `runs/`; the later coordinator addition published only files listed in a SHA256SUMS. None of these is listed in one.
- **Also included, already published byte for byte** (kept so the logs have their inputs and context beside them): the other JSON, log, SHA256SUMS, INVENTORY, DONE and SPICE input files of the same folders (`blocks.spice`, `.spiceinit`, `input.spice` and the inverter `runs/` inputs).

## Excluded (regenerable, not archived)
| Path | Size / target | sha256 / commit | Note |
|---|---|---|---|
| yieldK05_out/NOT1_6219/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 | regenerable, not archived (Lean build product) |
| yieldK05_out/NOT1_6219/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6165/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/CircuitInverterGate.olean | 274296 | d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/InverterInstanceTiming.olean | 137424 | f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/InverterTarget.olean | 124416 | 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/MonotoneOneSidedTarget.olean | 46112 | cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/MonotoneSupport.olean | 117960 | bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/MonotoneTarget.olean | 731064 | d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/Target.olean | 481032 | 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/TwoLayerTarget.olean | 498368 | 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 | regenerable, not archived (Lean build product) |
| yieldK05_out/XOR3_6187/inv/lean_build/TwoRailsTarget.olean | 48208 | 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 | regenerable, not archived (Lean build product) |
| yieldK05_out/ANDOR3_6110/D/pdk | symlink -> /home/user/kernel-R/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/ANDOR3_6147/D/pdk | symlink -> /home/user/kernel-R/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/D/pdk | symlink -> /home/user/kernel-R/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/inv/n0/runs/6219/R1_absent/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/inv/n0/runs/6219/R2_present/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/inv/n0/runs/6219/R3_leak_above/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/inv/n0/runs/6219/R4_leak_below/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/inv/n0/runs/6219/R5_static/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/NOT1_6219/inv/network_op/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/D/pdk | symlink -> /home/user/kernel-R/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n0/runs/6165/R1_absent/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n0/runs/6165/R2_present/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n0/runs/6165/R3_leak_above/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n0/runs/6165/R4_leak_below/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n0/runs/6165/R5_static/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n1/runs/6165/R1_absent/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n1/runs/6165/R2_present/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n1/runs/6165/R3_leak_above/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n1/runs/6165/R4_leak_below/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/n1/runs/6165/R5_static/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6165/inv/network_op/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/D/pdk | symlink -> /home/user/kernel-R/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n0/runs/6187/R1_absent/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n0/runs/6187/R2_present/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n0/runs/6187/R3_leak_above/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n0/runs/6187/R4_leak_below/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n0/runs/6187/R5_static/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n1/runs/6187/R1_absent/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n1/runs/6187/R2_present/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n1/runs/6187/R3_leak_above/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n1/runs/6187/R4_leak_below/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/n1/runs/6187/R5_static/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |
| yieldK05_out/XOR3_6187/inv/network_op/pdk | symlink -> /root/yieldK05/kit/research/circuit/pdk | SKY130 PDK git commit 1232782c1b9fab3aacda74d67ce7c92bf7da8105 | regenerable, not archived (pdk symlink; fetch_pdk.sh) |

## How to recover
```
git init -q a && cd a
git fetch https://github.com/HevisNico/kernel-R refs/heads/archive/combined-campaign-stop/K05-local
git checkout FETCH_HEAD -- .
cd archive/combined-campaign-stop/K05-local && sha256sum -c SHA256SUMS
```
Paths under `yieldK05_out/` are relative to the original `/root/yieldK05/out`. The excluded Lean products are rebuilt by the package's own Lean build; the pdk links point to the SKY130 models at 1232782c (research/circuit/fetch_pdk.sh).
