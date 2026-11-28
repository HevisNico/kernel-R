# K09 local archive lot (combined campaign stop, 2026-11-28)

## Provenance

- Machine: K09 (cloud session session_01TzF7ZYG7BYyVuQEG8JDatU).
- Requested by the combined campaign's coordinator (session_01TzF7ZUoTUj44AGYGuEFzHA) after the campaign stopped,
  under the owner's approval of one small archive lot per machine.
- Source directory: `/root/yieldK09/out`, the OUTROOT of the yield lot run on K09 (stage D, YIELD_LOT_RULE_2,
  code at 70a0f66b18ad5b7937eea6a7388a191055c68f97, run 2026-11-25 06:07–07:18 UTC). Dev seeds; counts for no claim.
- Related published branch: `evidence/yield-lot-K09`, tip `99bdbcbb67d5e511aa76dfab30a0b7918aa21baa`
  (results under `research/layered-networks/dev/yield_lot/results/K09/`).
- Other K09 work, already fully published and not repeated here:
  - rehearsal root on `evidence/combined-rehearsal-K09`, tip `4d2f1377fddb79300c72035b43c5a96252e7b967`;
  - seals on `evidence/combined-seals-K09`, tip `c644f542969ed39eefd91ac0c82dac9a597e731d`;
  - test (c) records on `evidence/devtest-K09` (52ada95b), `evidence/devtest-run2-K09` (34f0044a),
    `evidence/devtest-run3-K09` (bfed163e) and `evidence/devtest-run4-K09` (8f052b02).

## State and why these files were never published

Every file below is a raw file of a COMPLETED yield-lot run: all 4 stage-D jobs ended DONE, with 0 failed.
- The four `D/session.log` files are ngspice session logs.
- The `deck.spice` and `D/input.spice` files are the decks those sessions ran.
- `D/.spiceinit` and `D/blocks.spice` are their setup files.
- `DRIVER_PID` is the driver's pid file.

They were left off `evidence/yield-lot-K09` by the runbook's copy rule. Step 10 copied only `*.json`, `SHA256SUMS`,
`INVENTORY_*`, `DONE` and `*.log` files under 2 MB, and excluded `session.log`, `*/runs/*` and `*lean_build*`. A
later commit added only the files listed in a SHA256SUMS. None of these files is listed there, and no published
checksum covers them. They are archived here so that the logs keep their inputs beside them.

## Archived files (path under this folder, size in bytes, sha256)

- `yieldK09/out/DRIVER_PID` 4 `2fbfe464fac08a6c55d7a68a1006c3eb6b113d76bc494647d387a33de306e899`
- `yieldK09/out/ANDOR3_6153/deck.spice` 134862 `3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b`
- `yieldK09/out/ANDOR3_6153/D/input.spice` 134862 `3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b`
- `yieldK09/out/ANDOR3_6153/D/.spiceinit` 71 `ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1`
- `yieldK09/out/ANDOR3_6153/D/blocks.spice` 2212 `7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd`
- `yieldK09/out/ANDOR3_6153/D/session.log` 766453 `aa0139b7518d4d3dcacf0133b8379a1a82088eada3cf4a4897928d72ad46742d`
- `yieldK09/out/XOR3_6175/deck.spice` 144904 `28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e`
- `yieldK09/out/XOR3_6175/D/input.spice` 144904 `28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e`
- `yieldK09/out/XOR3_6175/D/.spiceinit` 71 `ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1`
- `yieldK09/out/XOR3_6175/D/blocks.spice` 2212 `7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd`
- `yieldK09/out/XOR3_6175/D/session.log` 879742 `9e8c381e0d02f44bd2756922fca3f57a29943940fbf99a009983167e6ddbdcc2`
- `yieldK09/out/ANDOR3_6130/deck.spice` 134862 `3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b`
- `yieldK09/out/ANDOR3_6130/D/input.spice` 134862 `3afd629f4aae973b5a357069fd52ba3c01d65b64f7a1bce14d0d95b1e033364b`
- `yieldK09/out/ANDOR3_6130/D/.spiceinit` 71 `ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1`
- `yieldK09/out/ANDOR3_6130/D/blocks.spice` 2212 `7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd`
- `yieldK09/out/ANDOR3_6130/D/session.log` 828215 `1f0350702eb3134a004634b10dd8bb0aa6c965a114572b0a0da8df84bc56a274`
- `yieldK09/out/XOR3_6196/deck.spice` 144904 `28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e`
- `yieldK09/out/XOR3_6196/D/input.spice` 144904 `28b8df4502b93e7a73ebd3ba6553f1d60e8fb46669029e0a2db58359a7301c9e`
- `yieldK09/out/XOR3_6196/D/.spiceinit` 71 `ceb0f22c2f12fc545406534ab6801716f61caed2cf3fed03d7f5c7fb193a4bb1`
- `yieldK09/out/XOR3_6196/D/blocks.spice` 2212 `7677efdb277d837937c28b13d807448a433d19019fc550c81e0c8d3234bfd1bd`
- `yieldK09/out/XOR3_6196/D/session.log` 857988 `255734912426d289d62eeb9575b606d385b3edfc7fb49f660f11b769bb1bece0`

## Excluded: regenerable, not archived

The Lean build products (`.olean`) are rebuilt by the kit from its pinned Lean sources (Lean 4.35.0):
- `yieldK09/out/XOR3_6175/inv/lean_build/InverterTarget.olean` 124416 `961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223`
- `yieldK09/out/XOR3_6175/inv/lean_build/Target.olean` 481032 `10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72`
- `yieldK09/out/XOR3_6175/inv/lean_build/TwoRailsTarget.olean` 48208 `706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3`
- `yieldK09/out/XOR3_6175/inv/lean_build/MonotoneTarget.olean` 731064 `d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277`
- `yieldK09/out/XOR3_6175/inv/lean_build/TwoLayerTarget.olean` 498368 `2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267`
- `yieldK09/out/XOR3_6175/inv/lean_build/MonotoneOneSidedTarget.olean` 46112 `cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967`
- `yieldK09/out/XOR3_6175/inv/lean_build/InverterInstanceTiming.olean` 137424 `f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165`
- `yieldK09/out/XOR3_6175/inv/lean_build/CircuitInverterGate.olean` 274296 `d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898`
- `yieldK09/out/XOR3_6175/inv/lean_build/MonotoneSupport.olean` 117960 `bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a`
- `yieldK09/out/XOR3_6196/inv/lean_build/InverterTarget.olean` 124416 `961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223`
- `yieldK09/out/XOR3_6196/inv/lean_build/Target.olean` 481032 `10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72`
- `yieldK09/out/XOR3_6196/inv/lean_build/TwoRailsTarget.olean` 48208 `706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3`
- `yieldK09/out/XOR3_6196/inv/lean_build/MonotoneTarget.olean` 731064 `d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277`
- `yieldK09/out/XOR3_6196/inv/lean_build/TwoLayerTarget.olean` 498368 `2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267`
- `yieldK09/out/XOR3_6196/inv/lean_build/MonotoneOneSidedTarget.olean` 46112 `cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967`
- `yieldK09/out/XOR3_6196/inv/lean_build/InverterInstanceTiming.olean` 137424 `f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165`
- `yieldK09/out/XOR3_6196/inv/lean_build/CircuitInverterGate.olean` 274296 `d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898`
- `yieldK09/out/XOR3_6196/inv/lean_build/MonotoneSupport.olean` 117960 `bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a`

The `pdk` symlinks point to the SKY130 PDK at 1232782c1b9fab3aacda74d67ce7c92bf7da8105 (research/circuit/fetch_pdk.sh):
- `yieldK09/out/ANDOR3_6153/D/pdk` -> /home/user/kernel-R/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/network_op/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n1/runs/6175/R2_present/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n1/runs/6175/R5_static/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n1/runs/6175/R1_absent/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n1/runs/6175/R3_leak_above/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n1/runs/6175/R4_leak_below/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n0/runs/6175/R2_present/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n0/runs/6175/R5_static/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n0/runs/6175/R1_absent/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n0/runs/6175/R3_leak_above/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/inv/n0/runs/6175/R4_leak_below/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6175/D/pdk` -> /home/user/kernel-R/research/circuit/pdk
- `yieldK09/out/ANDOR3_6130/D/pdk` -> /home/user/kernel-R/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/network_op/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n1/runs/6196/R2_present/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n1/runs/6196/R5_static/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n1/runs/6196/R1_absent/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n1/runs/6196/R3_leak_above/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n1/runs/6196/R4_leak_below/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n0/runs/6196/R2_present/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n0/runs/6196/R5_static/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n0/runs/6196/R1_absent/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n0/runs/6196/R3_leak_above/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/inv/n0/runs/6196/R4_leak_below/pdk` -> /root/yieldK09/kit/research/circuit/pdk
- `yieldK09/out/XOR3_6196/D/pdk` -> /home/user/kernel-R/research/circuit/pdk

The test (c) scratch folders: by design only their records were published (TEST_C.json, c.log and envcheck.out, on
the devtest branches above). The test recreates them on any run:
- `~/devtest_c/c` 542839852 bytes, 35818 files
- `~/devtest_c2/c` 542908323 bytes, 35820 files
- `~/devtest_c3/c` 543239008 bytes, 35832 files
- `~/devtest_c4/c` 543251529 bytes, 35832 files

## How to recover

    git fetch https://github.com/HevisNico/kernel-R refs/heads/archive/combined-campaign-stop/K09-local
    git checkout FETCH_HEAD -- archive/combined-campaign-stop/K09-local
    cd archive/combined-campaign-stop/K09-local && sha256sum -c SHA256SUMS

Put `yieldK09/out/...` back beside the published results of `evidence/yield-lot-K09`. Each path mirrors its place in
the run's OUTROOT. No file here is split; all are under 50,000,000 bytes.
