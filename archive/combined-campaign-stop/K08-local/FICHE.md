# K08 local archive (combined campaign stopped 2026-11-28)

## Provenance

- Machine: K08 (cloud container, 4 cores), Claude Code session `session_01TzF7ZYar4UYeXi8MMHMipK`.
- Source directory: `~/yieldK08/out` (/root/yieldK08/out), the OUTROOT of the K08 yield lot, stage D only, under
  `research/layered-networks/YIELD_LOT_RULE_2.md` (da23523), code at 70a0f66b, dev seeds, counts for nothing.
  Run 2026-11-25 06:07–07:52 UTC, 5/5 instances done (ANDOR3_6129, ANDOR3_6152, NOT1_6225, XOR3_6174, XOR3_6193).
- Related published branch: `evidence/yield-lot-K08`, tip 9c818fdc55ec4ac75d59e9ac8c1df25b25e87a04, folder
  `research/layered-networks/dev/yield_lot/results/K08` (every JSON, SHA256SUMS, INVENTORY, DONE, log and every
  SHA256SUMS-listed file of the OUTROOT).
- Other K08 sources were checked and hold nothing unpublished beyond what is named below: the rehearsal OUTROOT
  `~/reh/out_K08` is entirely on `evidence/combined-rehearsal-K08` (e880d80f, large file as transport parts; only the
  driver's local `.seal_log_work/.git`, whose commits equal `evidence/combined-seals-K08` tip 517f8fb, is not there).

## Archived items (under `yieldK08/out/`)

State: raw files of a completed yield-lot stage-D run, unchanged copies (`cp -p`).
Why never published: the yield-lot runbook's step-10 copy rule took only `*.json`, `SHA256SUMS`, `INVENTORY_*`,
`DONE` and `*.log` under 2 MB, excluding `session.log` and `runs/`, plus every SHA256SUMS-listed file. These files
matched none of these.

- `<inst>/D/session.log`: the ngspice session log of each stage-D run (the only content that cannot be regenerated).
- `<inst>/D/input.spice`, `<inst>/deck.spice`, `<inst>/D/blocks.spice`, `<inst>/D/.spiceinit`: the deck and its
  inputs beside each log (regenerable from the pinned code with `stage_d5.py deck`, kept so each log has its inputs).
- `DRIVER_PID`: the driver's pid file.

Recovery: fetch `archive/combined-campaign-stop/K08-local` by name, `cd archive/combined-campaign-stop/K08-local &&
sha256sum -c SHA256SUMS`, then copy `yieldK08/out/*` back over a checkout of `evidence/yield-lot-K08`'s results folder
or a fresh OUTROOT. No file is split (none exceeds 50,000,000 bytes).

## Regenerable, not archived

Lean `.olean` build products of the inverter gate (`<inst>/inv/lean_build/`), rebuilt by the run from the pinned Lean
sources (size, sha256, path):

- 274296 d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 yieldK08/out/NOT1_6225/inv/lean_build/CircuitInverterGate.olean
- 137424 f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 yieldK08/out/NOT1_6225/inv/lean_build/InverterInstanceTiming.olean
- 124416 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 yieldK08/out/NOT1_6225/inv/lean_build/InverterTarget.olean
- 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 yieldK08/out/NOT1_6225/inv/lean_build/MonotoneOneSidedTarget.olean
- 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a yieldK08/out/NOT1_6225/inv/lean_build/MonotoneSupport.olean
- 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 yieldK08/out/NOT1_6225/inv/lean_build/MonotoneTarget.olean
- 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 yieldK08/out/NOT1_6225/inv/lean_build/Target.olean
- 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 yieldK08/out/NOT1_6225/inv/lean_build/TwoLayerTarget.olean
- 48208 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 yieldK08/out/NOT1_6225/inv/lean_build/TwoRailsTarget.olean
- 274296 d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 yieldK08/out/XOR3_6174/inv/lean_build/CircuitInverterGate.olean
- 137424 f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 yieldK08/out/XOR3_6174/inv/lean_build/InverterInstanceTiming.olean
- 124416 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 yieldK08/out/XOR3_6174/inv/lean_build/InverterTarget.olean
- 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 yieldK08/out/XOR3_6174/inv/lean_build/MonotoneOneSidedTarget.olean
- 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a yieldK08/out/XOR3_6174/inv/lean_build/MonotoneSupport.olean
- 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 yieldK08/out/XOR3_6174/inv/lean_build/MonotoneTarget.olean
- 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 yieldK08/out/XOR3_6174/inv/lean_build/Target.olean
- 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 yieldK08/out/XOR3_6174/inv/lean_build/TwoLayerTarget.olean
- 48208 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 yieldK08/out/XOR3_6174/inv/lean_build/TwoRailsTarget.olean
- 274296 d4f4402594acfd7620862a8047a92be7e7976cd55d88e668959d349b1b805898 yieldK08/out/XOR3_6193/inv/lean_build/CircuitInverterGate.olean
- 137424 f2e8f6a7b3baf543f9919bae797c0db2c2a621219689fc0ce6789ceb29e46165 yieldK08/out/XOR3_6193/inv/lean_build/InverterInstanceTiming.olean
- 124416 961ae03c418411629be01aa633e78e4c0fcdabab8a1f15ee58b6adbce23bd223 yieldK08/out/XOR3_6193/inv/lean_build/InverterTarget.olean
- 46112 cac184d040630f1e4ad4ed06465f1eb208502b7badb8b51c4c37130a45215967 yieldK08/out/XOR3_6193/inv/lean_build/MonotoneOneSidedTarget.olean
- 117960 bf65f320d332f76f8209be7e8bf1547d5de2f0997ba1f38f58ea20a82a1f3c8a yieldK08/out/XOR3_6193/inv/lean_build/MonotoneSupport.olean
- 731064 d9e549231d1d2814cd84136d587ddfb7147ca99ec75148068c33ad5c97e17277 yieldK08/out/XOR3_6193/inv/lean_build/MonotoneTarget.olean
- 481032 10fcc53ffe8ab1b673010a53ac39f0d632490972687c1248b7ce63dafcad9d72 yieldK08/out/XOR3_6193/inv/lean_build/Target.olean
- 498368 2f3ca34cfcb9743514d6cefacb0322df1301797b251e386bb3f98b617a166267 yieldK08/out/XOR3_6193/inv/lean_build/TwoLayerTarget.olean
- 48208 706b0ab32daf84e9dcdae4fbc8d7b51792f4aa023093ac96e7e8c81c4c8a79d3 yieldK08/out/XOR3_6193/inv/lean_build/TwoRailsTarget.olean

The `pdk` symlinks in the OUTROOTs and worktrees (they point to the public SKY130 primitive models clone at
1232782c1b9fab3aacda74d67ce7c92bf7da8105).

Test (c) scratch folders (the test's own clones, worktrees and local bare seal repositories; by design only
TEST_C.json, c.log, envcheck.out and COMMIT were published, on evidence/devtest-K08, -run2-K08, -run3-K08, -run4-K08):

- ~/devtest_c: 1194832802 bytes, 84166 files
- ~/devtest_c2: 1195064901 bytes, 84172 files
- ~/devtest_c3: 1196156853 bytes, 84237 files
- ~/devtest_c4: 1196174145 bytes, 84237 files
