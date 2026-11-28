# K10 local archive lot (combined campaign stop, 2026-11-28)

## Provenance
- Machine: K10 (campaign machine), Claude Code session session_01TzF7ZUE4JRLnFVJpS5aeLA.
- Source directory: `~/yieldK10/out` (the yield-lot OUTROOT of machine K10, stage D only, YIELD_LOT_RULE_2).
- Published counterpart: `evidence/yield-lot-K10` at `37c9d0de` (first commit b09a75fa, second commit 37c9d0de with the files listed in SHA256SUMS).
- These files are copies; the originals were not changed, moved or deleted.

## Items (under `yieldK10/out/`)
| Path | State | Why never published | How to recover |
|---|---|---|---|
| `ANDOR3_6131/D/session.log`, `ANDOR3_6154/D/session.log`, `XOR3_6177/D/session.log`, `XOR3_6202/D/session.log` | Raw ngspice pipe log of a completed stage-D run of the yield lot (run ended DONE on 2026-11-25) | The runbook's copy rule (step 10) excluded `session.log` (`-not -name session.log`), and no SHA256SUMS lists it | This lot; or re-run stage D at 70a0f66b with the same plan (`PLAN_K10.json` on evidence/yield-lot-K10) |
| `XOR3_6177/deck.spice`, `XOR3_6177/D/input.spice`, `XOR3_6202/deck.spice`, `XOR3_6202/D/input.spice` | The SPICE deck of a completed yield-lot run (all four are byte-identical) | The copy rule kept only `*.json`, SHA256SUMS, INVENTORY_*, DONE and `*.log`; `.spice` was not kept, and no SHA256SUMS lists it | This lot; or regenerate with the deck builder at 70a0f66b for the same instance |
| `DRIVER_PID` | The pid of the yield-lot driver process (operational only) | Not matched by the copy rule | This lot; it has no meaning outside that run |

## Regenerable, not archived
- Test (c) scratch folders: `~/devtest_c` 1.4G, `~/devtest_c_run2` 1.4G, `~/devtest_c3` 1.4G, `~/devtest_c4` 1.4G. Their TEST_C.json, c.log, envcheck.out and COMMIT are on evidence/devtest-K10 and devtest-run2/3/4-K10. Not hashed.
- Lean `.olean` build products: 18 in `~/yieldK10/out` (39 counting `~/reh/out_K10`).
- `pdk` symlinks to the SKY130 PDK at 1232782c: 26 in `~/yieldK10/out` (59 counting `~/reh`).

## Integrity
`SHA256SUMS` in this folder covers every file of the lot except itself. Check with `sha256sum -c SHA256SUMS` from this folder.
