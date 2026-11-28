# Local-only files: K07

## Provenance

- Machine: K07
- Session: session_01TzF7ZX8H83BpXXaEaC2x7C
- Source directories on K07:
  - ~/yieldK07/out, the yield lot's OUTROOT;
  - ~/devtest_c, ~/devtest_c2, ~/devtest_c3, ~/devtest_c4, the test (c) work folders.
- Published counterparts:
  - evidence/yield-lot-K07 at 7a9b888 (under research/layered-networks/dev/yield_lot/results/K07);
  - evidence/devtest-K07 at 05a9696;
  - evidence/devtest-run2-K07 at 6256ef5;
  - evidence/devtest-run3-K07 at 4ef2f62;
  - evidence/devtest-run4-K07 at 092ffca.
- Paths below are relative to this folder. yieldK07/out/<path> is ~/yieldK07/out/<path> on K07, and devtest_cN/c.rc is ~/devtest_cN/c.rc.

## Items archived

- `devtest_c/c.rc`, 5 bytes
- `devtest_c2/c.rc`, 5 bytes
- `devtest_c3/c.rc`, 5 bytes
- `devtest_c4/c.rc`, 5 bytes
- `yieldK07/out/ANDOR3_6125/D/.spiceinit`, 71 bytes
- `yieldK07/out/ANDOR3_6125/D/blocks.spice`, 2212 bytes
- `yieldK07/out/ANDOR3_6125/D/input.spice`, 134862 bytes
- `yieldK07/out/ANDOR3_6125/D/session.log`, 815553 bytes
- `yieldK07/out/ANDOR3_6125/deck.spice`, 134862 bytes
- `yieldK07/out/ANDOR3_6151/D/.spiceinit`, 71 bytes
- `yieldK07/out/ANDOR3_6151/D/blocks.spice`, 2212 bytes
- `yieldK07/out/ANDOR3_6151/D/input.spice`, 134862 bytes
- `yieldK07/out/ANDOR3_6151/D/session.log`, 747962 bytes
- `yieldK07/out/ANDOR3_6151/deck.spice`, 134862 bytes
- `yieldK07/out/DRIVER_PID`, 4 bytes
- `yieldK07/out/NOT1_6223/D/.spiceinit`, 71 bytes
- `yieldK07/out/NOT1_6223/D/blocks.spice`, 2212 bytes
- `yieldK07/out/NOT1_6223/D/input.spice`, 39616 bytes
- `yieldK07/out/NOT1_6223/D/session.log`, 92142 bytes
- `yieldK07/out/NOT1_6223/deck.spice`, 39616 bytes
- `yieldK07/out/XOR3_6173/D/.spiceinit`, 71 bytes
- `yieldK07/out/XOR3_6173/D/blocks.spice`, 2212 bytes
- `yieldK07/out/XOR3_6173/D/input.spice`, 144904 bytes
- `yieldK07/out/XOR3_6173/D/session.log`, 841115 bytes
- `yieldK07/out/XOR3_6173/deck.spice`, 144904 bytes
- `yieldK07/out/XOR3_6192/D/.spiceinit`, 71 bytes
- `yieldK07/out/XOR3_6192/D/blocks.spice`, 2212 bytes
- `yieldK07/out/XOR3_6192/D/input.spice`, 144904 bytes
- `yieldK07/out/XOR3_6192/D/session.log`, 752529 bytes
- `yieldK07/out/XOR3_6192/deck.spice`, 144904 bytes

## State and reason

- **yieldK07/out/\*/D/session.log:** raw logs of a completed yield-lot run (stage D, dev seeds, counts for nothing). They are ngspice's full pipe output for each instance's stage-D session.
- **yieldK07/out/\*/D/input.spice, \*/deck.spice, \*/D/.spiceinit, \*/D/blocks.spice:** the decks and simulator inputs of that run. deck.spice and D/input.spice are byte-identical within each instance.
- **yieldK07/out/DRIVER_PID:** the driver's pid file.
- **devtest_cN/c.rc:** the exit status of each test (c) call, as written by the wrapper on K07. devtest_c3 holds rc=1, its analysis_refuses failure; the other three hold rc=0.

None of these files was published, because of the runbooks' copy rules:
- the yield-lot runbook (step 10) copied only *.json, SHA256SUMS, INVENTORY_*, DONE and *.log files under 2 MB, and excluded session.log by name;
- the follow-up copy added only the files that a SHA256SUMS lists;
- the test (c) runbook (step 5) copied only TEST_C.json, c.log and envcheck.out.

## Recovery

Fetch this branch by name and run `sha256sum -c SHA256SUMS` in this folder. Then copy each file back to its source path, for example yieldK07/out/ANDOR3_6125/D/session.log to ~/yieldK07/out/ANDOR3_6125/D/session.log.

## Regenerable, not archived

- `.olean` files: 27 files, 7376640 bytes in all, under ~/yieldK07/out/*/inv/lean_build/. They are Lean build output, rebuilt from the pinned sources.
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/CircuitInverterGate.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/InverterInstanceTiming.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/InverterTarget.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/MonotoneOneSidedTarget.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/MonotoneSupport.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/MonotoneTarget.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/Target.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/TwoLayerTarget.olean`
  - `~/yieldK07/out/NOT1_6223/inv/lean_build/TwoRailsTarget.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/CircuitInverterGate.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/InverterInstanceTiming.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/InverterTarget.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/MonotoneOneSidedTarget.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/MonotoneSupport.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/MonotoneTarget.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/Target.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/TwoLayerTarget.olean`
  - `~/yieldK07/out/XOR3_6173/inv/lean_build/TwoRailsTarget.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/CircuitInverterGate.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/InverterInstanceTiming.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/InverterTarget.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/MonotoneOneSidedTarget.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/MonotoneSupport.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/MonotoneTarget.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/Target.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/TwoLayerTarget.olean`
  - `~/yieldK07/out/XOR3_6192/inv/lean_build/TwoRailsTarget.olean`
- pdk symlinks: research/circuit/pdk in the clones and worktrees. They are links to the SKY130 PDK at 1232782c, fetched by research/circuit/fetch_pdk.sh.
- test (c) scratch folders. They are rebuilt by running test (c) at the same commit.
  - ~/devtest_c/c: 2,356,311,173 bytes, 110,008 files;
  - ~/devtest_c2/c: 2,185,258,324 bytes, 109,375 files;
  - ~/devtest_c3/c: 2,186,617,392 bytes, 109,420 files;
  - ~/devtest_c4/c: 2,186,876,977 bytes, 109,428 files.
