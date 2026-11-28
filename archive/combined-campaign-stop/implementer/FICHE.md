# FICHE: implementer archive at the stop of the combined campaign (lot e2)

## Provenance

- Session: session_01TzF7ZVGjZjJcvQGoXk8dXp ("kernel-R: exact-union fix (implementer)"), created 2026-11-28T07:09Z,
  child of the coordinator session_01TzF7ZUoTUj44AGYGuEFzHA. Archive assembled 2026-11-28, about 13:30Z.
- Repository: https://github.com/HevisNico/kernel-R
- Work branch: research/layered-campaign-dev. Its remote tip when this archive was made:
  7fa3693ea85a85dde8490e0efdb9eafa80ff7189. The campaign is stopped before its draw: dev stays at that commit, with
  no new fix and no freeze.
- Base revision of this work: da3d9b3b1f22b312eab3a4aaa67d06abf47f2c45. Every commit below is on top of it.
- main when the work started: 3f27bb36dadd77a57e27b8fa80f81c3864a02b0e. It is the identity source for author and
  committer.
- Commits of this session, all pushed to research/layered-campaign-dev, oldest first. Each "pins" commit regenerates
  FREEZE_PINS.json (114 files) with dev/freeze/final/closure2.py and make_pins3.py; analysis.py is the only pinned
  file changed each time.
  - 72013e1311008b5b40089efad208a0d4582a5adc: the exact union, in the FREEZE.txt check blocks and analysis.py
  - a5ba132bc59e64b4eb6adcc01d107177d5fbe22b: pins
  - 372573e80c7bf33822421c9769cc84d52f9b2b40: announce formats /1 and /2; rehearsal 2's list exact in campaign mode
  - fe82ec0a36f53a3ee3db17fb6661d2233ebf23fb: pins
  - 46e08e09f1db6172f1a05ee25ed0bc5aa81ffe55: check_scan, [block verify-scan], scan_checks and verify_scan
  - 13ebca8b42fc74e56f6ea8e0e4fd1f356e4734cd: pins
  - 82dd9260019ecd67d0b4685f5b561406d9585b9e: scan_verify_record read by [block announce] and analysis.py campaign
  - a4c9e9c2dd3d3c1658f763f7fb55c915552ebe73: pins
  - 2530adda1c506b40e9947ddf85c1dc96504874a3: review nits N1 and N2
  - 0376d1360fa8d1705aa94e78d92031769b978150: pins
  - f20b3d8bc9c8a9a79966badd97a0d368e48fad86: VERIFY_INPUTS.txt
  - b6605c76fa396221028eef0b54a4d9a661dfcd6c: one shared reader of the scan verify record (review #3)
  - 7fa3693ea85a85dde8490e0efdb9eafa80ff7189: pins. analysis.py has sha256
    0c10b8b94bcb1bd414683528b26a92b50db7cb3ac2c824b0a73b83cd00b860f6; FREEZE_PINS.json has sha256
    6b9704cf3394db1ff577011f0fc460983fcddf852145daeff4df12876649eca3.
- Local state checked when this archive was made:
  - the only local branch is fix/exact-union, at 7fa3693e, which equals the remote;
  - `git stash list` is empty;
  - no commit is unpushed, so this archive has **no bundle**;
  - the only untracked item is research/circuit/pdk, a symlink to the local PDK (/home/user/pdk at 1232782c). It is
    never committed and not archived.
- Toolchain (env/envcheck.json, envcheck_layered4, ok):
  - python 3.13.18 and numpy 2.3.5, in the venv /home/user/venv;
  - lean 4.35.0 (binary sha256 bf8d54e4…);
  - ngspice sha256 82065831…;
  - PDK 1232782c.

## What is in this folder

- `runs/<run>/`: the never-committed result files of the test runs. They are copied as is from /tmp/claude-0/<run>/,
  keeping their relative paths: DEFECTS.json, defects.log, equiv_a.log, EQUIV_A.json, c.log and TEST_C.json. The case
  work folders, which hold the fixtures each test regenerates and are up to 4.6 GB per run, are left out.
- `env/envcheck.json`: the toolchain check.
- `scratch/`: drafts and tools from the session's scratchpads, never committed. Some are DRAFT; see below.

## Per item

How the SHA of each run is known:
- DEFECTS.json carries `tree_head` and `analysis_sha256`, and these match the committed analysis.py. This is measured.
- Where a run has no DEFECTS.json, its SHA is INFERRED: it is the HEAD of the moment the command started (commit times
  above, command times in the session transcript).

Commands, run in research/layered-networks with PATH including ~/.elan/bin and /home/user/venv/bin/python:
- defect suite: `tests/test_analysis_defects.py OUT.json`. Its sha256 a006114c… is recorded in DEFECTS.json; the file
  was never edited.
- test (a): `tests/equiv_campaign.py OUTDIR`. It needs the worktrees /home/user/kit (d599300d) and /home/user/noise
  (458bc7a6).
- test (c): `tests/test_campaign.py WORKDIR [cases]`.

### TESTED

| run | SHA | command | result (from the files) |
|---|---|---|---|
| runs | a5ba132b (tree_head, measured) | defect suite | 52 of 52 PASS, rc 0 |
| runa2 | a5ba132b (inferred) | test (a) | 24 cases, identical true, rc 0 |
| runc2 | a5ba132b (inferred) | test (c), all cases | 31 of 31 PASS, rc 0 |
| g2 | fe82ec0a (tree_head, measured) | defects and (a); (c) stopped | defects 52/52; (a) 24 identical; (c) 6 of 6 before it was stopped |
| g3 | 13ebca8b (tree_head, measured) | defects, (a), full (c) | 52/52; 24 identical; (c) 34 of 34, rc 0 |
| g6 | f20b3d8b (tree_head, measured) | defects, (a), full (c) | 52/52; 24 identical; (c) 35 of 35, rc 0 |
| g7 | 7fa3693e (tree_head, measured) | defects and (a) | 52/52, rc 0; 24 identical, rc 0 |
| tc12 | working tree whose code equals b6605c76 (pins not yet regenerated) | (c) on the 7 cases touched by review #3 | 7 of 7 PASS |

- At 7fa3693e the full test (c) was **NOT run**. The coordinator deferred it to the final SHA, and none came, because
  the campaign stopped.
- The scan verify record was tested only on a local twin: (c) cases verify_scan and scan_verify_record. It was never
  tested on GitHub.

### Stopped, superseded or failed runs (kept for completeness, not evidence of a pass)

- runa, a5ba132b (inferred): test (a), rc 1. The kit worktree was missing ("no clean worktree at kit_commit
  d599300d"). Fixed by fetching research/inverter-instances and research/layered-networks at depth 1, then rerun as
  runa2.
- runc, a5ba132b (inferred): full (c), killed by a container restart after 7 of 7 cases had passed. Rerun as runc2.
- g4, a4c9e9c2 (inferred): stopped when the review nits were committed. defects.log is truncated, with no
  DEFECTS.json; (a) has 24 identical.
- g5, 0376d136 (tree_head, measured): defects 52/52 and (a) 24 identical. (c) was stopped after 4 of 4, superseded by
  g6. The analysis.py of 0376d136 is the same as f20b3d8b's.
- tc1 to tc11: targeted (c) runs on uncommitted working trees while each change was being made. Each failure there was
  fixed before the next commit, and the later full runs above passed.

| run | about | on top of (inferred) | result |
|---|---|---|---|
| tc1 | 07:19 | da3d9b3b | 2/2 |
| tc3 | 09:07 | a5ba132b | 2/4 |
| tc4 | 09:08 | a5ba132b | 4/4 |
| tc5 | 09:20 | fe82ec0a | 2/5 |
| tc6 | 09:21 | fe82ec0a | 6/6 |
| tc7 | 10:43 | 13ebca8b | 7/7 |
| tc8 | 10:47 | a4c9e9c2 | 7/7 |
| tc9 | 10:54 | 0376d136 | 3/3 |
| tc10 | 12:44 | f20b3d8b | 5/7 |
| tc11 | 12:45 | f20b3d8b | 2/3 |

### UNTESTED

- dev/freeze/final/proof2.py, with its new steps 08a, 08b, 08c and 09a-NEG-vs-not-hs, was **never run in full**. It
  needs about 50 GB and drand. Its twin replacements were only dry-checked: each one occurs exactly once in its block.
  The script for that check is scratch/dry_twins.py.
- The GitHub path of record_activity and record_created, the activity API's branch_creation, was never exercised
  against GitHub. Only the twin's ACTIVITY/ file was used; scratch/t08c/ holds a sample.
- The full test (c) at 7fa3693e: see above.

### DRAFT (scratch/, never committed)

Design notes and messages:
- DESIGN_E.md and DESIGN_L.md: design notes sent to the owner. Their content went into the commits above.
- msg2.txt and msg3.txt: parts 2 and 3 of an earlier report to the coordinator.

Diffs:
- FREEZE.diff, analysis.diff, pins.diff;
- r2_*.diff, r3_*.diff, r2_stats.txt.

These are snapshots taken during the work. The commits are authoritative:
`git diff da3d9b3b 7fa3693e -- research/layered-networks` gives the full change.

Editing scripts, used once to apply changes:
- edit_freeze.py, edit_freeze2.py;
- new_case.py to new_case4.py;
- case5.py, helpers5.py.

Their results are in the commits.

Pins work files:
- pins/PINS_*.json and pins/closure_*.json: intermediate outputs of closure2.py and make_pins3.py. The final pins are
  the committed FREEZE_PINS.json.

Announce rehearsals:
- ann1/announce.block.sh: [block announce] as extracted;
- ann1/announce.twin.sh: its twin variant;
- ann1/c/DRAW_ANNOUNCE.txt and ann1/r/DRAW_ANNOUNCE.txt: the campaign (/2) and rehearsal (/1) announces that the twin
  run produced. Their clones, which include a 29.5 MB pack each, are left out.

Inputs and samples:
- drand/r.json: quicknet round 34340412, fetched once from drand. It is hardcoded in tests/test_campaign.py as
  ROUND_34340412.
- t08c/evidence__combined-scan-verify.json: a twin ACTIVITY sample for proof2 step 08c.

## How to recover

- Code: `git fetch https://github.com/HevisNico/kernel-R refs/heads/research/layered-campaign-dev`. Do not clone in
  full: the evidence branches are about 23 GB. Then check out 7fa3693ea85a85dde8490e0efdb9eafa80ff7189.
- Toolchain: meet env/envcheck.json, then run envcheck_layered4.
- Test (a) needs the kit and noise worktrees:
  - `git fetch --depth 1 <repo> refs/heads/research/inverter-instances refs/heads/research/layered-networks`;
  - worktrees at d599300d and 458bc7a6, at /home/user/kit and /home/user/noise.
- Rerun the three commands above. Compare with runs/<run>/: DEFECTS.json's tree_head and analysis_sha256, TEST_C.json's
  per-case `ok`, EQUIV_A.json's `identical`.
- Check this folder with `sha256sum -c SHA256SUMS`, run from this folder.

## Left out

- Bundle: none needed (no unpushed commit, no stash).
- Case work folders of every (c) run. They are regenerated fixtures and very large: runc2 4.6 GB, g3 4.6 GB, g2 1.7 GB.
- ann1's git clones, with their 29.5 MB packs.
- research/circuit/pdk, the local symlink.
- apt.log, tool.log, elan-init.sh: setup noise and an installer. stat1.txt and stat2.txt: `git show --stat` copies of
  public commits.
- No file here is over 50,000,000 bytes. The largest is about 157 KB, and the folder is about 2.1 MB.
