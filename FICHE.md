# Stage D: archive of the local work at the stop of the combined campaign

## Provenance

- **Who:** the stage-D worker, Claude Code session `session_01TzF7ZYVsvGaQ6EzEjxCJLM`.
- **When:** archived 2026-11-28 at the owner's request (« archiver le travail local de l'étage D qui serait perdu à la
  fermeture de cette session »), relayed by the coordinator `session_01TzF7ZUoTUj44AGYGuEFzHA`. The combined campaign
  was stopped before its official draw.
- **Sources:**
  - the main clone `/home/user/kernel-R`, with its local branches and worktrees;
  - the session scratchpad `S = /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad`.
- **Method:** everything was copied, never moved; nothing was deleted at the source. The files keep their content
  unchanged; they were copied with `shutil.copy2`.
- **One commit, on an orphan history.** Its author and committer are the identity of origin/main's last commit.

## Layout

| Path | What it is |
|---|---|
| `bundles/` | git bundles of every local commit that is not on GitHub (below) |
| `scratchpad/` | the never-committed files of S, at their own paths relative to S (below) |
| `NOT_COPIED_INVENTORY.tsv` | the files of S NOT copied, each with its path, size and sha256, and the reason |
| `SYMLINKS_NOT_COPIED.tsv` | the symlinks of S, with their targets; not copied (the archive has no symlinks) |
| `SHA256SUMS` | the sha256 of every other file in this commit |
| `FICHE.md` | this file |

## 1. Local commits not on GitHub (`bundles/`)

The method is the same for every branch:
- Every local branch tip was tested against GitHub: first the `git ls-remote` tips, then a fetch of the commit by its
  sha.
- For each tip not on GitHub, the base is its first first-parent ancestor that IS on GitHub, found by the same test.
- Each bundle is `<branch> ^<base>`, so the base is its prerequisite.
- `git bundle verify` passed on every bundle when it was made.

**To recover:** in a clone holding the base, run
`git fetch bundles/<name>.bundle 'refs/heads/*:refs/heads/archived/*'`, then `git log` on the archived branch.

### `kernel-R_local_branches.bundle` (from `/home/user/kernel-R`)

| Branch | Tip | Base (on GitHub) | Commits | Status |
|---|---|---|---|---|
| research/layered-stage-d | 071ba6ca | f2019b00 (the remote tip of research/layered-stage-d) | d83ee5f0, 4fcd90a3, 071ba6ca (2026-11-26) | UNTESTED here (a) |
| research/layered-campaign-int | 7b2c1a49 | 54689b62 | 11 (a2ea377f … 7b2c1a49, 2026-11-26) | UNTESTED here (a) |
| research/layered-campaign-int-old | e2165368 | cacea0b7 | 2 (2026-11-24) | DRAFT, superseded (b) |
| backup/layered-campaign-freeze-local-15befbd6 | 15befbd6 | 3f27bb36 (main) | 2 (2026-11-26) | DRAFT, superseded (b) |
| backup/layered-campaign-freeze-local-297e4a2d | 297e4a2d | 3f27bb36 (main) | 2 | DRAFT, superseded (b) |
| backup/layered-campaign-freeze-local-a8e51644 | a8e51644 | 3f27bb36 (main) | 2 | DRAFT, superseded (b) |
| backup/layered-campaign-int-local-4b3ec785 | 4b3ec785 | 404a0d76 | 1 | DRAFT, superseded (b) |
| backup/layered-campaign-int-local-681e67c8 | 681e67c8 | bb5ae626 | 5 | DRAFT, superseded (b) |
| backup/layered-campaign-int-local-760a72e6 | 760a72e6 | 596b8f1f | 1 | DRAFT, superseded (b) |
| backup/layered-campaign-int-local-a8ec3b5f | a8ec3b5f | 1fde9525 | 1 | DRAFT, superseded (b) |
| backup/layered-campaign-int-local-d98b72d3 | d98b72d3 | 0081f0f0 | 1 | DRAFT, superseded (b) |

(a) These commits held stage-D and integration work of 2026-11-24..26. The tests run on them at the time are recorded
    in their own commits. Nothing was rerun for this archive, so no result is claimed here. The three research/layered-stage-d
    commits were kept local at the owner's request, with the owner's identity, and were never pushed.
(b) Local snapshots of freeze and integration candidates. Each was superseded by a later candidate: the dev branch
    research/layered-campaign-dev and the freeze 5d02acce. They are kept for the record only.

### `stage_lr_erratum_v1_unused.bundle` (from `S/stage_lr`)

- **What:** c375deea, the FIRST draft of the erratum to evidence/combined-rehearsal1-local-records. Its base is
  dd672b12.
- **Status:** DRAFT, never pushed. It was replaced by e1c870d4, which is pushed, on the owner's revised text.

### `testfixture_*.bundle` (from `S/joint/work` and `S/prefreeze3/workA`)

- **What:** local test seal logs, branch `evidence/combined-seals-K01`, made by local test runs. They are root
  histories (no base).
- **Status:** TEST FIXTURES, not results. GitHub's real `evidence/combined-seals-K01` is a different history.

### Not bundled

- Test fixture repositories created by `tests/test_campaign.py` and the dry runs (`S/tcfull/WD/*`, `S/e2e17/*`,
  `S/eqbrun/*`, `S/b2/repo`, `*.seal_log_work`, `log_*.git`, …). Their commits are test-made (for example
  "test: pins regenerated (test)"), not work. Their working files are copied under `scratchpad/`; their .git
  folders are not.
- Every worktree of the main clone (`S/dev`, `S/fz/freeze`, `S/int4/wt`, `S/evwt`, …) and every clone in S
  (`S/rehearsal/kernel-R`, `S/frz/clone`, `S/stage_lr`, …) had a clean `git status`. `S/b2/repo` is the one exception:
  a test fixture with test-deleted files. Their commits are on GitHub or in the bundles above.

## 2. Never-committed files (`scratchpad/`)

These are copied as they are, from S, at the same relative paths. That is 461.5 MB in about 10,100 files. No file is
over 50,000,000 bytes.

**Not copied** (see `NOT_COPIED_INVENTORY.tsv`, which has each file's sha256):
- the raw simulation and trace data (`*.raw`, `*.raw.part-*`, `*.part-0*`) and the Lean build outputs (`*.olean`):
  10.15 GB in total;
- `S/rehearsal/analysis/R/`: the roots fetched from GitHub for the rehearsal-1 analysis, which are public;
- the git folders, the Python venvs (`prefreeze2/venvA`, `plotenv`, `venv235`, …), the wheels, the partial scan
  repository `frz/scan4/scanrepo` (incomplete, never to be reused), `rescan_tests/nonumpy` (a test venv),
  `arch_probe` (made for this archive), and every symlink (see `SYMLINKS_NOT_COPIED.tsv`).

Status of the main elements. Any file not named below is a working file of the session (a script, plan, log or
output) and is **UNTESTED: no result is claimed for it**.

| Element (under `scratchpad/`) | Status | What, on which sha, result |
|---|---|---|
| `tcfull/` (run.log, TEST_C_f46c49e0.json, HEAD.txt, WD/ minus raws) | TESTED | the full test (c) at research/layered-campaign-dev f46c49e0: 30 cases, 29 ok, 1 failing (analysis_refuses, a stale expectation, fixed in 0ce2d1af) |
| `tcref.py`, `tcref1/`, `tcref2/`, `tcref3/`, `tcref_dirty.txt` | TESTED | the fixed analysis_refuses, run alone in its three branches (pins match, tree not clean, pins differ): all PASS, with the 0ce2d1af test code |
| `frz/f3/P8.stdout`, `frz/f3/P8/` (minus the twin repo and raws) | TESTED, NOT GREEN | proof2 at 8b5c9f95: exit 1; step 05 (second-scan) refused because research/layered-campaign-dev moved during the scan; steps 06–14 not run |
| `frz/scan4/run.sh`, `frz/scan4/SCAN_LSREMOTE.txt`, `frz/scan4/scan.log` | DRAFT, KILLED | the first rescan attempt (2026-11-27 20:35), killed during its fetch on the coordinator's stop. No output. Superseded by `dev/freeze/final/rescan/rescan.sh` (pushed in 030e6bd9 and 9219986b) |
| `rescan_tests/` | TESTED | the no-scan refusal tests of rescan.sh at 9219986b: envcheck refusal, dirty clone, extra untracked file, tampered block, existing WORKDIR; each rc 1 |
| `eqa/`, `eqa_frz/`, `eqa*.log` | TESTED | test (a): 24/24 identical at 8b5c9f95 (eqa) and at 5d02acce (eqa_frz), byte-identical; the other eqa*.log are earlier runs |
| `rehearsal/analysis/` (OUT1, OUT2, logs; minus R/) | TESTED | the rehearsal-1 analysis, two byte-identical runs; published (below) |
| `rehearsal/replay/` (minus raws) | TESTED | TASK 3, the replay of the third symbol; published (below) |
| `rehearsal/trace_study/` (minus the raw) | TESTED | the trace study; published (below) |
| `frz/fill_freeze.py`, `frz/make_pins*.py`, `frz/closure*.json`, `frz/scan3/` | TESTED (as used) | the freeze tooling; closure2.py and make_pins3.py are pushed under dev/freeze/final/ |
| `defects_*.json`, `defects_8b5c.log`, `suite5d/` | TESTED | runs of the independent defect suite at various dev states; the published records are the DEFECTS_AT_*.json files on the dev branch |
| `new_analysis_*.py`, `new_cases.py`, `new_draw.py`, `new_main.py`, `analysis_ef374ccd.py` | DRAFT | the parts analysis.py and its tests were assembled from; the assembled code is pushed |
| `fix_final.diff`, `sealpush_fix.diff`, `cd_note.patch` | DRAFT | patches, applied or superseded in pushed commits |
| `PREDICTION_CANDIDATE.md`, `runbook_sent.md`, `FIX_SHA_TABLE.json` | DRAFT | notes and a sent runbook |
| `taskB_show.txt`, `taskB2_show.txt`, `block_sha_before.txt` | RECORD | the diffs of 030e6bd9 and 9219986b as sent to the coordinator; the block's sha256 before the amendment |
| `stage_lr_SHA256SUMS.tmp` | RECORD | the working sums made for evidence/combined-rehearsal1-local-records |
| `arch_*.txt` | RECORD | the probes made for this archive: ls-remote, repositories, unpushed refs, their bases |

## 3. Results already public (commits and paths)

| What | Branch | Commit | Path |
|---|---|---|---|
| The C/D freeze candidate (campaign.py, analysis.py, FREEZE.txt) | research/layered-campaign-dev | 8b5c9f95 | research/layered-networks/ |
| The independent suite at 5d02acce (34/51) | research/layered-campaign-dev | a22f6f2e | dev/rehearsal1/suite_at_5d02acce/ |
| Trace study | research/layered-campaign-dev | df2bb840 | dev/rehearsal1/trace_study/ |
| TASK 3 replay | research/layered-campaign-dev | 9618a665 | dev/rehearsal1/replay/ |
| analysis_refuses made deterministic | research/layered-campaign-dev | 0ce2d1af | tests/test_campaign.py |
| The final rescan wrapper (block byte for byte, labelled additions) | research/layered-campaign-dev | 030e6bd9, 9219986b | dev/freeze/final/rescan/ |
| The rehearsal-1 analysis | evidence/combined-rehearsal-analysis | 4fd58425 | (root) |
| Local records of rehearsal 1 and the candidate | evidence/combined-rehearsal1-local-records | dd672b12, erratum e1c870d4 | (root) |
| The first freeze | research/layered-campaign-freeze | 5d02acce | |

The paths are under research/layered-networks/ unless the table says otherwise.

## Checking this lot

- **The files:** run `sha256sum -c SHA256SUMS` at the root.
- **The bundles:** in a clone with the bases, run `git bundle verify bundles/<name>.bundle`. The two test-fixture
  bundles have no prerequisite.
- **The files not copied:** each one's sha256 is in NOT_COPIED_INVENTORY.tsv. They can be checked against a surviving
  copy, or against the published copies:
  - the replay raws: dev/rehearsal1/replay/runs/RAW_SHA256SUMS.txt (9618a665);
  - the trace raw: evidence/combined-rehearsal1-local-records.

## 4. Complement (second commit): the six XOR replay traces

The owner approved adding them («Oui aux six traces du rejeu XOR»). They are TASK 3's six ngspice raws, which the
first commit had left out as raw data. They are now under `scratchpad/rehearsal/replay/`, and they are removed from
NOT_COPIED_INVENTORY.tsv.

| Path | Size (bytes) | sha256 |
|---|---|---|
| scratchpad/rehearsal/replay/r_27735_case1/replay.raw | 15178249 | 8f4ccd74f6566dd419f4eff3edd5fe90c93a223d9263aba4aacb441caae2f322 |
| scratchpad/rehearsal/replay/r_27735_case2/replay.raw | 15613929 | 29206d64613abac02a1a14f5d63c57195fb9bdfc100a74fffd1d5a21a8b9a8aa |
| scratchpad/rehearsal/replay/r_27735_case3/replay.raw | 15501929 | 7221a809319d0b982406106d84321152dac50dd8eb8b3f119548acf3d09bd2ba |
| scratchpad/rehearsal/replay/r_88529_case1/replay.raw | 15779409 | 08d018acc01c405134ba352d56a02650bbbc6c37fe9aa189cbd608702cfd03d2 |
| scratchpad/rehearsal/replay/r_88529_case2/replay.raw | 16227969 | c4e25a3189557f20713e1b1670d87a503dfdb30065de111951773d4cf4397c57 |
| scratchpad/rehearsal/replay/r_88529_case3/replay.raw | 16170849 | f7ae92bc901204a5f78ca15aaae367c74af2e0b34bcf6b67d869300337c09949 |

- **Published reference:** research/layered-networks/dev/rehearsal1/replay/runs/RAW_SHA256SUMS.txt at
  research/layered-campaign-dev 9618a665.
- **Status: TESTED.** Each file's sha256 equals its line in RAW_SHA256SUMS.txt at 9618a665. This was checked before
  the copy, and again on the copy.
- The same six files are also on evidence/combined-rehearsal1-local-records (dd672b12), under replay/.
