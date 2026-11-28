# Lot a: test-writer

## Provenance
- Session: session_01TzF7ZTyrHCbSzqfjfwMyQW (the test writer of research/layered-networks/tests/test_analysis_defects.py).
- Repository: HevisNico/kernel-R.
- Local branch: research/layered-campaign-dev at aad8aa09303ac7bdedaabeb5c17eaf44834ff0f1, rebased locally on
  13ebca8b42fc74e56f6ea8e0e4fd1f356e4734cd. None of the commits below was pushed.
- Base revision on which the current cases load: 7fa3693ea85a85dde8490e0efdb9eafa80ff7189 (the 90 L cases). The test
  file of aad8aa09 is run by copying it into a clean worktree of that commit:
  `LAYERED_DEFECT_ONLY=L python3 -B tests/test_analysis_defects.py OUT.json`.

## Contents
- `test-writer.bundle`: every local commit of the session, 59 refs `refs/heads/local/<sha>` (one per commit, the
  pre-rebase variants included) and `refs/heads/research/layered-campaign-dev`. It is an INCREMENTAL bundle: a bundle of
  `--all` would be about 450 MB (the clone's history), over the 50 MB limit. Its 13 prerequisite commits are all
  ancestors of 7fa3693e on research/layered-campaign-dev. `git bundle verify` reports it okay in the session's clone.
  Recovery: in a clone holding research/layered-campaign-dev at or after 7fa3693e,
  `git fetch test-writer.bundle 'refs/heads/*:refs/remotes/test-writer/*'`.
- `tests_at_run/test_analysis_defects.py.at_<commit>`: the test file at each commit that was run (bytes from git).
- `records_committed/`: the run records committed locally (dev/equiv/DEFECTS_L_AT_*.json), named
  `<record>__tests_<test commit>__commit_<record commit>.json`.
- `scratchpad_files/`: the session's uncommitted files, copied as they are: the latest run records and logs of the
  runs on f20b3d8b and 7fa3693e, earlier run records (D8/D9/D10, draw, beacon, X, R suites, already summarized in the
  records pushed in earlier sessions), and the helper scripts (runL.py, one.py) and section drafts (lsection.py,
  vsection.py, rec.py) that went into the test file.

## Runs of the L cases
Each run: the test file's commit and sha256, the kernel-R commit whose code ran, the sha256 of the analysis.py imported,
and the result. "spec" is the campaign announce in layered-draw-announce/2; "interim" writes it as a5ba132b did.

| test commit | test file sha256 | kernel-R code | analysis.py sha256 | result | record |
|---|---|---|---|---|---|
| 78e0e4b7 | 3b3489f864bae4f4e8c29b4fd81e1cfb5231386a1bfab8aa7227306a20ee7232 | da3d9b3b | c16995e8… | 10/24 (the 14 extra-exclusion cases fail: the defect shown) | records_committed/…78e0e4b… |
| cb55bc59 | aac61a833bebb6f577640b74a5eb9e2f80b24dee19e98a9e0977a4fc4640fc55 | da3d9b3b | c16995e8… | 10/24 | records_committed/…cb55bc5… |
| 2e211049 | 452b3b0e2bd5555d31925487a9c3a4be8786f0a5f8c78baf6a748e789421b73c | da3d9b3b | c16995e8… | 10/33 | records_committed/…2e21104… |
| 99b6fe0b | 71fef4f600ea106120af8178018ac49a6baec637e160c32edf35e2d16734072e | a5ba132b | b35e9522… | spec 20/34, interim 29/34 | records_committed/…99b6fe0… (both) |
| f347a4d4 | c23cef2f850d5fea3c2e13e3ff36e0d8a10ed98c45802b6a946dd8f88938cf46 | a5ba132b | b35e9522… | spec 19/52, interim 29/52 | records_committed/…f347a4d… (both) |
| 8063d314 | 1c46172a3246cf285119ec2ff8d9a3d05e7d58de2fda7027c11c990a3f00e95b | a5ba132b | b35e9522… | spec 19/58, interim 27/58 | records_committed/…8063d31… (both) |
| e2a80288 | 22db93d8153267c7ae13ddba2b1a72979ef4ba585b56626398d8fc3634c8968b | 13ebca8b | 013f01ac… | 59/62 | records_committed/…e2a8028… |
| bd0351a5 | 4a15b57adc269708a5e6480974fbc5ee8a1edf4f578150800c39868018d52b35 | 13ebca8b | 013f01ac… | 60/71 (the 11 record and N2 cases await f20b3d8b) | records_committed/…bd0351a… |
| bd0351a5 | 4a15b57adc269708a5e6480974fbc5ee8a1edf4f578150800c39868018d52b35 | f20b3d8b | 069eeca8… | 66/71 (5 fixtures without a verify record) | NOT KEPT (see below) |
| ac5b7aa8 | 4b1a8bb3dd74ce09c61b3ef3b4690643c8d7947f077027e4c540cf013c083e27 | f20b3d8b | 069eeca8… | 71/71 | scratchpad_files/DEFECTS_L_AT_f20b3d8b.json, LF.log |
| aad8aa09 | 2b06d9be1b0573840b2eea123a40698ef0f9c2ca54a9ce3bfae41a6c78bc1abb | 7fa3693e | 0c10b8b9… | 90/90 | scratchpad_files/DEFECTS_L_AT_7fa3693e.json, L7.log |

Full sha256 of each test file: `sha256sum tests_at_run/*` (also in SHA256SUMS). Full analysis.py sha256:
c16995e8eb2e… (da3d9b3b), b35e95225308… (a5ba132b), 013f01ac79ed75bd1acf1343f4b97c4a8ec20464f720e6a63a0bfb42bb23d016
(13ebca8b), 069eeca87927cdfea23f12bfc3522932cd0db662a73f5800c10c7480f67bbaa6 (f20b3d8b),
0c10b8b94bcb1bd414683528b26a92b50db7cb3ac2c824b0a73b83cd00b860f6 (7fa3693e); each record carries the full value.

## State of each item
- test_analysis_defects.py at aad8aa09: TESTED, 90/90 at 7fa3693e (L cases only, LAYERED_DEFECT_ONLY=L). The earlier
  52 non-L cases (D8, D9, D10, draw, E1, E2, beacon, X1, X2, R) were last run in full at 8b5c9f95 (52/52, record pushed
  earlier); they were NOT rerun on 13ebca8b, f20b3d8b or 7fa3693e.
- The 66/71 run on f20b3d8b: TESTED, but its record and log were overwritten in the scratchpad by the 71/71 rerun of
  the same day; its result and its five failures are only in the session's messages to the coordinator.
- The /2 interim switch LAYERED_DEFECT_CAMPAIGN_ANNOUNCE=1 or 1s: kept in the test file for code before the /2 change;
  not used at 13ebca8b and later.
- scratchpad_files/*.py (lsection.py, vsection.py, rec.py): DRAFT sections, already merged into the test file; runL.py
  and one.py: run helpers, not part of the suite.
- Nothing is left out but the session's clone itself (its history is on GitHub) and the twins and temporary folders
  the cases build and delete.
