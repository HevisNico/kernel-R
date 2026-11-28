# Lot a: test-writer, FICHE complement (after the audit of 9f8517f1)

The audit reran tests_at_run/test_analysis_defects.py.at_aad8aa0 in a clean worktree at 7fa3693e and got 61/90. This
file states what the 90 L cases need. Each point was checked in this session on 2026-11-28 at 7fa3693e.

## 1. History the clone needs
- To RUN the L cases, the checkout of 7fa3693e is enough (any depth): the cases read the tree and `git rev-parse HEAD`.
- To USE test-writer.bundle, the 13 prerequisite commits are needed. The minimum is depth 94 from 7fa3693e:
  `git fetch --depth 94 <origin> 7fa3693ea85a85dde8490e0efdb9eafa80ff7189`. With depth 94, `git bundle verify` is
  okay; with depth 93 it fails. The farthest prerequisite, 63facf70458a, is 93 generations below 7fa3693e. With depth
  60, the 7 prerequisites 63facf70, f2a615a3, 91f6fa57, 2d30c5c8, e14c3200, ac98a83a and 93cf7a92 are missing, as the
  audit found. A full clone also works. If research/layered-campaign-dev moves on, count the depth from 7fa3693e, not
  from the new tip.

## 2. A remote named origin
The test reads `git remote get-url origin` of the clone that holds the tree under test. The first L case to need the
shared fixture (list_base) fetches, by branch name from that URL:
- refs/heads/evidence/combined-rehearsal-draw-result, at f74b75fb, for rehearsal 1's DRAW.json;
- refs/heads/evidence/combined-rehearsal-draw, for its EXCLUDED_PUBLISHED.json and DRAW_ANNOUNCE.txt.
Without origin, that first fetch fails after list_base has created its folder, so every later case fails with
FileExistsError. The URL must reach those two branches. Only cli_pre_announce needs no origin.

## 3. GitHub's activity API and gh
- With the shims loaded (see point 4), NO case calls gh or any GitHub API. This session's gh is not authenticated
  ("Failed to log in to github.com using token"), and the 90/90 run at 7fa3693e passed with it.
- Two shims replace the GitHub reads. Each is a usercustomize.py that the test writes and puts on PYTHONPATH for its
  own subprocesses:
  - SHIM: check_draw offline and check_rehearsal_seeds with strict=False. It is used by the 14 list_blocks_* cases.
  - TWIN_SHIM: analysis.scan_verify_record and analysis.record_created go to the twin's path. It is used by the 13
    verify_record_* cases and by announce_block_exact and announce_block_scan_byte.
- If the shims are NOT loaded, these 29 cases read the real GitHub, and some need an authenticated gh on
  HevisNico/kernel-R that they cannot pass in any case:
  - list_blocks_rehearsal_exact, _extra, _drop_noise, _drop_scan and _field read rehearsal 1's announce and activity
    from GitHub, through gh api repos/HevisNico/kernel-R/activity. The audit's gh failure.
  - list_blocks_campaign_exact, _extra, _drop_noise, _drop_scan, _field, _no_scan, _scan_short, _r2_extra and
    _scan_unreadable read rehearsal 2's announce from GitHub. That branch does not exist: see point 5.
  - verify_record_exact, _absent, _other_hash, _not_success, _success_only, _other_freeze, _empty_freeze,
    _verify_lsremote_sha, _scan_lsremote_sha, _problem_line, _force_back, _recreate and _other_analysis_sha, plus
    announce_block_exact and announce_block_scan_byte: record_created asks GitHub for the record branch's activity.
    The audit's gh failure.
  These are the audit's 9 + 19 + 1 failures.
- The other 61 cases run without gh or any GitHub API. All of them except cli_pre_announce do need the two git
  fetches of point 2. They are:
  - list_funcs_*;
  - scan_* and scan_file_*;
  - verify_scan_* (on the twin, through url.insteadOf, with GIT_ALLOW_PROTOCOL=file);
  - cli_pre_announce, pre_announce_*, announce_commit_* and record_analysis_*;
  - announce_rehearsal1_parses and format_*.

## 4. Environment
- Python 3.13.18. The run used numpy 2.5.3 and py_ecc 8.0.0; the audit used numpy 2.3.5 with the same result for the
  61 cases. The L cases import analysis.py, draw_seeds.py, beacon_chain.py, beacon_verify.py and plan_split3.py of
  the tree.
- Python's user site directory must be ENABLED for the interpreter that runs the test (sys.executable is passed to
  every subprocess), because the shims are usercustomize.py files. site.ENABLE_USER_SITE is False:
  - with PYTHONNOUSERSITE set;
  - with python -s or -I;
  - when the effective uid differs from the uid.
  Check it with `python3 -c "import site; print(site.ENABLE_USER_SITE)"`; it must print True.
- Tools: git (2.43.0 here), bash 5, coreutils (sha256sum, realpath, split, timeout), awk and sed. Lean and ngspice are
  NOT needed for the L cases.
- Network: only the git fetches of point 2. The drand rounds are hard-coded, and the blocks' GitHub URLs go to local
  twins.

## 5. list_blocks_campaign_exact: "couldn't find remote ref refs/heads/evidence/combined-rehearsal2-draw"
ESTABLISHED: it has the same cause as the 9 gh failures. The shim was not loaded; no twin was left unbuilt.
- [block check-list] calls A.check_draw on rehearsal 2's DRAW.json in rehearsal mode, with offline left at None. With
  SHIM loaded, the call becomes offline=True, with the fixture's announce file.
- Without SHIM, check_draw takes its GitHub path: announce_on_github fetches refs/heads/evidence/combined-rehearsal2-draw
  from https://github.com/HevisNico/kernel-R. That branch does not exist, because rehearsal 2 was never announced, so
  the fetch fails before any activity is read. The other list_blocks_campaign_* cases fail on their gate.
- Reproduced here at 7fa3693e with the archived test file and PYTHONNOUSERSITE=1. The record is
  evidence/no_user_site_run_at_7fa3693e.json.
  - list_blocks_campaign_exact gives exactly: refused: the draw's announce cannot be read from GitHub
    (evidence/combined-rehearsal2-draw): RuntimeError("git fetch -q https://github.com/HevisNico/kernel-R
    refs/heads/evidence/combined-rehearsal2-draw: fatal: couldn't find remote ref refs/heads/evidence/combined-rehearsal2-draw").
  - verify_record_exact gives "refused: GitHub records no activity for the scan verify record
    evidence/combined-scan-verify". Here the API answered with no item; in the audit, gh failed instead.
  - list_blocks_rehearsal_exact fails its own control, because no shim line was logged.
- So the 29 failures have one cause: the user site, and with it the shims, was not active in the audit's run. With it
  active, as here, the same file gives 90/90.
