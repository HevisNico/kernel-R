# Notes on equivalence test (b), the second run (dev/equiv/EQUIV_B.json)

**Code commit of the run: 86a00ac2479101f116f600626f05a13cddedb799**, on four test machines, in test mode
(RUNBOOK_B.md). EQUIV_B.json is kept exactly as tests/equiv_b.py (at that commit, unchanged) wrote it.

## The roots

| Machine | Root (evidence branch, tip) | Seal log (tip) | Reference root (the chain) |
|---|---|---|---|
| K02 | evidence/devtest-run2-K02 41f053ff | evidence/devtest-seals2-K02 69be17bc | final dry run out_K01 (campaign_run14): XOR3_9803, U_XOR3_9803 |
| K03 | evidence/devtest-run2-K03 a08d88d0 | evidence/devtest-seals2-K03 b4442f30 | prefreeze g2 rootA (campaign_run11, stage_d5 era): ANDOR3_6104, U_ANDOR3_6104 |
| K05 | evidence/devtest-run2-K05 a4cbddc8 | evidence/devtest-seals2-K05 80f2c0f5 | e2e17 out_K01 (NOT1_6220), out_K02 (NOT1_6212, U_NOT1_6212) (campaign_run17) |
| K06 | evidence/devtest-run2-K06 6931fd91 | none (a duplicate only) | e2e17 out_K07 (DUPX_NOT1_6212) |

Each root was fetched by name, and its SHA256SUMS verifies. No file was over 50 MB on push, so none was split.

## Verdicts

- **Identical except listed:** U_XOR3_9803, ANDOR3_6104, U_ANDOR3_6104, NOT1_6220 (D4-audited), NOT1_6212,
  U_NOT1_6212.
- **DUPX_NOT1_6212: DIFFERS on the wait's length only.** The two unlisted paths are seal_wait.json /attempts (7 vs 9
  polls) and /waited_s (363.8 vs 480.1 s). They record how long the duplicate waited for its home machine's seal,
  which depends only on when the home machine pushed. Every other field of the 15 files is identical except listed.
- **XOR3_9803: DIFFERS on the Date: line of the split trace extracts only.** The 12 unlisted paths are, for each of
  N0–N3, extract/trace.raw.part-000 (bytes) and the two hashes that follow from it (extract/PARTS.txt and
  extract.json /parts[0]/sha256). Traces over 50 MB are stored as parts; equiv_b.py applies check_duplicate's
  raw_compare (the Date: line excepted) to files ending in trace.raw, and the parts fall to a byte compare.
  dev/equiv/b/check_extract_parts.py (a record helper, not campaign code) checks every part and every reassembled
  trace: dev/equiv/b/EXTRACT_PARTS_XOR3_9803.json, `all_identical_except_date_line: true`. In each round, part-000
  equals the reference once its first `Date:` line is removed, every later part is byte-identical, and the whole trace
  has the same length and is identical except that line.
  The campaign's duplicate check (tests/check_duplicate.py) compares a round folder's own trace.raw, or its
  trace.digest.json when the raw is deleted. It never reads the extract folder, so this gap cannot touch a counted
  comparison.

The rules were not changed after seeing these differences (the coordinator's decision): a rule chosen after the fact
is not a rule.

## The analysis on these roots (dev/equiv/b/run2/)

analysis.py test, twice for each times source, on the four roots; the two runs of each are byte-identical.
- `times=bare`: every instance not sealed. This is correct: the seal logs are on GitHub, not local bare repositories.
- `times=github`: **a defect found by this run.** sealpush.times(github) asks the activity API for
  `activity_type=push` only, and GitHub records the push that creates a branch as `branch_creation`. The first seal
  on each log branch therefore has no push time, and is a seal defect: XOR3_9803, ANDOR3_6104 and NOT1_6212 are not
  sealed. Only NOT1_6220, the second seal on K05's branch, is counted (NOT1 K0 and K3: held on one instance). The
  regeneration is identical for all four seals. Fixed in 2011058e (next section).
- In both: U holds in the three groups. The cross-machine duplicate's comparison agrees with its original; its
  check_duplicate verdict is null here because no controls tree was given in test mode.

No committed analysis result in this repository's layered tree used times=github: all RESULTS.json files record
`bare`, the local bare post-receive log, or no times source.

## After the fix (dev/equiv/b/run2/RESULTS_times_github_ef374ccd.json)

**The simulations ran at 86a00ac2. The fixed commit ef374ccd differs from it only in sealpush.py and the tests**
(dev/equiv/b/FIX_SHA_TABLE.json: of the 35 files campaign.py runs or imports, every one is byte-identical except
sealpush.py). In sealpush.py only `times` changed, and `GITHUB_PUSH_TYPES`, `github_times` and `activity_pages`
were added; the `__main__` block is identical. sealpush2.py, which pushes the seals and fetches the log, uses
sealpush's LOG, git, seal_sha and utc only, and campaign.py runs `sealpush2.py push` and imports sealpush2.fetch.
Neither the push nor the fetch calls a changed function, so **the roots stand**; only the analysis reads times.
No new run of (b).

The fix: sealpush.times(github) reads every activity item of the ref (paged with activity_pages) and keeps the types
push and branch_creation (github_times). GitHub records the first push of a log branch as a branch creation, and that
event counts as its push. A force push or a branch deletion never gives a time; whether one on a log branch should
make a seal defect is left to the complementary analysis.

analysis.py test at ef374ccd, twice, on the four roots with `times=github`:
- RESULTS.json and SHA256SUMS byte-identical between the two runs (kernel_build/KERNEL_BUILD.json differs only in
  its `seconds`, the build's duration);
- `seal_defects` empty; the four instances sealed, each seal pushed before its stage N started:
  XOR3_9803 margin 3.493 s, ANDOR3_6104 2.832 s, NOT1_6212 2.909 s, NOT1_6220 3.368 s;
- verdicts at K0 and K3: XOR3 and ANDOR3 held on one instance, NOT1 held on 2 instances, not established;
- against RESULTS_times_github.json (before the fix, kept as the record of the defect), the only differences are the
  three seals now timed and what follows from them in counts and verdicts, and `pins` (tree_commit ef374ccd;
  sealpush.py listed as differing from its FREEZE_PINS.json pin, which the next freeze regenerates).
