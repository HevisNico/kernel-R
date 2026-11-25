# Second pre-freeze dry run, 2026-11-25 (local only, nothing pushed)

## The fixes (local commit feee4472 on research/layered-stage-d, new files only, owner-authored)
| Defect | Fix | File |
|---|---|---|
| 1, 6 | campaign_run2's end is held (no INVENTORY_END or DONE) until every job has ended, remote duplicates included. Then: core_budget is rewritten with the peak over every job; DUPX_<inst>/SHA256SUMS; the top-level SHA256SUMS, which covers it; then INVENTORY_END and DONE | campaign_run9.py |
| 2 | **extraction.** Before the save_ref round's trace.raw is deleted, ROUND/ref/ is written: trace.raw holding the comparator vectors (time, x<j>.vrefm, vrefmn, nzm, nzh<j>, nzj<j>; the original columns, bit for bit), a record copy, SHA256SUMS and ref.json. Size: XOR3 44.6 MB (11 of 670 vectors), NOT1 3.7 MB. A failed extraction keeps the whole trace | ref_extract.py, campaign_run9.py |
| 3 | PLAN remote_duplicates[].seal_dir. The seal log branch is fetched by name; the commit must be on it, and its SEALS.txt line for the instance must equal sha256(seal_dir/SHA256SUMS); seal.verify must hold. The seal is then copied to DUPX/seal, and N0 is compared with campaign_run's compare_argv (compare_d2, noiseless) into DUPX/N0/comparison.json. Otherwise DUPX/seal_check.json says why and no comparison is written. check_duplicate is unchanged | campaign_run9.py |
| 5 | numpy fingerprint = sha256 over the files RECORD lists under numpy/ and numpy.libs/ (contents on disk, not RECORD's claims), without __pycache__, bin/ or dist-info. ENV format layered-env/2 | envcheck_layered2.py |
| 4 | owner's criterion, written in the file: equal outcomes (words, lessons, tests, skews, emissions), decks equal outside the noise lines, u within ±1 in the last digit (1e-7 V, the grid checked). Latch dates and inverter x readings are listed, not judged | tests/check_noise_identity2.py |

**Tests.**
- tests/test_campaign_run9.py: 3 pass.
  - DONE and INVENTORY_END are absent while the remote duplicate runs; afterwards verify prints "verified" and covers
    DUPX/SHA256SUMS.
  - A valid seal that is not the logged one gives no comparison.
  - The extraction keeps the original columns bit for bit.
- The earlier tests still pass: test_campaign_run8, 7, 5 and 3, test_yield_lot2, test_stage_d.
- On the first dry run's data:
  - check_ref_level on the XOR3 extract gives output byte-identical to the run on the full 2.7 GB trace;
  - check_noise_identity2 passes on XOR3 9803 (3 of 232 u at exactly one digit, all listed).

**Transport of the seal to machine B (open, for the owner).** B needs the original's seal folder: three small files,
MANIFEST.json, SHA256SUMS and the sealed prediction. Today the seal log branch carries only the hash line, and the seal
files leave machine A only with its results push. In the dry run both clones are on one machine, so seal_dir is a path.
In the campaign, either:
- A also pushes its seal folder at sealpush time (to its log branch or a sibling branch), which adds to the approved
  protocol; or
- the remote duplicate's comparison runs once A's results branch is pushed.

## Setup
- **Clones A and B.** Two fresh clones from GitHub (single branch research/layered-stage-d). In each, the stage-d fix
  commit feee4472 was fetched by name from this session's local repository (the fixes are not pushed).
  layered-networks 458bc7a6 and inverter-instances d599300d were fetched by name from GitHub. Each clone has its own
  PDK (fetch_pdk.sh, 1232782c) and its own numpy 2.3.5 venv.
- **envcheck.** ok on both (envcheck_layered2).
- **Machine.**
  - uptime -s was 2026-11-25 16:45:38 throughout (the container restarted at 16:45, before this run).
  - nproc 4; pgrep ngspice was 0 before each launch.
  - Disk: 21 GB free at the start. I deleted the first dry run's three scratch trace.raw files (zero1, ref1 and the
    DUPX: 2.42, 2.72 and 1.85 GB; their digests remain), leaving 28 GB.
- **Instance.** NOT1 9804 (excluded dev seed, known to have room at K3). Clone A ran campaign_run9 with save_ref_round
  1, U on NOT1, and the seal log to a local bare repo (pre-receive refuses deletions and non-fast-forward updates;
  post-receive logs times). Clone B ran campaign_run9 with remote_duplicates [NOT1 9804, seal_dir = A's seal, seal_log
  = A's 1cc71e9d].

## Results
- **Clone A.** deck, inverters, D, seal, sealpush (1cc71e9d, stage N 2.015 s later), N0 to N3 with C0 to C3 (all
  agree), U holds. 13 MB at the end.
- **Clone B.** The DUPX N0 is ok; seal_check is ok (logged seal sha256 58694398…, verdict agrees). 19 MB, including the
  DUPX trace.raw (19.5 MB), kept by campaign_run5's rule.

| Criterion | Result |
|---|---|
| ENDED DONE only after the duplicate | **PASS.** B was polled every 10 s, 9 times, while its driver was alive: DONE and INVENTORY_END were absent and `wait` printed RUNNING. DUPX N0's record was written at 17:04:35.654, its comparison at 35.800, DONE at 35.816. (`wait` saw DONE on the last poll, written within that poll) |
| verify "verified", covering the duplicate | **PASS** on A and on B. B's top-level SHA256SUMS lists DUPX_NOT1_9804/SHA256SUMS, which covers N0/comparison.json, input.spice, noisy_record.json, trace.digest.json, the seal's 3 files, duplicate_here.json and seal_check.json |
| check_duplicate IDENTICAL, unchanged | **PASS.** input.spice, comparison.json, noisy_record.json and the trace (by digest, Date: excluded; 63f2076f) identical; session.log identical under the criterion. DUPLICATE IDENTICAL |
| ref noise readable from the root after the raw deletion | **PASS.** No trace.raw is left in A except N1/ref/trace.raw (3.7 MB, sha256 8bdd0468…). check_ref_level on A/NOT1_9804/N1/ref: rms(e) 396.4 µV against nzm 396.7 (0.9993), 0.949 of the 417.6 µV budget, residual max 29.1 µV: REFERENCE LEVEL READ |
| the same numpy fingerprint in A and B | **PASS.** files_sha256 cd6ab151… (895 files) in both. ENV static_sha256 fcc8786f… is equal in A and B |
| new zero-noise check PASS | **PASS.** check_noise_identity2 on A's N0 against a separate scale=0 round 1: decks, words, lessons, tests, skews, emissions equal; 12 u, 0 differing. Listed: 5 latch dates (1–2 ns) and 12 inverter x readings. One is large: slot 1 n0 x_D, 0.9056 (off) against 1.0155 (zero), where every other slot reads about 1.0156 in both runs; consistent with x read by interpolation while x moves fast at D. Listed, not judged |
| analyze twice byte-identical | **PASS.** analyze6 over A and B, run twice, byte-identical. Seal regenerated identical, log_ok, 0 seal defects; NOT1 counted at K0 and K3 |

## Found here, not fixed
- **analyze3's cross-machine duplicate disagrees with check_duplicate.** It reports `trace.digest.json_identical:
  false` for NOT1 9804, while check_duplicate says IDENTICAL. analyze3 compares the two trace.digest.json files byte for
  byte, and each holds its run's `date_line`, so this line will always read false for a real duplicate. It also does
  not read DUPX/N0/comparison.json or seal_check.json.

## Measured costs (NOT1 9804, CPU min; plan_split COST in brackets)
- inverters 2.41 (2.5); D 3.58 (3.7); N0 1.57 (1.5); N1 2.10, N2 2.13, N3 2.07 (2.0 each).
- U 0.43; DUPX N0 1.42.
- Instance total 13.9 CPU-min.
- **XOR3, from the first dry run:** inverters 12.4 (11.5); D 60.5 (57); N0 48.4 (42); noisy rounds 63.0, 61.4, 63.0
  (62); U 3.2; DUPX N0 46.9.
