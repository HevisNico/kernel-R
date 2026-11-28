# Seal folder on the log branch, analyze7, x_D diagnosis — 2026-11-25 (local only, nothing pushed)

Local commit b74d9514 on research/layered-stage-d (new files only, owner-authored, subject-only): sealpush2.py,
campaign_run10.py, analyze7.py, tests/test_campaign_run10.py. Its 2 tests pass, and test_campaign_run9 still does.

## (1) The seal folder pushed with the log line
- **sealpush2.push.** One commit on evidence/combined-seals-K<nn> appends the SEALS.txt line and adds seals/<instance>/
  (every file SHA256SUMS lists, and SHA256SUMS). Before the push:
  - the commit's diff against the branch tip must hold only A entries plus M of SEALS.txt;
  - SEALS.txt must start with the old file;
  - seals/<instance>/ must not exist on the branch yet (a second seal is refused).
  The push is plain, checked by ls-remote. Stage N starts only after it succeeds (campaign_run5's check, unchanged).
- **campaign_run10.**
  - Machine A's sealpush step runs sealpush2.
  - Machine B's remote duplicate needs only seal_log: it fetches the branch by name (sealpush2.fetch), takes
    seals/<inst>/ at the commit, records seal_fetch.json, then applies campaign_run9's three checks (commit on the
    branch, SEALS line = sha256 of SHA256SUMS, seal.verify) and writes its comparison.

### Test against a local bare repo standing in for GitHub
The repo had a pre-receive hook refusing deletions and non-fast-forward updates, and a post-receive hook logging
times.

| Group | Seal folder (3 files) | Commit | push started → server received → ls-remote confirmed (UTC) |
|---|---|---|---|
| NOT1 9804 | 3 904 bytes | 2bf3da2f | 17:12:22.6133 → .6454 → .6546 (41 ms) |
| XOR3 9803 | 6 592 bytes | 5efbea59 | 17:12:22.8501 → .8835 → .8935 (43 ms) |
| ANDOR3 9805 (seal from dev/dryrun_b) | 5 736 bytes | 4d7a365f | 17:12:23.0948 → .1311 → .1418 (47 ms) |

- **The commits.** Each later commit's diff is "M SEALS.txt" plus 3 "A seals/<inst>/…".
- **Machine B.** It fetched each folder by name at its commit; seal.verify held, and the SHA256SUMS sha256 equalled the
  logged line (58694398…, 24d0ca90…, 469d2f29…).
- **Refusals.**
  - A second seal of NOT1_9804: "seals/NOT1_9804 is already on … a second seal is refused".
  - A forced rewind of the branch: refused by the hook (non-fast-forward).
  - A fetch at a commit before the seal, or at an unknown commit: refused.
- **Push times.** These are local-disk times. A GitHub push adds the network round trip; the folder adds only about
  4–7 kB.

### End to end with campaign_run10 (NOT1 9804; clones A and B updated to b74d9514 by name)
- **Clone A.** The sealpush commit 872c4b8d holds SEALS.txt and seals/NOT1_9804/ (3 files, 3 904 bytes). The push
  took 267 ms from start to confirmation (17:18:45.514 → .781), and the server logged it at .7686. The chain completed
  with C0–C3 agreeing.
- **Clone B.** The plan gave seal_log only. seal_fetch ok; seal_check ok (sha256 6a251931…, verdict agrees).
  - verify "verified".
  - check_duplicate (unchanged): DUPLICATE IDENTICAL.

## (2) analyze7
- **The rule.** Every DUPX is judged by the controls tree's tests/check_duplicate.py itself (loaded from PLAN noise_tree,
  its sha256 recorded: 6686f0cd…), on <orig>/<inst>/N0 against DUPX_<inst>/N0. That is: digest content with the Date:
  line excluded; records and comparison without the excepted fields; session.log outside the progress lines.
- **What it reports.**
  - identical, and the checker's lines;
  - seal_check.json (without its local path), and seal_fetch.json;
  - DUPX comparison.json's verdict, and whether it equals the original's comparison without the excepted fields.
  - analyze3's old entries are kept as cross_machine_duplicates_v3.
- **On the second dry run's roots (outA, outB).** NOT1_9804: identical true. The checker's lines are all identical,
  then DUPLICATE IDENTICAL. Comparison agrees and equals the original's; seal_check ok. analyze3's old line there still
  says trace.digest.json_identical false.
- **Determinism.** Run twice: byte-identical (RESULTS sha256 a3a92f63…).
- **On the campaign_run10 roots (outA10, outB10).** identical true; comparison agrees, equal to the original's; seal_fetch
  ok. Run twice: byte-identical.

## (3) x_D diagnosis (read-only, no fix)
- **Which readings the gate and the prediction use: neither uses x_D.**
  - `inverter_x` (x_tau, x_D) is written only by the controls' noise3/controls4/controls5 network runs, into
    noisy_record.json.
  - No stage-D, comparison or fit code reads it (stage_d*.py, compare_d*.py, fit*.py: no reference), and the 56
    yield-lot stage-D records carry no inverter_x.
  - The inverter gate (kit invinst.indeck) does not read the network run at all. It takes its x from its own five runs
    R1–R5 per inverter, at a bounded time step (maxstep 5 ns, or 20 ns for the leak runs). Its read times are 0,
    D + reset_len + 0.05 tu, the comparator flip and the slot maxima, never 2 ns before an edge.
  - The prediction is built from stage D, and the comparison (compare_d2) compares words, outputs, cell bits and skew
    slots.
  - The only user of x_D is noise3.budget (a validation tool of the noise budget, not part of the campaign chain). It
    uses x_D only on silent slots (input present), as dx_D_silent; on fired slots it uses the latch shift.
- **How x_D is sampled.**
  - noise3.Net3.slot runs `meas tran qN find v(xn<j>.vq) at=T + D·tu − 2 ns`, then x = (1.25 − vq)/0.5. ngspice
    interpolates linearly between the two simulator time points around that instant.
  - At T + D the slot ends and the reset begins: on a fired slot, x falls from about 1.016 to about 0.73 within a few ns.
- **Why slot 1 differs (NOT1 9804, noise off).** From the DUPX trace of the identical noise-off run (vq saved):
  - in slot 1, the simulator stepped from T + 19 990.9 ns (x = 1.0158) straight to T + 20 003.6 ns (x = 0.8194, already
    after the drop);
  - linear interpolation at T + 19 998 ns gives 0.9056, an artifact: the true x there is flat at about 1.0157;
  - in slots 0, 2, 3 and 4 a time point fell within 0.5 ns of the read instant, and the reading is 1.0156–1.0157.
  - At zero amplitude every noise source is present: the trnoise grid of 0.4 µs and the window pulses vkw with 1 ns
    edges at T + D. These force time points at the edge, so the reading is correct (1.0155).
  - The artifact is deterministic. It reproduced exactly in the duplicate on clone B and in the campaign_run10 rerun
    (0.9056 three times).
- **Could a reading like this change a verdict or a margin? Not in the campaign chain.**
  - No gate verdict, margin, prediction or comparison reads x_D.
  - **In stage D:** no, it is not read.
  - **In the network check** (the in-deck gate): no; its x comes from its own maxstep-bounded runs, and its network
    fingerprint uses device vth and v(ibm), not x.
  - **The risk is in the noise-budget validation (noise3.budget).**
    - On a silent slot, the same edge sits 2 ns after the read. An interpolated value of order 0.1 x against a K3
      budget of 3σ ≈ 0.0075 x would show up as a spurious budget excess in dx_D_silent.
    - Only noise-off rounds lack the forcing time points. And the budget compares a noisy x_D with the noise-off one,
      so one bad noise-off reading would bias every difference taken from it.
    - In the dry runs no silent-slot x_D deviated: XOR3 and NOT1 silent readings agree to 0.001 x or better. But the
      mechanism can occur.
- **How often.**
  - **Yield lot (56 instances):** 0 readings; stage D records no inverter_x, and stage N was not run.
  - **The two dry runs and the campaign_run10 check.** 14 records scanned (XOR3 9803: N0–N3, zero, ref and DUPX;
    NOT1 9804: N0–N3, zero and DUPX), 468 x_D readings. Deviations above 0.01 x from the median of their inverter and
    state:
    - 1 confirmed artifact: NOT1 9804 N0 slot 1 (fired), 0.9056 against 1.0157, the same in its duplicate and in the
      third run;
    - 2 small deviations on fired slots of noisy rounds: NOT1 9804 N1 slot 3, 0.9956; N2 slot 3, 1.0017 (median
      1.0157). Their trace.raw files are deleted, so I could not establish whether they are this artifact or noise.
    - 0 on silent slots.
