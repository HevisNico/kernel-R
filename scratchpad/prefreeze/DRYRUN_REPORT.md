# Pre-freeze dry run, 2026-11-25 (local only, nothing pushed, no fix applied)

## Setup
- **Clone 1.** One fresh clone (single branch research/layered-stage-d), with research/layered-networks and
  research/inverter-instances fetched by name as worktrees. Tips:
  - stage-d a398d1f2c6ab7c86a7807ed751096da160812d47;
  - layered-networks 458bc7a6d763127ff2fe0214e2cb79a1a6549f9b;
  - inverter-instances d599300d51fcf3a1a4c33d103b89827f8ac4da41.
- **PDK.** Fetched fresh with the repository's research/circuit/fetch_pdk.sh at 1232782c. The kit and noise trees'
  research/circuit/pdk are symlinks to it.
- **Clone 2** (the duplicate): the same three tips, with its own PDK and its own venv.
- **Python.** A numpy 2.3.5 venv (pip, PyPI wheel sha256 11e06aa0…).
- **envcheck_layered.** ok on both clones (lean, ngspice, numpy, pdk), and ENV.json was written.
- **Machine.**
  - uptime -s was 2026-11-25 12:18:49 at the start and at the end (the container restarted after the yield lot).
  - 32 GB free at the start, 24 GB at the end.
  - pgrep ngspice was 0 before each launch.
  - nproc 4.
- **Instance.** XOR3 9803, which is in the exclusion inventory (EXCLUDED_ALL.txt), run with campaign_run8. The plan
  set U_groups XOR3, rounds 3 and save_ref_round 1, and no d4_audit seed.
- **Seal log.** Pushed to a local bare repo:
  - pre-receive refuses a deletion or a non-fast-forward update (my reading of "refusal hook": the brief does not
    define it);
  - post-receive logs the push times.

## Chain (out1, launch 12:23:29Z, end 15:25Z)
| Step | Result | CPU min | wall min | Planned CPU min (plan_split COST) |
|---|---|---|---|---|
| inverters (indeck_noise4) | K3_BUDGET ok (both gates record delta 2506/1e6, eta 2597/1e6); n0 and n1 K0 and K3 | 12.4 | 8.0 | 11.5 |
| D (stage_d5) | measured; eligible K0, room K3, no failing clause | 60.5 | 61.3 | 57 |
| seal, sealpush | pushed 243b918d at 13:32:45.87Z; stage N started 2.013 s later | 0 | 0 | |
| N0 (controls4), C0 | agrees (23 letters, 4 outputs, 16 cell bits, 2 skew slots) | 48.4 | 48.8 | 42 |
| N1 (controls5 save_ref=1), C1 | noisy, agrees | 63.0 | 63.8 | 62 |
| N2, C2 | noisy, agrees | 61.4 | 62.2 | 62 |
| N3, C3 | noisy, agrees | 63.0 | 63.8 | 62 |
| U (controls4) | holds: 0 R-cell fires, 4 inverter fires reported | 3.2 | | about N0 (42) |
| DUPX N0 from clone 2 (out2) | ok | 46.9 | 47.6 | 42 |
| D4 audit | not triggered (no d4_audit seed for one instance) | | | |

- **Instance total.** 308.7 CPU-min (5.15 core-h), against 296.5 planned (+4 %). Critical path 3.03 h (chain 1.97 h,
  then the longest round 1.06 h), within the 5.833 h window.
- **Controls.** 50.1 CPU-min, against 84 planned.
- **Plan §5.** It says XOR3 noisy ≈ 42 CPU-min. The measured 61–63 matches plan_split's 62, not §5.

## Checks
- **(a) PASS.** `campaign_run.py verify out1` prints "verified". SHA256SUMS.pre_post_writes and SHA256SUMS differ
  only on the RESULT.json line. out2 is verified too; there the rewrite also added DUPX_XOR3_9803/duplicate_here.json.
- **(b) FAIL** (check_duplicate.py out1/XOR3_9803/N0 out2/DUPX_XOR3_9803/N0):
  - input.spice identical; noisy_record.json identical;
  - trace identical by digests (data 88b39efa…, header without Date:); session.log identical under the criterion;
  - but "comparison.json: present in one folder only", so DUPLICATE DIFFERS. See defect 3.
- **(c) FAIL** (check_noise3_identity N0 against a separate controls4 round 1 at scale=0):
  - equal: the decks outside the noise lines, the words, lessons, tests, skews and emissions;
  - 3 of 232 u differ by 0.1 µV, the record's last printed digit:
    - slot 11 lesson c1_0 port 0: −0.0117282 against −0.0117283;
    - slot 13 lesson c2_0 port 0: −0.0234327 against −0.0234326;
    - slot 24 test c2_0 port 0: −0.0234312 against −0.0234311;
  - allowed and listed: 38 latch dates (shifts −4 to +17 ns) and 108 inverter x readings (max 0.00106 x);
  - the same 3 of 232 as NOISE3_REPORT's XOR3 row.
- **(d) PASS, read from a separate rerun.** The campaign root's N1 trace was deleted (defect 2), so round 1 was rerun
  with controls5 save_ref=1 outside the root. tests/check_ref_level.py:
  - n0: rms(e) 370.1 µV against nzm 370.3 (0.9996); 0.886 × the noise4 budget of 417.6 µV;
  - n1: 387.3 µV against 387.5 (0.9996); 0.928 × the budget;
  - lag 12.3 and 13.8 ps; residual max 28.6 and 28.4 µV; kickback about 337 mV.
- **(e) PASS.** analyze6 (times=bare) ran twice, byte-identical. Seal regenerated identical, log_ok, margin 2.013 s,
  0 seal defects. XOR3 9803 counted at K0 and K3, not refuted.
- **(f).** See the chain table.
- **(g) PASS.** out1 is 20 MB. Every trace.raw (N0 1.85, N1 2.72, N2 2.67, N3 2.69, U 0.02 GB) was deleted after its
  digest. The transient peak was about 8.1 GB, with N1–N3 in parallel. out2 keeps its DUPX trace.raw (1.8 GB), by
  campaign_run5's rule.

## Defects (none fixed)
1. **DONE before the remote duplicate.** On a root with remote_duplicates, campaign_run2 writes SHA256SUMS,
   INVENTORY_END and DONE (15:25:43), and `campaign_run8 wait` prints "ENDED DONE", before campaign_run4 runs the
   remote duplicate (ended 16:13:17). RESULT.json and SHA256SUMS are rewritten afterwards. A machine following the
   runbook would close, verify ("verified" on the partial root) and commit mid-run.
2. **The save_ref trace is deleted.** The save_ref round's trace.raw is deleted when its comparison agrees
   (campaign_run5's raw rule, which keep_raw sets per instance, not per round). The record keeps only the vector
   names, so (d) cannot be read from a campaign root.
3. **A remote duplicate always "differs".** A remote duplicate (DUPX) runs no comparison, so check_duplicate reports
   "comparison.json present in one folder only", and every cross-machine duplicate fails the criterion even when
   everything else is identical.
4. **The zero-amplitude identity fails as written.** check_noise3_identity requires u bit-equal; the run is equal
   only to the record's last digit (3 of 232 at 0.1 µV, reproducible). Either the criterion or the claim must change.
5. **The numpy hash depends on the venv path.** ENV.json's numpy record_sha256 covers dist-info RECORD, whose
   bin/f2py and bin/numpy-config hashes include the venv's path. Two machines with the same numpy therefore get
   different static_sha256 (here 02ff71db against a230eb9f). The within-root check is not affected; a cross-machine
   comparison is meaningless.
6. **The core budget omits the remote duplicate.** RESULT.json core_budget is written by campaign_run3 before
   campaign_run4's remote duplicate runs: out2 reports peak_in_use 0 although it ran one job (cosmetic).
7. **A second launch is refused while ngspice runs** (by design). The duplicate from the second clone could only
   start after the main run ended, which adds 47.6 min of wall time on one machine.
8. **Cost notes.**
   - Plan §5's XOR3 noisy figure (42 CPU-min) is stale; the measured value is 61–63.
   - U costs 3.2 CPU-min, against expected_cost's assumption of about N0.
   - N0 is 15 % above plan.

## Predictions and verdicts (dev seed, count for nothing)
- **Prediction.** Eligible K0, room K3, every cell measured, no failing clause.
- **Verdicts.** C0–C3 agree.
- **Untrained network.** U holds.
