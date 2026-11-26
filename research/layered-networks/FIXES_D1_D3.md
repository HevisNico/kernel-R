# D1–D3 of the final dry run: the fixes and their checks (2026-11-26). Development only; nothing pushed

## D1: analyze10 verifies stage_d6 seals
- **How the script is chosen.** stage_d6 names itself: its predictions carry `code["stage_d6.py"]`. analyze10 takes the
  latest stage_d<N>.py the sealed prediction names (stage_d6, then 5, 4, 3). It requires the kernel field to agree
  with that name: stage_d6 named ⇔ `kernel` present. Otherwise the seal is refused, with the reason.
  - So the name decides, and the kernel field is a consistency check.
  - The frozen chain is unambiguous without a new driver: TEMPLATE_CAMPAIGN_3's stage_d_script is stage_d6.py, and its
    predictions name stage_d6.py.
- **The regeneration** runs stage_d6 on the kernel library built from the pinned sources (campaign_run14.build_kernel,
  refused on a changed source). It must be **byte-identical** to the seal, the kernel field included.
- **On the final dry run's 8 roots, without simulation:**
  - all 8 seals regenerate identically, and seal_defects is empty;
  - two runs are byte-identical (RESULTS.json 112b9253…, 63 s and 36 s);
  - the counts are those expected: NOT1 K0 held 6, K3 held 4 with 2 no_prediction (6217 and 6219 have no room); XOR3
    K0 and K3 held 1; ANDOR3 K0 held 1, K3 no_prediction.
- **Against analyze9.** The differences are only the counts D1 zeroed: `instances[*].seal/K0/K3`, `groups[*][K].counted /
  not_sealed / verdict`, `counts` and `seal_defects`, plus the new keys (format, analyze10_sha256, stage_d_script_rule,
  kernel_sources_sha256). d4_audit and controls are equal.
- **tests/test_analyze10.py:**
  - the seal regenerates;
  - refused: stage_d6 named without a kernel field; a kernel field without stage_d6 named; a changed kernel field ("differs
    from the seal in ['kernel']");
  - analyze3's old order reproduces D1.

## D2: the remote duplicate without manual steps (campaign_run15, plan_split3)
- **plan_split3.py** names each duplicate's home_machine, home_branch and home_instance.
- **campaign_run15 refuses a duplicate** without home_branch, with this machine's own branch as its home, or with a
  hand-written seal_log/seal_dir.
- **The wait.**
  - The duplicate fetches the home branch by name every interval_s = 60, for at most limit_s = 21600 (6 h, from
    TEMPLATE_CAMPAIGN_3), until SEALS.txt has the instance's line.
  - It then sets the tip as its seal_log, in the plan's entry in memory that stage N reads (the plan file is not
    changed).
  - It checks the line and the folder as campaign_run10 did, and only then runs N0.
  - At the limit it is not completed (ok false, not_completed, the reason), and nothing runs.
  - The attempts are in DUPX_<inst>/seal_wait.json.
- **The test**, a short NOT1 run on two fresh clones at 5ec35421 (plan_split3 m = 8 on NOT1 6212, 6213):
  - K03 (clone B) holds only the duplicate of NOT1_6212. It was launched at 11:11:24, before its home existed. It polled
    9 times, from 11:11:39 to 11:19:39 (waited 480 s).
  - K01 (clone A, the home) was launched at 11:12:55. Its seal reached the bare repository at 11:19:20 (post-receive
    log).
  - The duplicate found the line at 11:19:39, then fetched and checked the seal (ok) and ran N0 (89 s, exit 0).
  - analyze10 on the two roots, twice (byte-identical): **DUPLICATE IDENTICAL**, comparison agrees, the seal check ok,
    NOT1 K0/K3 held 1.
  - A defect of my own was found and fixed on the way. The first attempt failed because stage N reads the seal log from
    the plan's duplicate entry, not from the call's argument. It was fixed in 5ec35421, before this test.
- **tests/test_campaign_run15.py** (3/3):
  - the templates and refusals;
  - the wait on a simulated clock: no branch, then a branch without the line, then the line pushed during the wait;
  - the limit giving not_completed;
  - the launch refused below 30 GB.

## D3: disk
- **The rule as decided.** TEMPLATE_CAMPAIGN_3 has disk_launch_gb 30, and campaign_run15's launch refuses below it.
  OUTROOT/DISK_AT_LAUNCH.json records the free space. disk_guard_gb stays 20 during the run.
- **The per-machine peak** (disk_peak.py → dev/disk_peak/DISK_PEAK.json). It uses plan_split3's assignment for NOT1 60,
  ANDOR3 32, XOR3 37, the measured raw and extract sizes, and 4 jobs.

  | | m = 12 | m = 8 |
  |---|---|---|
  | kept at the end, per machine (worst: room everywhere) | 1.9–3.9 GB | 2.8–5.8 GB |
  | transient: the 4 largest raws at once (4 noisy XOR3 rounds, 2.70 GB each) | 10.8 GB | 10.8 GB |
  | **peak, worst** | **12.7–14.7 GB** | **13.6–16.6 GB** |
  | peak, expected (p_room) | 11.6–13.6 GB | 12.1–15.0 GB |

  Every machine holds 2–5 XOR3 instances, so the transient term is the same everywhere.
- **The finding: 30 − 20 = 10 GB is below every machine's peak.**
  - With 30 GB at launch, a machine whose XOR3 rounds end together drops below the 20 GB guard. Its next steps are held,
    including the comparisons that would delete the raws, so it stops until someone frees space.
  - In the final dry run the three XOR3 rounds ended a little apart, and free space at 30 s sampling fell from 27.3 to
    24.7 GB. So it did not happen there, but nothing prevents it.
- **For the owner to choose:**
  - **(a)** disk_launch_gb ≥ 20 + 16.6 → **40 GB** (recommended; nothing else changes);
  - **(b)** keep 30/20 and let the comparison steps C<n> (which delete a raw) start below the guard: new code;
  - **(c)** lower jobs on machines with XOR3: this slows the window.
- **Not applied.** The template keeps 30.
