# G2 pre-freeze dry run (2026-11-25): ANDOR3 6104 on machines A and B, one container

**Local dry run. Development only; counts for nothing. No fix applied.** These are the raw outputs of the run, copied from
/home/user/g2run. Files over 50 MB and the pdk links are listed in NOT_COPIED.txt, with sizes and sha256.

## Setup
- **Trees.** Clones A and B, fetched by branch name:
  - research/layered-stage-d 26a2d9f8 (campaign_run11, envcheck_layered3, sealpush2);
  - research/layered-networks 458bc7a6;
  - research/inverter-instances d599300d.
- **Environment.** Each clone has its own PDK at 1232782c and its own numpy 2.3.5 venv. envcheck_layered3 passed on
  both (envcheck_A.txt, envcheck_B.txt).
- **Machine.** uptime -s 2026-11-25 18:57:30, 4 cores, 15 GB. Free disk was 55 GB at the start and 42 GB at the end.
  pgrep ngspice was 0 at the start and at the end.
- **Instance.** ANDOR3 6104, the lowest of YIELD's 3/24 with K3 room. It is K0-eligible and has no front end.
- **Seal log.** A local bare repo with the pre-receive refusal hook only (sealog_hooks.txt, sealog_refs.txt,
  sealog_git_log.txt).
- **The two runs.**
  - Machine A (PLAN_A.json, rootA): deck, D, seal, sealpush to evidence/combined-seals-K01 (commit e15d77c9), N0, N1 to
    N3 (round 1 with save_ref), C0 to C3 and U.
  - Machine B (PLAN_B.json, rootB): the remote duplicate. It fetches the seal log by name from the bare repo.
  - B's launch was refused while A's ngspice ran ("refused: 1 ngspice process(es) running"), so B ran after A.

## Results
| Item | Result |
|---|---|
| (a) ENDED DONE | **Pass**, on each machine. A ended at 20:56:12Z, after every A job (U included). B ended at 21:23:55Z, after its DUPX job. Nothing ties A's end to B's duplicate: A's PLAN has no remote_duplicates. |
| (b) verify | **Pass**: "verified" on rootA and on rootB. |
| (c) check_duplicate | **Pass: DUPLICATE IDENTICAL**, by A/noise tests/check_duplicate.py, unchanged. seal_fetch ok, seal_check ok, the seal sha equal to A's pushed line. |
| (d) C0 to C3, U | **Pass.** All four comparisons "agrees", with 0 differences. U holds: 8 patterns, 0 fires. |
| (e) check_noise_identity2 | **Pass** (zeroA/identity2.txt): rootA N0 against a scale=0 round 1 (zeroA/Z). 4 of 200 u differ, each within ±1 in the last digit. Listed only: 40 latch dates differ, by 2 to 4 ns, at most −15 and +10 ns. |
| (f) analyze7, twice | **Byte-identical** (an7_1, an7_2), and the seal regenerated identical. **But log_ok is false**: no push time was recorded (defect 1), so K0 and K3 read not_sealed. |
| (g) cost | See below. |

**Cost, in CPU-min (wall in brackets), against the plan:**

| Step | Actual | Plan |
|---|---|---|
| D | 47.4 (47.9) | 40 |
| N0 | 26.9 (27.2) | 27 |
| N1 | 38.6 (39.0) | 26 |
| N2 | 38.1 (38.4) | 26 |
| N3 | 38.7 (39.1) | 26 |
| U | 2.2 | |
| DUPX N0 | 27.0 (27.2) | |
| scale=0 round 1, run alone | 32.1 (32.3) | |

- N1 to N3 ran in parallel, on 3 of 4 cores.
- The critical path was 6852 s.
- Disk: rootA 4.7 GB, rootB 0.84 GB, the whole run folder 13 GB.

## Defects (none fixed)
1. **My setup error.** The bare repo lacks sealpush.py's post-receive push_times hook, so analyze7 times=bare has no
   push time for the seal.
2. **save_ref on a network without inverters saves nothing.**
   - N1/ref_extract.json reads ok false, and the whole trace is kept.
   - The step still reads done, and analyze7 is silent on it.
   - Nothing refuses save_ref_round when the network has no inverters.
3. **The noisy rounds cost more than planned:** about 38.5 CPU-min against 26 (32 when run alone), and D 47 against 40.
4. **K3 room holds only under one-port.** analyze7 max_rule_comparison: 6104's K3 room holds only under the one-port
   testError rule. This is informational.
5. **One container ran both machines,** so B ran after A rather than alongside it.

## Timeouts (read from campaign_run.py)
- **The defaults.** DEFAULT_TIMEOUT, in seconds:
  - deck 120, inverters 3600, D 7200, N 7200, C 300, U 3600, dup 7200;
  - seal 120, which is also the limit of the sealpush step.
- **Overrides.** PLAN groups[g].timeout_s overrides the instance steps only. U, dup and DUPX, and the duplicate's C use
  the defaults.
- **At the limit.** The child runs in its own session, and a Timer sends SIGKILL to its process group. The step is
  recorded in status.json as {status "timeout", why "more than N s", wall_s, cpu_s, ended}.
- **After a timeout.** The step is never re-run, and the instance stops there. A step found running at a resume is
  marked "interrupted". U, dup and DUPX record timed_out and exit in RESULT.json.
- **session.py** has its own limits: 600 s for the ngspice size run, 60 s for the close wait.
- **Not hit.** No limit was hit in this run.
