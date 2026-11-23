# Development lot of inverter instances: the rule, written before the data

**Development work, not preregistered.** This rule is committed alone, before any instance of the lot runs. The lot
runs only after the owner's go. Code: the package of this folder at commit cd8823e, the redesign (`J0` = 4.0) with
the open premises marked in the gate output (`config.json` as at 1345f4b). This version replaces the draft of ada8f0e, which was written for the
unredesigned cell (J0 = 3.0). No lot ran under that draft.

## Size and seeds

- **N = 60 instances**, seeds **9911 to 9970** ([`JOBS`](JOBS), one seed per line).
  - The range is outside every campaign range found in the repository (the highest is 8501-8515). It is also outside
    the three cost seeds 9901-9903.
- **Sized from the measured cost.**
  - 3 seeds: 0.93-0.96 machine-minutes per instance, and about 1 s of Lean per instance. This was measured
    twice: before the redesign and after it (3 jobs, 2.9 machine-minutes in all).
  - So 60 instances are about 58 machine-minutes, about 15 minutes of wall time on one 4-core machine with 4 jobs.
  - After the redesign, the 3 cost seeds gave 3 eligible out of 3, and 3 with room out of 3. With N = 60, the 95 %
    Wilson interval at a rate near 0.9 is about ±0.08. The width is reported, not used to decide.

## What "usable" means (two counts, reported separately)

- **Eligible (K0):** the kernel's verdict on the instance's generated Lean file is `true` for K0. The instance also
  needs:
  - all five runs share one sample (fingerprint);
  - it is silent with the input present;
  - it fires with the input absent.
- **With room (K3):** the same, for K3: K0 plus 3 sigma of `research/circuit/noise.json`.
- A job that fails, times out, or is not measured (no threshold crossing, no emission) counts as **not usable** in both
  counts, and stays in n.
- Every count is reported as **k out of n**, with the list of seeds and of the premises that failed.

## Stopping rule (decided now, applied by `driver.py --stop rule.json`)

- **Early stop:** after the first 20 finished instances, if fewer than 6 are eligible (K0 below 30 %), no new job is
  started. The lot stops and the verdict is "redesign".
- **Final verdict:** on all instances run:
  - if fewer than 18 of 60 are eligible (K0 rate below 30 %), the verdict is "redesign";
  - otherwise "continue", and the rate goes to the owner to size the Monte Carlo sample.
- The 30 % threshold is a placeholder, kept as the coordinator asked. The final number goes to the owner once
  the redesigned margins are known.
- The 30 % threshold is a development choice. It is a design-health bound, not a compute bound: at one machine-minute
  per instance, even a 30 % rate is cheap to draw around. Below it, the cell's silence margin is too thin for mismatch.
  9903 failed on help-mirror mismatch alone.
- Nothing is changed during the lot: no config, no code, no seed. An error that stops the lot is reported as it is.

- Every verdict is conditional on the open premises listed in each `GATE_*.json` (one constant leak [I], the
  real bridge, the latch). Counts are reported with that status.

## Compute ceiling

- **90 machine-minutes**, the summed wall time of the jobs (about 1.5 times the estimate). Once it is reached, no new
  job starts, and the instances not started are reported as not run.
- Each job has a 30-minute timeout. At most 4 jobs run at a time on a 4-core machine.
- Free disk is checked (at least 20 GB) and reported before the run.
