# Development lot 2 of inverter instances (cell C5): the rule, written before the data

**Development work, not preregistered.** This rule is committed alone, before any instance of the lot runs. The lot
runs only after the owner's go.
- **Code:** the package of this folder at commit d25ee8e, cell C5: help mirror w = 2, l = 16 µm, J0 = 4.0
  (`design_sweep/SWEEP_2.md`). `config.json` is as at d25ee8e. Nothing in the code or the config changes during the
  lot.
- **Earlier instances:** the seeds used so far are 9901-9903 (cost check) and 9911-9970 (lot 1). The sweep's stress
  seeds 9928, 9944 and 9963 are among them. None of them counts here, and none is reused.

## Size and seeds

- **N = 60**, seeds **9711 to 9770** ([`JOBS`](JOBS)).
- **Why the range is clear:**
  - it is disjoint from 9901-9970 (the development seeds used so far);
  - it is disjoint from every campaign range found in the repository: 1000-1199, 2000-2399, 5001-5020, 6001-6100,
    7101-7103, 7301-7306, 7401-7412, 7701-7710, 7801-7805, 8301-8310 and 8501-8515.
  - A search of every fetched branch (main, the proof branches and the family-campaign branches) finds no number
    9711-9770 used as a seed. The only matches are decimals in a layout report (`0.9742`, …). Noise seeds are 5-digit
    (90000 + round).
- **Cost:** about 1 machine-minute per instance, as measured (C5: 52-60 s), so about 60 machine-minutes in all.

## What "usable" means (two counts, k out of n)

- **Eligible (K0):** the kernel's verdict on the instance's Lean gate is true for K0. That includes `StateBound`
  (max |x| ≤ H0·hl on both runs). The instance also needs:
  - one sample across its five runs;
  - silence with the input present;
  - firing with the input absent.
- **With room (K3):** the same for K3, which adds 3 sigma of `research/circuit/noise.json`.
- A job that fails, times out, or is not measured counts as not usable in both counts and stays in n.
- Every verdict is conditional on the open premises listed in each gate output:
  - the leak along the trajectory, a modelling step [I];
  - the measured real hypotheses, which are the simulation's claims;
  - the latch delay, measured rather than bounded.
- X, α and the latch are measured again on every instance.

## Target, fixed now

Both of these must hold:
- the **minimum K3 silence margin over all instances run is at least 0.05**; and
- **room in at least 57 of 60.**

Either missed: the verdict is **"C6 fallback"**, that is, C5 plus J0 = 4.4 (`design_sweep/SWEEP_2.md`). Both met: the
verdict is **"C5 holds"**.

## Stopping rule (applied by `driver.py --stop rule.json`)

- **Early stop:** after the first 20 finished instances, if fewer than 19 have room, no new job is started. The
  verdict is then "C6 fallback".
- **Compute ceiling:** 90 machine-minutes of summed job time. Once it is reached, no new job starts, and the
  instances not started are reported as not run; they count against room for the 57/60 target.
- Each job has a 30-minute timeout. At most 4 jobs run at a time on a 4-core machine.
- Free disk is checked (at least 20 GB) and reported before the run.

## Report

- eligible k/n and room k/n;
- min, median and max of the K0 and K3 silence and firing margins, δ, α, X (present and absent, against H0·hl) and
  the emission dates;
- every failure with its cause;
- wall time and machine-minutes.
