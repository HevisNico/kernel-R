# The inverter's K3 budget at the injected noise (noise4), and the comparator reference saved (controls5)

**Development only, nothing preregistered.** These are new files only: `noise4.py`, `noise4_budget.json`,
`controls5.py`, `tests/check_ref_level.py`. The following stay as pushed: controls4.py, noise3.py, the gate
(research/inverter-instances `invinst/gate.py`) and research/circuit/noise.json.

## noise4: the K3 budget at the measured level (the owner's decision)

- **Method.** Each σ is budgeted at the **larger of two measures**, from two noisy NOT1 runs of dev seed 9801 with
  two noise seeds, both read by `tests/check_noise_sources.py`.
- **Seed 98011.** Round 1, from controls4: `dev/controls4/not1_N1a`.
- **Seed 98014.** Round 4, from controls5 with save_ref=1: `dev/controls5/seed2_N4`. It was chosen as an unused seed:
  - the dev noise seeds used so far are 98011–98013, 98021–98022 and 98031;
  - the dry-run spec seeds 9804–9806 give noise seeds 98041 and up;
  - the rehearsal seeds are not drawn yet.
- **The constants** are in `noise4_budget.json`. `noise4.py check` verifies each measure against its
  noise_sources.json and the chosen σ as the larger of the two.
- **The R cells** are unchanged (campaign (a)'s convention).

| | noise.json (the gate today) | seed 98011 | seed 98014 | **noise4 (the larger)** |
|---|---|---|---|---|
| comparator σ_δ (total vnzm rms) | 335.0 µV, 6.70e-4 x | 417.6 µV, 8.352e-4 x | 347.4 µV, 6.947e-4 x | **417.6 µV, 8.352e-4 x** (×1.25) |
| mirror charge σ_η (sd per D window, n = 130) | 7.843e-4 x | 8.653e-4 x | 7.988e-4 x | **8.653e-4 x** (×1.10) |
| K3 allowance δ = 3σ_δ (rounded up to 1e-6) | 2011/1000000 | | | **2506/1000000** |
| K3 allowance η = 3σ_η | 2353/1000000 | | | **2597/1000000** |

- **Both maxima come from seed 98011,** so the allowance is the one first computed.
- **Seed 98014 is closer to noise.json.**
  - Comparator white part: 310.8 µV, against vnmw 316.6.
  - So its flicker part is about 155 µV, against about 264 µV with seed 98011.
  - Mirror sources: 0.461 and 0.465 nA rms, against inmw 0.490.
- **Run-to-run spread.** The white mirror sources differ by about 6 % between the two seeds, and the two halves of one
  run differ by about 3 %. That is more than independent samples would give, so two runs are a small sample. Within
  one run, the comparator input matches the source exactly (0.9994 and 0.9995 of nzm's rms).

**What the gate's K3 budget must read:**
- `allowance_K3` in `research/layered-networks/noise4_budget.json`: δ = 2506/1000000 and η = 2597/1000000, in x.
- K0 is unchanged.
- Nothing else in the gate changes.

### The dev inverters under the new budget (`noise4.py room`, saved as `dev/noise4/room.json`)

- **Method.** Only the gate's Python mirror is used (gate.py at d599300: premises, measures, best_early, design),
  with the stored measures. Nothing is simulated and no Lean file is compiled (the kernel agreed with the mirror on
  60 / 60).
- **Reproduction first.** Under the noise.json allowance the mirror reproduces every stored K3 verdict and margin
  (62 / 62).

| Inverters | K0 eligible | K3 room, noise.json | **K3 room, noise4** |
|---|---|---|---|
| dev lot (60 instances) | 59 | 58 | **58** (none lost) |
| XOR3 9803 in network, n0 and n1 | 2 | 2 | **2** |

- Every margin falls by the same amount: the silence margin by 0.00089 x and the firing margin by 0.00074 x.
- The tightest instance with room is 9963, whose silence margin goes from 0.0255 to **0.0246**.
- The two failures are unchanged.
  - **9944:** eligibility (StateBound), whatever the allowance.
  - **9928:** SilenceAfter. Its margin goes from −0.00003 to −0.00092.
- **Caveat.** These sigmas are the larger of two 2.6 ms runs, not a population estimate. The flicker part
  (about 155 or 264 µV) is the least well determined.

## controls5: the comparator reference saved, for the pre-freeze dry run

- **The option.** `controls5.py stagen … save_ref=1`, off by default. It is controls4's stage N with this one
  option.
- **What it saves.** In one noisy round, the trace also holds each inverter's `xn<j>.vrefm` (the reference before
  the noise) and `xn<j>.vrefmn` (the comparator's input). The record then carries `"saved_ref"`.
- **Refusals (exit 2, before any session):** save_ref=1 on round 0, and save_ref other than 0 or 1.

**Validation, NOT1 9801:**

| Check | Result |
|---|---|
| option off, round 0, against controls3 (`tests/check_controls4.py`, dev/noise3/not1_seal_N0) | input.spice byte-identical, record identical without cost, trace and digest present |
| option off, round 1, against a controls3 round 1 with the same seal (dev/controls4b/c3_N1) | the same: identical |
| option off, round 1, against controls4's not1_N1a (`tests/check_duplicate.py`) | **DUPLICATE IDENTICAL** |
| option on, round 1, against option off | input.spice identical; record identical apart from `saved_ref`; the same 76378 time points; every common vector bit-identical; two vectors added |

**The level read at the comparator input** (`tests/check_ref_level.py`, saved as `dev/controls5/ref_N1/ref_level.json`;
the second seed's in `dev/controls5/seed2_N4/ref_level.json`, 347.1 µV against nzm's 347.3, with the same 12.3 ps lag
and 28 µV maximum residual):

- **What the input carries.** e = vrefmn − vrefm is the injected vnzm plus two deterministic parts.
  - **A lag of 12.3 ps × dvrefm/dt** while the reference ramps. The input is loaded by the comparator's device.
  - **The comparator's kickback at each trip:** about 332 mV peak, for a few ns.
- **The level.** Outside ±200 ns of the 5 latch dates (6496 of 6501 grid points):
  - rms(e) = **417.2 µV**, against rms(nzm) = 417.4 µV on the same points (ratio 0.9994);
  - white part 324.2 µV, against 324.5 µV.
- **The residual.** After removing the lag, the residual is 0.28 µV at the median and 28 µV at most. 50 ns before
  each latch it is −16 to −17 µV.
  - This deterministic residual is also in a noiseless run, so it is inside the measured δ.
  - It is about 5 % of σ.
- **So the comparator sees exactly the injected vnzm,** at 1.245 × noise.json's level and 0.999 × noise4's budget.
  This is not an independent estimate: it is the same noise seed as not1_N1a, read at the comparator's input rather
  than at the source.

## Cost

- **Runs:** five NOT1 runs of 1.2 to 1.7 CPU-min (controls5 off at rounds 0 and 1, on at rounds 1 and 4, and controls3
  at round 1). The regate takes seconds.
- **Disk:** trace.raw is 34.8 MB with save_ref, against 33.6 MB without. For XOR3, keep save_ref to the single dry-run
  round, and delete each raw file after its digest.
