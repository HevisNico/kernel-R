# Noise study, phase 0: feasibility

Phase 0 of the study committed in [`../COMMITMENT.md`](../COMMITMENT.md). **Feasibility only, no claim.** Nothing
here strengthens or weakens campaigns 1 to 3, and nothing here is preregistered. The validation criteria of
section 4 are a **proposal** for the owner to fix before phase 1; they were written after the pilot below and
must be applied to new draws.

Simulated: the nominal cell (section `tt`, no mismatch seed) and, for the operating-point checks only, the
development instances 7101, 7102 and 7103 (section `tt_mm`). No other seed was simulated.

## Environment

The pinned toolchain of the campaigns was rebuilt in this container and checked by hash:

| | Pinned | Here |
|---|---|---|
| ngspice 42 (`/usr/bin/ngspice`, Ubuntu package `42+ds-3build1`) | `820658317b0b5403…b821b7fc45` | identical |
| PDK `skywater-pdk-libs-sky130_fd_pr` | `1232782c1b9fab3aacda74d67ce7c92bf7da8105` | identical |
| Python 3.12.3 (`/usr/bin/python3.12`) | `e50d468e8b0adfb0…fdfe4bb150f` | identical |
| numpy 2.3.5, SHA-256 of its `RECORD` | `064003bdb6f9f7bb…564917be2fb` | identical, in a venv at `/home/user/owner-prep/venv312` |

The numpy `RECORD` holds the absolute path of the venv (in its `bin/f2py` and `bin/numpy-config` lines), so the
pinned hash is reproduced only by a venv at that path. A venv elsewhere gives another hash for the same numpy.

Ubuntu 24.04.5, 4 processors, 16 GB. All runs below were made 4 at a time, as in the campaigns.

## 1. Device noise in a transient

**ngspice 42 adds no noise of the device models to a transient.** This was checked on the pinned binary:

- A SKY130 `nfet_01v8` biased in saturation (w 2, l 0.5, 0.7 V on the gate, 20 kΩ load), transient over 200 µs with a
  10 ns step. The output departs from its mean by 6.7e-14 V rms, and two runs give the same number to the last
  digit. That is numerical error, not noise. (Its thermal noise alone would be several µV rms in that band.)
- The binary contains a resistor flag `noisy` and a variable `enable_noisy_r`. In four variants (instance flag,
  model flag, the variable set in the start file and in the control section, with and without a `trnoise` source
  in the deck), a 1 MΩ resistor on 1 pF gave exactly 0 V rms in a transient, where kT/C is 64 µV. In `.noise` the
  same flag works (`noisy=0` removes the resistor's contribution), and the pilot below uses it that way.
- `DESIGN.md` already reports that a run without the injected sources, run again, gives the same file byte for byte.

**`.noise` does have the device noise of the SKY130 models.** The BSIM4 cards carry thermal noise and the unified
flicker model (`fnoimod = 1`, exponents `ef` 0.84 for `nfet_01v8`, 1.0 for `pfet_01v8`, 0.88 for
`pfet_01v8_lvt`). With a fifth argument to the `noise` command (`noise v(out) src dec 20 1 1e8 1`) ngspice
writes, for every transistor, its output noise density split into channel thermal (`.id`), flicker
(`.1overf`), gate currents and body resistances. This works on the full flattened network deck (232 transistors per
cell) in about 30 s.

**So an equivalent transient model has to be built from `.noise`.** The construction tried in the pilot:

1. **Freeze an operating point of the cell** in the network deck of `../../network-circuit/net.py`, unchanged
   apart from: the preset switch of each integrator replaced by a noiseless 1e14 Ω resistor (the stored voltage
   keeps a DC solution through the preset loop, whose loop gain falls to one near 0.5 Hz, below the band), the
   bench resistors (10 kΩ control filters, 1 kΩ injection resistors) made noiseless, and `ac 1` on `vcm` as the
   input that the `noise` command requires. The mismatch seed is set with `setseed` then `reset`, as in the runs.
2. **Rank the devices** by their share of the output noise power over 10 Hz to 1.25 MHz, and keep the largest until
   they make 99 % of it.
3. **Find the noise current of each kept device**: its thermal and flicker output densities divided by |H|², where
   H is the transfer from a unit AC current between its drain and source to the output (one AC analysis per
   device, in the same deck). This gives a white density A (A²/Hz) and a flicker coefficient B, with
   S(f) = A + B / f^ef.
4. **Put back one current source per kept device**, between its drain and source: a `trnoise` voltage source
   (white part and 1/f^ef part, sampled every 0.4 µs as in the campaigns) drives a VCCS. All noise sources stay
   voltage sources, which is the rule of `DESIGN.md` ("Solver").
5. **Calibrate `trnoise`.** Its 1/f amplitude parameter is not an rms value: see 1.1.

### 1.1 The `trnoise` generator ([`gen.py`](gen.py), [`GENERATOR.json`](GENERATOR.json))

There were 40 separate processes per exponent, each running 40 ms with no circuit, NT = 0.4 µs, NAMP = 1 mV for
the 1/f^α part and NA = 1 mV for the white part.

| α | c(α) = f^α S(f) / NAMP², 1 kHz to 500 kHz | spread of c between bands, 100 Hz to 500 kHz | per-draw spread | white S / (2 NT NA²) | sd of the mean of a 40 ms draw, / NAMP |
|---|---|---|---|---|---|
| 0.84 | 0.0405 | 0.0406 to 0.0414 | ±1.5 % | 0.996 to 1.002 | 1.38 |
| 0.88 | 0.066 | 0.063 to 0.069 | not computed | 0.96 to 1.02 | 1.70 |
| 1.00 | 0.316 | 0.290 to 0.326 | ±1.8 % | 0.95 to 1.01 | 2.05 |

- **The slope is right** from 100 Hz to 500 kHz, and the white part is the ideal sampled white noise up to
  1.25 MHz. Above 500 kHz the 1/f^α part is 20 % above its fit. The band from 25 to 50 Hz holds one bin per draw and
  is not resolved here.
- **The amplitude of a draw is stable**: c varies by under 2 % between draws, and the deck around the source does
  not change it (2 or 3 sources, with or without the start file of the campaigns).
- **NAMP is not the rms of the flicker part.** With α = 1, the mean of a 40 ms draw has a standard deviation of
  2.05 NAMP. `../../circuit/noise.py` gives `trnoise` the rms of the flicker part between 100 Hz and 1.25 MHz as
  NAMP. Phase 1 found that "the flicker amplitude given to the generator for `nzo` is 0.038 mV rms; the run mean it
  produces is twice that" (`../../network-circuit/phase1/NOISE.md`, section 3). That ratio is what this
  calibration predicts. **It is consistent with, not proof of, the cause of the overstatement.**

## 2. The pilot: one operating point, nominal cell ([`pilot.py`](pilot.py))

**The hold point.** One cell, no pulse, preset ended, output `v(xa.vmem1)`: the stored voltage of port 1. This is
the path that `NOISE.md` found to make the run offset (the integrator amplifier, coefficient one).

### 2.1 Extraction ([`MODEL_nominal.json`](MODEL_nominal.json))

240 devices have a noise vector at that output. Four make 99.9 % of its noise power from 10 Hz to 1.25 MHz:

| Device | Share | White A, A²/Hz | Flicker B (S = B/f^ef) | Corner, Hz | Gate and body parts |
|---|---|---|---|---|---|
| op-amp `xm4` (NMOS load) | 0.447 | 2.43e-24 | 1.48e-19 | 497 000 | 1e-5 |
| op-amp `xm3` (NMOS load) | 0.424 | 2.43e-24 | 1.48e-19 | 497 000 | 1e-5 |
| op-amp `xm1` (PMOS input) | 0.064 | 8.87e-25 | 1.44e-20 | 61 000 | 5e-5 |
| op-amp `xm2` (PMOS input) | 0.064 | 8.87e-25 | 1.44e-20 | 61 000 | 5e-5 |

- **The extraction is consistent.** For each device the extracted thermal density, and its flicker density times
  f^ef, are flat over the band to within a ratio of 1.00001 between the 95th and 5th percentiles. That is what a
  stationary white plus 1/f^ef source requires, and the `ef` of the model card holds exactly.
- The flicker of the NMOS load dominates below about 500 kHz. That is not what the injected model assumes: it puts
  14 % of the flicker on the op-amp and the rest of its rms in a white part.
- **The noise of the stored voltage at that point**, from `.noise`: 13 µV rms from 1 to 10 Hz, 67 µV from 10 Hz to
  1.25 MHz, and **172 µV above 1.25 MHz**. A transient whose sources are sampled every 0.4 µs cannot hold that last
  part. A read is a 40 µs mean, which removes it, but a sample can catch it (section 3).

### 2.2 Transient against `.noise` (`TRAN_*.json`)

Eight draws of 40 ms per model, one simulator process each, on the same frozen deck. The quiet run sets the
numerical floor at 0.4 pV, nine orders below the noise.

Mean periodogram of the stored voltage (Hann window) over the `.noise` density, by third of a decade. The ± is
the standard error over the 8 draws:

| Band, Hz | Bins per draw | Device model | Injected model (as in campaigns 1 to 3) |
|---|---|---|---|
| 46 to 100 | 2 | 0.52 ± 0.07 | 3.02 ± 0.78 |
| 100 to 215 | 5 | 0.81 ± 0.16 | 3.74 ± 0.78 |
| 215 to 464 | 10 | 1.23 ± 0.13 | 2.46 ± 0.33 |
| 464 to 1 000 | 21 | 0.97 ± 0.17 | 3.08 ± 0.20 |
| 1 000 to 2 154 | 47 | 1.05 ± 0.06 | 2.94 ± 0.17 |
| 2 154 to 4 642 | 99 | 1.00 ± 0.06 | 2.61 ± 0.11 |
| 4 642 to 10 000 | 214 | 0.97 ± 0.03 | 3.18 ± 0.11 |
| 10 000 to 21 544 | 461 | 1.00 ± 0.02 | 4.09 ± 0.08 |
| 21 544 to 46 416 | 994 | 0.95 ± 0.02 | 6.35 ± 0.10 |
| 46 416 to 100 000 | 2 141 | 1.01 ± 0.02 | 9.67 ± 0.14 |
| 100 000 to 215 443 | 4 612 | 0.99 ± 0.00 | 14.7 ± 0.1 |
| 215 443 to 464 159 | 9 936 | 0.98 ± 0.01 | 20.5 ± 0.2 |
| 464 159 to 1 000 000 | 21 407 | 0.92 ± 0.01 | 25.0 ± 0.2 |

Drift of a read (the mean over 40 µs) over a time lag, rms, in µV. The `.noise` column is
∫ S(f) sinc²(f · 40 µs) 4 sin²(π f lag) df, from the `.noise` density:

| Lag | From `.noise` | Device model | Injected model |
|---|---|---|---|
| 0.36 ms (18 units) | 39.8 | 39.4 | 69.0 |
| 2 ms | 45.1 | 44.0 | 78.2 |
| 5 ms | 47.2 | 44.4 | 79.8 |
| 10 ms | 48.5 | 45.2 | 82.0 |
| 19 ms | 49.6 | 48.2 | 86.9 |

- **From 1 kHz to 464 kHz the device model is within 5 % of `.noise`** in every band. The 8 % deficit from 464 kHz
  to 1 MHz is the linear interpolation between samples, as expected.
- **Below 1 kHz, 8 draws of 40 ms do not resolve the spectrum.** The band from 46 to 100 Hz is low (0.52 ± 0.07).
  It holds two bins next to the window and the mean removal, the same place where the generator alone is low.
  This is the band that makes a run offset, so phase 1 needs longer draws or many more of them to check it
  (section 4).
- **The read drift that matters is reproduced**: the device model is within 1 to 9 % of `.noise` for lags from
  0.36 to 19 ms.
- **The injected model gives 1.7 to 1.8 times the drift of `.noise`** at the same point, and 2.5 to 25 times its
  density from 46 Hz to 1 MHz. Its total rms on the stored voltage is 262 µV, against 66 µV for the device model.
  This is one operating point of the nominal cell, not the run offset of a run (no preset sample here). It agrees
  in direction with M5 of campaign 3 and with `NOISE.md`.
- **Cost on this frozen deck**: 398 s per draw for the device model (4 sources), 372 s for the injected model, 155 s
  quiet (one draw).

## 3. What phase 0 found not yet feasible as it stands

1. **`.noise` on the mismatch instances is ill-conditioned below about 30 Hz.** With seeds 7101 to 7103, the
   operating point is reproducible (two runs give the same voltages). The frozen deck and the network deck agree on
   every node that the freeze does not touch, and each seed differs from the nominal ([`OP_7101.json`](OP_7101.json),
   [`OP_7102.json`](OP_7102.json), [`OP_7103.json`](OP_7103.json)). So the mismatch sample is kept. But the
   ranking then gives one transistor of the sequencing logic all the noise: the lower NMOS of the NAND `xnsa`
   (7102, port 1: 3.5e4 V/√Hz at 1 Hz on the stored voltage). Its two series NMOS are both off: the node between
   them, at 82 mV, is held only by leakage (gds 1.2e-14 S, gmin 1e-16 S), and the small-signal matrix is near
   singular at low frequency. On the nominal cell the same node was harmless by chance.
   - Raising gmin to 1e-12 S for the analysis is no fix. The preset loop through 1e14 Ω then loses against the
     junction conductances, and the integrator goes to the rail.
   - Proposed fix, untested: a noiseless conductance of about 1e-12 S to ground on the internal nodes of the
     stacks of the logic gates only (not on the summing node), in the analysis decks only. Check that it leaves the
     ranking of the nominal cell unchanged.
2. **The preset may sample noise that lies outside the band.** At the preset point (switch closed,
   [`MODEL_nominal_preset.json`](MODEL_nominal_preset.json)) the stored voltage carries 183 µV rms in all, of
   which 52 µV are below 1.25 MHz. If the end of the preset freezes that noise (the switch opens within a
   nanosecond), the preset sample would be dominated by a part that a source sampled every 0.4 µs cannot make.
   This is a question, not a finding: the quantity frozen is the charge of the feedback capacitor, and the
   preset point gave no usable extraction here (its derived densities varied by a factor of 100 over the band;
   the transfer is suppressed by the loop, and the method of 2.1 is not valid as it is there).
   - Phase 1 must settle it at the preset point: the variance of v(vmem) − v(sum) from `.noise` over all
     frequencies, against a transient preset with sources sampled finer during the preset, or an explicit sampled
     term derived from `.noise`. The precharge of the sensor (kT/C on 400 fF, about 0.1 mV, which `DESIGN.md`
     lists as not modelled) is the same case.
3. **Only one of the operating points was done.** The comparators matter at their decision (inputs balanced) and
   the mirror during a pulse. Their bias changes within a cycle, so a stationary source is right only if A and B
   change little between those points. Otherwise the source must be modulated (a gain set by the current through
   a zero-volt sense source, which keeps all noise sources as voltage sources).
4. **Ideal sources are not devices.** The bias currents, the pulse current `bip`, and the references and supplies
   are ideal and noiseless in `.noise`. The injected model gives the mirror a shot noise of 2qI at 300 nA. Under a
   device model that term would have to stay as a declared non-device term, or be dropped, and that is the owner's
   call.

## 4. Proposed validation criteria (to be fixed before phase 1)

These are proposals. The numbers come from the pilot and the generator's own scatter. Validation must use new
draws, not those of this file.

| | Criterion | Proposed tolerance |
|---|---|---|
| V1 | `trnoise` calibration, for each exponent used: c(α) from at least 40 draws | every third of a decade from 100 Hz to 500 kHz within ±5 % of the calibration mean |
| V2 | Extraction, at each operating point and output: the kept devices cover the band power; their densities are flat; gate and body parts are small | cover ≥ 99 %; p95/p5 of A and of B·f^ef ≤ 1.1; other parts ≤ 1 % per device. A point that fails is not used |
| V3 | **Spectrum**: mean periodogram of the transient against `.noise`, in thirds of a decade from 2/T_draw to 464 kHz, at each frozen point and output | each band within ±10 %, or within 3 standard errors where those exceed 10 %, with enough draws that every band from 1 kHz up has a standard error ≤ 3 % |
| V4 | **Low-frequency part** (the band that makes run offsets): band power from 1/T_run to 1 kHz, and the drift of a 40 µs read for lags 0.36, 2, 5, 10, 19 ms | power within ±15 %; every drift within ±10 % of the `.noise` value. Needs about 64 draws of 40 ms, or 16 of 160 ms, per point (about 7 h of one processor on the frozen deck, or 1.8 h four at a time) |
| V5 | **Against the injected model** (descriptive, not pass/fail): the same drifts, the run mean, and the run offset of a noisy train of the nominal cell under both models | reported side by side, with the 0.090 / 0.064 mV of `NOISE.md` and the 0.111 / 0.094 mV of M5 |
| V6 | Out-of-band part: the `.noise` power above 1/(2 NT) at every point that is sampled (preset, precharge) | the sampled variance in transient within ±15 % of `.noise` over all frequencies, or the missing part added as an explicit term and declared |
| V7 | Numerical: the quiet floor, failures, the time grid | floor ≤ 1 % of the noise in every band; no aborted run; every noise sample and edge is a time point (as audited in `DESIGN.md`) |

The band that matters, as proposed: from 1/T_run (about 25 Hz for 40 ms) to 464 kHz for the stored voltage, which
is read as a 40 µs mean. For a comparator decision it reaches 1.25 MHz, with V6 for anything above.

## 5. Cost of a campaign under the device model

**Measured** ([`cost.py`](cost.py), [`COST.json`](COST.json)): four real network runs of the nominal cell, two cells,
12 pulses, 2.44 ms simulated, four at a time. The device sources of the cost runs have placeholder amplitudes,
for the cost only.

| Model | Noise sources | Wall, s | Against injected |
|---|---|---|---|
| quiet | 0 | 87 | 0.75 |
| injected (campaigns 1 to 3) | 14 | 117 | 1 |
| device, 10 per cell | 20 | 114 | 0.98 |
| device, 46 per cell (every analog transistor) | 92 | 137 | 1.17 |

The measured injected/quiet ratio, 1.34, is close to the 1.3861 of the campaign cost model. **A noisy run under the
device model costs at most about 1.17 times a noisy run today.** It costs the same if the ranking keeps about ten
sources per cell. The time grid is set by the 0.4 µs samples and the 200 ns largest step either way.

**Estimate for a campaign**, scaled from campaign 3, whose noisy ring runs took 871 to 1 211 s (mean 1 053 s)
and its quiet runs 1 042 to 1 279 s. A device-model noisy run then takes about 1 235 s (at most about 1 420 s).
The bound below is that of campaign 3: per machine, Σ(limit + 10 s)/4 + max(limit + 10 s), with limit = 1.3 ×
expected. Two machines, four runs at a time each, and one quiet run per instance as in campaign 3:

| Instances | Noisy runs per instance | Network-run bound, two machines together |
|---|---|---|
| 6 | 3 | 12 780 s (3.5 h) |
| 6 | 4 | 15 210 s (4.2 h) |
| 6 | 5 | 17 640 s (4.9 h) |
| 9 | 3 | 16 770 s (4.7 h) |
| 9 | 4 | 20 820 s (5.8 h) |
| 9 | 5 | 24 060 s (6.7 h) |
| 12 | 3 | 22 320 s (6.2 h) |
| 12 | 4 | 27 180 s (7.5 h) |
| 12 | 5 | 32 040 s (8.9 h) |

- The measures stage (scans and trains per instance) comes on top. In campaign 3 its bound was 5 750 s per
  machine; if its noisy trains move to the device model, at most about 1.17 times that.
- With the 14 400 s per stage of campaign 3, the network runs fit 6 instances with 3 noisy runs each.
- **The model itself has a cost before any campaign**: the extraction at three or four operating points for each
  new instance (about 1 min of one processor per point, once item 1 of section 3 is fixed) and the validation of
  V1 to V7 on the nominal cell and the development instances (V4 alone is about 2 h four at a time per point; V1
  to V7 together, about 6 to 10 h of a machine).

These are estimates, not measures of such a campaign. The budget is the owner's to set.

## 6. After the first report: what phase 0 settled

This section supersedes, where they differ, sections 3 to 5 above, which are kept as written.

**The noise analysis of a whole cell is not used.** In the frozen decks of [`model.py`](model.py), the operating
point that ngspice's `noise` command solves for itself fails (gmin, then source stepping) on almost every state and
instance, nominal included, where `op` and `ac` converge; its result is then computed about another point. On 7102
the same op-amp transistor, at the same `op` point (gm 6.561e-5 S, id 4.865 µA), came out 1.17 to 1.71 times
noisier at `pulse` than at `hold`, by a factor common to every device of an output. The per-cell extractions of
`model.py` (`EXTRACT_*.json`) are kept as evidence of that failure, not as a model. The method that replaces it,
[`devnoise.py`](devnoise.py), takes the noise current of each candidate transistor at its own operating point, in a
deck where all its terminals are forced (drain through a 0 V probe, the probes summed by CCVS: a transfer of
exactly 1 Ω); the transfers come from AC in the isolated cell deck; the output density is Σ S_k |H_k|². Each
candidate's drain current in the forced deck must equal its `op` current within 10⁻³ relative + 1 pA (magnitudes:
`@m[id]` carries ngspice's type and mode signs).

**Item 1 of section 3 (NAND stacks)** is moot for this method: the logic gates are not candidates, and their
outputs are checked at the rails (10 mV) at every frozen state. The stack-node conductance stays in the decks.

**Item 3 of section 3 (other operating points)** is done: `hold`, `window`, `fire`, `pulse` and `preset`, cells a
and b, on the nominal cell and 7101, 7102, 7103 ([`DEVNOISE_*.json`](DEVNOISE_nominal.json),
[`IDCHECK_*.json`](IDCHECK_nominal.json), [`CHECK_V2.json`](CHECK_V2.json)):
- V2 passes on all 18 outputs of each instance: cover ≥ 0.99, flat A and B, no logic device, no DC failure, the
  drain-current check at most 0.39 of its tolerance, the isolated operating point within 2.6 nV of the full deck;
- V2b (stationarity) passes: a device kept in several states has the same A and B within 0.01 % (the 17.6 to
  71.5 % of the `model.py` extractions came from the failed operating point);
- V2c passes: the same method in the full two-cell deck (`devnoise.py --full`, [`FULLDECK_nominal.json`](FULLDECK_nominal.json),
  [`FULLDECK_7102.json`](FULLDECK_7102.json)) gives the same devices, A, B, shares and band rms on all 36 outputs
  within 3.1e-8 relative. The cells are joined only by ideal supplies, so the isolation changes nothing.
- The model's devices are the same 23 per cell on all four instances (per port: op-amp `xm1`–`xm4`, window
  comparator `xm1`–`xm4`, mirror `xmin`, `xmout`; per cell: FIRE comparator `xm1`, `xm3`, `xm4`).

**The pilot of section 2 is not affected** ([`PILOT_CHECK.json`](PILOT_CHECK.json)): at the nominal hold point,
`devnoise.py` keeps the same four devices with the same shares and A and B within 0.019 %, and 66.7 µV rms in band.
The comparisons of section 2.2 (66 µV against 262 µV for the injected model; the drift ratio of 1.7 to 1.8) stand.

**Item 2 of section 3 (preset)** is changed, not settled. Across the integrating capacitor at the preset point,
`devnoise.py` gives 0.07 µV rms over 10 Hz to 1.25 MHz and 0.2 µV above, from the devices alone (the preset switch
is noiseless by declaration). This agrees with the AC of the circuit at its converged point: from the op-amp's
input to the capacitor voltage the gain is 1.55e-3 at preset (against 2.0 to the stored voltage at hold). The
earlier 183 µV (and 38 µV in band) came from the whole-cell `noise`, whose operating point fails. V6 of the
criteria (a transient preset) decides it.

**Seeding** (owner's point 1): the noise is sampled outside the simulator by numpy, per run, from the noise seed
10 × instance + round ([`noisegen.py`](noisegen.py), [`SEEDS_7101.json`](SEEDS_7101.json)); the slow 1/f part from
1/T_c, T_c = 1e5 s, is a fixed realization per instance and source taken at the run's virtual time (1 000 s per run).

**Item 4 (ideal sources)**: decided by the owner, the mirror's shot noise 2qI is kept as a declared non-device
term, at the peak of `bip` (173 nA); the other ideal sources are noiseless and listed in the criteria.

**Cost, superseding section 5** ([`cost3.py`](cost3.py), [`COST_C4_need4.json`](COST_C4_need4.json),
[`COST_C4_need4_sources.json`](COST_C4_need4_sources.json)). Campaign 4's need-4 network run (three cells, about
17 ms, emulated from `dnf.calendar(4, 4, 4, 4)`), four runs at a time:

| Run | Sources | Wall, s | Peak memory, MB |
|---|---|---|---|
| quiet | 0 | 814 | 632 |
| injected (campaigns 1 to 3) | 21 | 1 316 | 912 |
| PWL, every analog transistor | 144 | 4 716 | 1 610 |
| PWL, the model's union of `model.py` | 144 | 4 570 | 1 552 |
| PWL, the model (devnoise) | 75 | 2 461 | 1 216 |
| filesource, every analog transistor | 144 | 1 305 | 785 |
| **filesource, the model (devnoise)** | **75** | **1 033** | **717** |
| filesource, the model at zero amplitude | 75 | 827 | 659 |

The device sources have placeholder amplitudes (those of op-amp `xm3` at hold): this measures cost. With the 75
sources as XSPICE `filesource` instances, a noisy run costs 1.27 times a quiet run and 0.79 times the injected model;
its deck is 0.1 MB and its samples 50 MB in 10 files (8 sources each), generated in 24 s. The 1.17 of section 5 was
measured on 2.44 ms runs, where the PWL sources' cost had not yet grown with the run's length.

**Extraction time per instance** ([`EXTRACTION_TIME.json`](EXTRACTION_TIME.json), from the work files of the
extractions above, four instances at a time on four processors, so about one processor each). A two-cell instance
took 3 484 s (nominal) to 4 290 s (7102), all five states; per cell, on average:

| State | Outputs per cell | s per cell | Of which the trip sweeps |
|---|---|---|---|
| `window` | 2 | about 920 | about 790 (one sweep in `op`, the same sweep again before the transfers, about 200 s each) |
| `fire` | 1 | about 490 | about 400 |
| `hold` | 2 | about 195 | none |
| `pulse` | 2 | about 190 | none |
| `preset` | 2 | about 190 | none |
| operating-point check | per instance | about 40 | none |

Per output: the operating point about 14 s (plus a sweep of about 200 s at `window` and `fire`), the device-noise
run about 13 s, the transfers about 70 s (78 AC runs, plus the repeated sweep at `window` and `fire`).
Section 5 of the criteria estimates the extractions at about 1 h 45 for the four instances four at a time; they
took 58 to 72 min.

For campaign 4 (three cells per instance, every instance extracted in stage M):
- as the code stands, all five states: about 3 × 2 000 s, **about 1 h 40 of one processor per instance**;
- `preset` serves V6 only, a criterion of the validation, so campaign 4 does not need it: about 3 × 1 815 s,
  **about 1 h 30**;
- `hold`, `window`, `fire` and `pulse` are all needed: the model takes each device's A and B from the state of its
  largest share, and the rule for campaign 4 withholds noisy runs from an instance that fails V2 or V2b, which are
  checked on those four states. Both ports and every cell are needed, as each device has its own mismatch;
- the transfers repeat the trip sweep that the operating point has just done, and set the source to the same trip
  value. Reusing the value would give the same extraction and save about 200 s per `window` and `fire` output: about
  3 × 1 215 s, **about 1 h per instance**. This is a change to `devnoise.py` after the criteria were pushed, so it is
  not made; it needs the owner's decision, and a check that it reproduces `DEVNOISE_*.json` to the last digit.

**Two settings come with the filesource**, both found in phase 0:
- one file of 76 columns stops the deck at 1 µs ("timestep too small", even at zero amplitude); one column, and
  groups of 8, do not;
- with an XSPICE device present, ngspice lowers trtol to 1 for the whole circuit; `set xtrtol=7` keeps the default
  of the other runs. The check that it changes nothing the campaign uses ([`zerocheck.py`](zerocheck.py),
  [`ZEROCHECK_need4.json`](ZEROCHECK_need4.json)): the need-4 run with the 75 sources at zero amplitude gives the
  quiet run's 110 occurrences, writes and 49 FIRE events, every stored voltage read by the router within 87 nV
  (tolerance 1 µV), FIRE dates within 0.1 µs. The full stored-voltage traces differ by up to 4.8 mV, only at write
  edges shifted by up to 0.1 µs between the two runs' time steps (median difference about 1 nV); reads and events
  are what the campaign uses. The first version of the check compared FIRE dates to 1e-9 unit; after the first
  comparison it was changed to identify a FIRE by its cell, its occurrences and its routed lines.
- The filesource returns its samples within 5e-9 of their rms across the stops and resumes of the router.

## Reproduction

The venv must be at this path for the numpy hash to match:

```sh
/usr/bin/python3.12 -m venv /home/user/owner-prep/venv312 && /home/user/owner-prep/venv312/bin/python -m pip install numpy==2.3.5
sh research/circuit/fetch_pdk.sh        # from research/circuit: the PDK at the pinned commit
P=/home/user/owner-prep/venv312/bin/python; PDK=research/circuit/pdk; cd research/network-noise-study/phase0
$P -B gen.py WORK GENERATOR.json /usr/bin/ngspice 40 0.84 0.88 1.0
$P -B pilot.py extract WORK MODEL_nominal.json tt none /usr/bin/ngspice $PDK
$P -B pilot.py extract WORK MODEL_nominal_preset.json tt none /usr/bin/ngspice $PDK preset
$P -B pilot.py tran WORK TRAN_device.json MODEL_nominal.json device 0.04 8 /usr/bin/ngspice $PDK
$P -B pilot.py tran WORK TRAN_injected.json MODEL_nominal.json injected 0.04 8 /usr/bin/ngspice $PDK
$P -B pilot.py tran WORK TRAN_quiet.json MODEL_nominal.json quiet 0.04 1 /usr/bin/ngspice $PDK
$P -B pilot.py op WORK OP_7101.json tt_mm 7101 /usr/bin/ngspice $PDK      # and 7102, 7103
$P -B cost.py WORK COST.json MODEL_nominal.json /usr/bin/ngspice $PDK 3
```

After the first report:

```sh
$P -B devnoise.py extract WORK DEVNOISE_nominal.json tt none a,b /usr/bin/ngspice $PDK hold window fire pulse preset
$P -B devnoise.py extract WORK DEVNOISE_7101.json tt_mm 7101 a,b /usr/bin/ngspice $PDK hold window fire pulse preset   # and 7102, 7103
$P -B devnoise.py extract --full WORK FULLDECK_nominal.json tt none a,b /usr/bin/ngspice $PDK hold window fire pulse preset   # and 7102
$P -B devnoise.py idcheck WORK_OF_AN_EXTRACTION IDCHECK_nominal.json
$P -B compare.py CHECK_V2.json DEVNOISE_nominal.json:FULLDECK_nominal.json DEVNOISE_7102.json:FULLDECK_7102.json -- DEVNOISE_7101.json DEVNOISE_7103.json
$P -B cost3.py dnf WORK COST_C4_need4_sources.json /usr/bin/ngspice $PDK DNF_PY 4 pwlmodel fs46 fsmodel fszero   # DNF_PY: a copy of research/learned-dnf-circuit's dnf.py
$P -B zerocheck.py ZEROCHECK_need4.json QUIET_RUN_DIR FSZERO_RUN_DIR
```

Each WORK must be a new folder. The noise of a run is seeded by the simulator's process number, so no transient
here repeats exactly; the extractions and the operating points do.
