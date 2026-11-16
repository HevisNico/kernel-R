# Noise study, validation: the final analysis of attempt 2 and amendment 3

Every run of attempt 2 and of amendment 3's queue had ended with exit 0 before any summary was looked at. The
analysis is `vanalyze.py` of the released code (`74e93b4`, GO `341aac1`), with one fix made after the results
existed (section 9). Its outputs are [`RESULTS_A2.json`](RESULTS_A2.json), the governing reading, and
[`RESULTS_A2_SPLIT_AS_WRITTEN.json`](RESULTS_A2_SPLIT_AS_WRITTEN.json), the reading under `SPLIT_A2.md` as first
written.

## 1. Verdict

**The model is not validated.** V1, V2, V2b and V2c pass. V3, V4, V6, V7 and V8 fail.

The verdict comes from the criteria of [`../VALIDATION_CRITERIA.md`](../VALIDATION_CRITERIA.md) with amendments 1 to 4,
which govern ([`NOTE_VERDICT.md`](NOTE_VERDICT.md)). Item 6 of amendment 1 therefore applies:
- the default is the simulator's noise, which is the injected model of `../circuit/noise.py` used in campaigns 1 to 3;
- a corrected model needs an independent justification, made without looking at any campaign-4 data.

| Criterion | Governing reading (amendments 1–4) | `SPLIT_A2.md` as first written | Changes? |
|---|---|---|---|
| V1 generator | pass | pass | no |
| V2 extraction | pass | pass | no |
| V2b | pass | pass | no |
| V2c cell-by-cell vs full deck | pass | pass | no |
| V3 spectra | **fail**: 1 of 34 outputs passes (7101 window a1) | **fail**: 30 outputs computed, 1 passes; 4 outputs of 7103 not established | **yes**, in what it rests on: 7103 window a1, fire b, pulse a1 and pulse b2 go from failing to not established |
| V4 low frequency | **fail**: 9 of 13 outputs pass | **fail**: the same 9 of 13 | no |
| V6 out-of-band part | **fail**: 0 of 16 ports | **not established** on all four instances (the V6 runs of machine 5 are missing) | **yes**: failing becomes not established |
| V7 numerical floor | **fail** on 7101, 7102 and 7103 (latency) | **fail**, the same | no |
| V8 seeding | **fail** on 7101, 7102 and 7103 | **fail**, the same | no |
| V5, reported (not part of the verdict) | complete, 13 outputs | **incomplete**: no output can be computed (one injected draw of each instance is missing) | **yes** |
| Section 3 constants | computed (section 4) | **not established**: one noisy train of each development instance is missing | **yes** |
| **Verdict** | **not validated** | **not validated** | no |

Under the `SPLIT_A2.md` reading, amendment 3's point 5 applies on its own: V3, V6 and the constants are not
established, so the model is not validated even before any failure is counted. Under both readings, V4, V7 and V8
fail on runs that machine 5 never held.

## 2. Completeness, environment and restarts

- **Runs.**
  - Plan: 463 runs.
  - Results: 463, with no duplicate and every exit 0.
  - Attempt 2: 430 runs on machines 1 to 8 (machine 5: 25).
  - Amendment 3's queue: 33 runs (section 8).
- **Environment and code.** All 12 MACHINE records (8 of attempt 2 and 4 of the queue) show the reference
  environment with identical hashes (`vplan.inventory`). They also show the released code: HEAD `341aac1`, whose
  parent is `74e93b4`, with a clean tree (`vplan.released`).
- **No restart during a run.** A restart kills the plan process, and the process writes a run's exit line only
  after the run ends. Every one of the 463 runs has its exit line. Boot times are taken from `uptime` in each
  SYSTEM.txt and from the UPTIME logs. GO is at 11:05:16 UTC.
  - Machine 1: booted 09:37:00 and never restarted. UPTIME_REFS.log was constant to 16:58:54, and UPTIME_END.txt
    still showed 09:37:00 at 17:41:07.
  - Machines 2, 3 and 4: booted about 07:12, 07:17 and 07:17. That is before GO, and their containers did not
    restart until their attempt-2 share was collected.
  - Machines 6, 7 and 8: booted about 09:48, before GO.
  - Machine 5:
    - its container restarted at about 16:11, which cut 4 runs ([`a2/m5/SYSTEM.txt`](a2/m5/SYSTEM.txt), "up 0 min"
      at 16:11:17);
    - it booted again at 16:28:36 ([`a2/m5/SYSTEM_RESTART.txt`](a2/m5/SYSTEM_RESTART.txt)), with no OOM in the
      kernel log;
    - its 25 completed runs have their exit lines.
  - Queue:
    - machine 2 booted 16:29:02, and its UPTIME.log is constant to 16:58:49;
    - machine 3 booted 16:28:15, constant (26 samples);
    - machine 5 booted 16:28:36, constant;
    - machine 4 booted 07:17:41, and still showed it at 16:44:31, after its last run.
  - Every queue run started after its machine's boot and ended before that machine's final SYSTEM.txt, which shows the same boot.
- **Memory.** The peak per run was 363 to 483 MB, against 16 GB per machine. No OOM appears in any kernel log.
- **Attempt 1.** Attempt 1 (folders [`m1`](m1) to [`m4`](m4)) was abandoned for OOM (amendment 2). Its runs are
  kept as they are and enter no criterion.

## 3. Extractions (V2, V2b, V2c) and their cost

- **Equality with phase 0.** The four extractions (nominal, 7101, 7102, 7103) and the two V2c references (nominal
  and 7102, full deck) equal phase 0's to the last digit written. See [`CHECK_EXTRACT.json`](CHECK_EXTRACT.json).
- **V2.** Passes on every instance. The isolated operating point is within 2.6 nV of the full deck's (7103 a, worst
  node).
- **V2b.** Passes. The worst value is 1.1e-4.
- **V2c.** Passes on all 18 outputs of the nominal cell and all 18 of 7102. The worst figure recorded is 3.1e-8.
- **Conditioning check.** Passes. The largest share difference is 5e-13.
- **Where window, fire and pulse ran.** These draws ran on the isolated cell. V2c is what makes that equivalent
  to the full deck.
- **The full-trace 4.8 mV difference.** It occurs only at write edges shifted by up to 0.1 µs. Reads and events,
  which are what the campaign uses, are not affected.

**Extraction cost per instance** (two cells, about one processor each, four instances at a time; from
[`../phase0/EXTRACTION_TIME.json`](../phase0/EXTRACTION_TIME.json), whose extractions the validation reproduced to
the last digit):

| Instance | Wall | window | fire | hold | preset | pulse | op check | op / device-noise / AC part |
|---|---|---|---|---|---|---|---|---|
| nominal | 3 484 s | 46 % | 23 % | 10 % | 10 % | 10 % | 1 % | 33 / 7 / 59 % |
| 7101 | 4 218 s | 48 % | 23 % | 10 % | 9 % | 9 % | 1 % | 34 / 6 / 59 % |
| 7102 | 4 290 s | 46 % | 27 % | 9 % | 9 % | 8 % | 1 % | 35 / 6 / 58 % |
| 7103 | 4 052 s | 45 % | 25 % | 9 % | 9 % | 11 % | 1 % | 34 / 6 / 59 % |

- **Per output.** About 90 s for hold, preset and pulse; about 390 to 630 s for window and fire.
- **Why window and fire cost more.** Their operating point and their AC transfers both repeat the trip sweep.

**Measured time per draw** (one processor, four at a time):

| Draw | Time |
|---|---|
| `hold`, one cell, 80 ms | about 350 s |
| `hold`, two cells, 80 ms | about 750 s |
| injected `hold`, two cells | about 1 617 s |
| window | about 3 880 s |
| fire | about 3 680 s |
| pulse | about 175 s |
| V6, 50 µs | about 15 s |
| V8, 1 ms | about 31 s |
| one train of section 3 | about 350–450 s |

## 4. V5 and the constants of section 3 (reported whatever the verdict)

**Constants under the model** (pooled over the three development instances, 56 run offsets and 232 doses):

| Constant | Measured | Campaign 4 uses at least |
|---|---|---|
| between runs | 0.0311 mV | 0.111 mV |
| within a run | 0.0419 mV | 0.094 mV |
| per dose | 0.00255 mV | 0.009 mV |

Per instance, between runs: 7101 0.0282 mV, 7102 0.0297 mV, 7103 0.0346 mV. Dose noise: 0.0026, 0.0025 and
0.0025 mV. Trains excluded by the train rules: 7101 b2 two, 7102 a2 two, none on 7103.

**The same constants under the injected model** (V5): 0.0886 mV between runs, 0.0659 mV within a run and
0.00862 mV per dose (52 run offsets, 233 doses). All three measured values, under either model, are below the
values campaign 4 uses at least.

**V5** compares the injected model of campaigns 1 to 3 with the model's reference, on the `hold` outputs. Its
spectrum is 2.0 to 4.0 times the reference in the lowest band and about 19 to 20 times in the 215–464 kHz band. Its
drift rms is about 1.7 to 1.86 times. Its 25 Hz–1 kHz power is 2.3 to 3.0 times, and its between-run rms 2.4 to 4.9
times. The injected noise is thus well above the device model at every frequency. The full table is in section 6.

## 5. What the failures are, as observed

These are observations. None of them changes the verdict, the criteria or the analysis.

- **V3, 215–464 kHz.**
  - Every `hold` output sits at 0.845–0.852 of the reference in this band, and `window` and `fire` at 0.866–0.895.
  - The lower bands of `hold` pass, except on 7103 a2, with 8 draws.
  - Observation: a sampled noise interpolated linearly between samples 0.4 µs apart has a power response of
    sinc⁴(f·Δt). Over this band that averages about 0.87, which is close to what is seen. This was not tested.
    V1 checks the generated samples, not the interpolated source.
- **V3, `pulse`.**
  - Every pulse output is far below its reference: 0.03 to 0.10 below 5 kHz, and at most 0.37.
  - Observation: this is the largest failure, and it is not explained here.
- **V3, some 1–5 kHz bands** of window and fire: 0.82–0.90 and 1.11–1.23, with 8 draws each.
- **V4.**
  - Drifts are within ±4 % on every output, and the 25 Hz–1 kHz power is at 0.80–0.99.
  - The between-run rms fails on 4 outputs of 13: 7101 a2 0.567, 7101 b1 1.331, 7102 b1 0.628 and 7103 a2 1.444.
    Each of these rests on 7 pairs.
- **V6.**
  - The transient variance is 6 500 to 18 600 times the reference: about 20 µV rms against 0.2 µV.
  - Observation: the reference is the preset-state density across the capacitor, which the closed switch keeps
    small. The sample is taken 1 µs after the switch opens.
  - The rule of V6 that a transient below 75 % means "not validated" is not what triggered here. The ratio is
    above 1.25.
- **V7.**
  - The two quiet trains are identical byte for byte.
  - The zero-amplitude train gives the same writes and FIRE events, with reads within 0.11 µV (tolerance 1 µV)
    and doses within 6e-5 mV (tolerance 0.002).
  - Its FIRE latencies differ from the quiet train by up to 0.039, 0.067 and 0.053 mV-equivalent, against a
    tolerance of 0.005.
  - So the zero-amplitude sources change no read or dose beyond the floor, but they do move the latencies.
- **V8.**
  - The rerun of the first seed is identical byte for byte.
  - The operating point with the model differs from the quiet run's in the last printed digits on 327 of 1 830
    nodes, by at most 3e-12 V. The branch currents involved are about 1e-15 A.
  - One of the 12 correlations is above 0.1: 0.116, on a stored voltage of 7103. The others are within ±0.045.

## 6. Every criterion, output by output (governing reading)

Ratios are the transient against the reference. Tolerances are those of the criteria.

#### V3

| Output | Draws | Bands passing | Failing bands (ratio) | Pass |
|---|---|---|---|---|
| nominal hold a1 | 32 | 10/11 | 215k–464k Hz (0.848) | **no** |
| 7101 hold a1 | 8 | 10/11 | 215k–464k Hz (0.849) | **no** |
| 7101 hold a2 | 8 | 10/11 | 215k–464k Hz (0.850) | **no** |
| 7101 hold b1 | 8 | 10/11 | 215k–464k Hz (0.847) | **no** |
| 7101 hold b2 | 8 | 10/11 | 215k–464k Hz (0.846) | **no** |
| 7102 hold a1 | 8 | 10/11 | 215k–464k Hz (0.849) | **no** |
| 7102 hold a2 | 8 | 10/11 | 215k–464k Hz (0.849) | **no** |
| 7102 hold b1 | 8 | 10/11 | 215k–464k Hz (0.846) | **no** |
| 7102 hold b2 | 8 | 10/11 | 215k–464k Hz (0.846) | **no** |
| 7103 hold a1 | 8 | 10/11 | 215k–464k Hz (0.845) | **no** |
| 7103 hold a2 | 8 | 8/11 | 100–215 Hz (0.773); 1k–2.15k Hz (1.112); 215k–464k Hz (0.851) | **no** |
| 7103 hold b1 | 8 | 10/11 | 215k–464k Hz (0.852) | **no** |
| 7103 hold b2 | 8 | 10/11 | 215k–464k Hz (0.851) | **no** |
| nominal window a1 | 8 | 8/10 | 464–1k Hz (1.226); 215k–464k Hz (0.895) | **no** |
| nominal fire a | 8 | 9/10 | 215k–464k Hz (0.892) | **no** |
| nominal pulse a1 | 8 | 0/10 | 215–464 Hz (0.069); 464–1k Hz (0.068); 1k–2.15k Hz (0.085); 2.15k–4.64k Hz (0.093); 4.64k–10k Hz (0.137); 10k–21.5k Hz (0.206); 21.5k–46.4k Hz (0.279); 46.4k–100k Hz (0.343); 100k–215k Hz (0.335); 215k–464k Hz (0.207) | **no** |
| 7101 window a1 | 8 | 10/10 | – | yes |
| 7101 window b2 | 8 | 7/10 | 1k–2.15k Hz (0.881); 2.15k–4.64k Hz (0.835); 215k–464k Hz (0.893) | **no** |
| 7101 fire a | 8 | 9/10 | 215k–464k Hz (0.877) | **no** |
| 7101 fire b | 8 | 7/10 | 1k–2.15k Hz (0.817); 2.15k–4.64k Hz (0.869); 215k–464k Hz (0.866) | **no** |
| 7101 pulse a1 | 8 | 0/10 | 215–464 Hz (0.045); 464–1k Hz (0.057); 1k–2.15k Hz (0.066); 2.15k–4.64k Hz (0.087); 4.64k–10k Hz (0.140); 10k–21.5k Hz (0.191); 21.5k–46.4k Hz (0.288); 46.4k–100k Hz (0.342); 100k–215k Hz (0.336); 215k–464k Hz (0.214) | **no** |
| 7101 pulse b2 | 8 | 0/10 | 215–464 Hz (0.067); 464–1k Hz (0.059); 1k–2.15k Hz (0.068); 2.15k–4.64k Hz (0.085); 4.64k–10k Hz (0.137); 10k–21.5k Hz (0.214); 21.5k–46.4k Hz (0.280); 46.4k–100k Hz (0.326); 100k–215k Hz (0.356); 215k–464k Hz (0.237) | **no** |
| 7102 window a1 | 8 | 8/10 | 1k–2.15k Hz (1.132); 215k–464k Hz (0.893) | **no** |
| 7102 window b2 | 8 | 8/10 | 1k–2.15k Hz (0.886); 215k–464k Hz (0.894) | **no** |
| 7102 fire a | 8 | 8/10 | 1k–2.15k Hz (0.826); 215k–464k Hz (0.880) | **no** |
| 7102 fire b | 8 | 8/10 | 1k–2.15k Hz (0.835); 215k–464k Hz (0.868) | **no** |
| 7102 pulse a1 | 8 | 0/10 | 215–464 Hz (0.049); 464–1k Hz (0.069); 1k–2.15k Hz (0.064); 2.15k–4.64k Hz (0.093); 4.64k–10k Hz (0.133); 10k–21.5k Hz (0.221); 21.5k–46.4k Hz (0.278); 46.4k–100k Hz (0.340); 100k–215k Hz (0.372); 215k–464k Hz (0.316) | **no** |
| 7102 pulse b2 | 8 | 0/10 | 215–464 Hz (0.052); 464–1k Hz (0.047); 1k–2.15k Hz (0.066); 2.15k–4.64k Hz (0.091); 4.64k–10k Hz (0.142); 10k–21.5k Hz (0.205); 21.5k–46.4k Hz (0.269); 46.4k–100k Hz (0.347); 100k–215k Hz (0.373); 215k–464k Hz (0.310) | **no** |
| 7103 window a1 | 8 | 8/10 | 4.64k–10k Hz (0.899); 215k–464k Hz (0.893) | **no** |
| 7103 window b2 | 8 | 9/10 | 215k–464k Hz (0.895) | **no** |
| 7103 fire a | 8 | 9/10 | 215k–464k Hz (0.870) | **no** |
| 7103 fire b | 8 | 9/10 | 215k–464k Hz (0.872) | **no** |
| 7103 pulse a1 | 8 | 0/10 | 215–464 Hz (0.055); 464–1k Hz (0.047); 1k–2.15k Hz (0.070); 2.15k–4.64k Hz (0.091); 4.64k–10k Hz (0.130); 10k–21.5k Hz (0.199); 21.5k–46.4k Hz (0.268); 46.4k–100k Hz (0.313); 100k–215k Hz (0.265); 215k–464k Hz (0.132) | **no** |
| 7103 pulse b2 | 8 | 0/10 | 215–464 Hz (0.026); 464–1k Hz (0.050); 1k–2.15k Hz (0.075); 2.15k–4.64k Hz (0.103); 4.64k–10k Hz (0.146); 10k–21.5k Hz (0.209); 21.5k–46.4k Hz (0.282); 46.4k–100k Hz (0.333); 100k–215k Hz (0.328); 215k–464k Hz (0.195) | **no** |

#### V4

| Output | Drift ratios (5 lags) | Band 25 Hz–1 kHz | Between runs (pairs) | Pass |
|---|---|---|---|---|
| nominal hold a1 | 0.993–0.998 | 0.906 | 1.105 (31) | yes |
| 7101 hold a1 | 1.001–1.031 | 0.945 | 0.915 (7) | yes |
| 7101 hold a2 | 1.011–1.030 | 0.977 | 0.567 (7) (fail) | **no** |
| 7101 hold b1 | 0.995–1.021 | 0.994 | 1.331 (7) (fail) | **no** |
| 7101 hold b2 | 0.992–1.031 | 0.924 | 1.001 (7) | yes |
| 7102 hold a1 | 0.991–1.022 | 0.871 | 0.870 (7) | yes |
| 7102 hold a2 | 1.001–1.043 | 0.992 | 0.797 (7) | yes |
| 7102 hold b1 | 0.977–0.997 | 0.938 | 0.628 (7) (fail) | **no** |
| 7102 hold b2 | 0.989–1.011 | 0.817 | 0.977 (7) | yes |
| 7103 hold a1 | 0.968–1.001 | 0.910 | 0.712 (7) | yes |
| 7103 hold a2 | 0.978–1.009 | 0.797 | 1.444 (7) (fail) | **no** |
| 7103 hold b1 | 1.000–1.013 | 0.945 | 0.950 (7) | yes |
| 7103 hold b2 | 1.002–1.017 | 0.959 | 0.777 (7) | yes |

#### V5 (injected model against the model's reference; reported, not a criterion of the verdict)

| Output | Spectrum band ratios (low → high) | Drift ratios | Band 25 Hz–1 kHz | Between runs |
|---|---|---|---|---|
| nominal hold a1 | 3.50 → 18.98 (min 2.58) | 1.709–1.787 | 2.955 | 2.420 |
| 7101 hold a1 | 3.99 → 19.01 (min 2.51) | 1.693–1.761 | 2.708 | 3.575 |
| 7101 hold a2 | 2.90 → 18.97 (min 2.52) | 1.695–1.749 | 2.384 | 3.249 |
| 7101 hold b1 | 3.69 → 19.01 (min 2.50) | 1.715–1.751 | 2.961 | 3.257 |
| 7101 hold b2 | 2.04 → 18.90 (min 2.04) | 1.688–1.856 | 2.283 | 2.827 |
| 7102 hold a1 | 3.06 → 20.18 (min 2.53) | 1.735–1.822 | 2.376 | 4.863 |
| 7102 hold a2 | 3.05 → 20.17 (min 2.67) | 1.726–1.828 | 2.851 | 3.440 |
| 7102 hold b1 | 4.00 → 19.99 (min 2.70) | 1.751–1.831 | 2.893 | 3.192 |
| 7102 hold b2 | 3.16 → 19.79 (min 2.65) | 1.726–1.763 | 2.943 | 2.562 |
| 7103 hold a1 | 3.81 → 19.35 (min 2.51) | 1.683–1.764 | 2.915 | 3.887 |
| 7103 hold a2 | 3.29 → 19.06 (min 2.67) | 1.680–1.710 | 2.871 | 2.501 |
| 7103 hold b1 | 2.63 → 19.06 (min 2.54) | 1.708–1.789 | 2.747 | 2.682 |
| 7103 hold b2 | 3.31 → 18.78 (min 2.46) | 1.718–1.775 | 2.911 | 2.586 |

#### V6

| Port | Transient variance (V²) | Reference (V²) | Ratio | Pass |
|---|---|---|---|---|
| nominal a1 | 5.93e-10 | 4.66e-14 | 12727 | **no** |
| nominal a2 | 6.01e-10 | 4.66e-14 | 12898 | **no** |
| nominal b1 | 8.65e-10 | 4.66e-14 | 18574 | **no** |
| nominal b2 | 5.57e-10 | 4.66e-14 | 11950 | **no** |
| 7101 a1 | 4.14e-10 | 4.64e-14 | 8915 | **no** |
| 7101 a2 | 5.69e-10 | 4.64e-14 | 12253 | **no** |
| 7101 b1 | 5.16e-10 | 4.65e-14 | 11078 | **no** |
| 7101 b2 | 3.52e-10 | 4.7e-14 | 7486 | **no** |
| 7102 a1 | 3.06e-10 | 4.68e-14 | 6533 | **no** |
| 7102 a2 | 6.46e-10 | 4.67e-14 | 13837 | **no** |
| 7102 b1 | 4.03e-10 | 4.64e-14 | 8681 | **no** |
| 7102 b2 | 4.94e-10 | 4.66e-14 | 10612 | **no** |
| 7103 a1 | 3.91e-10 | 4.63e-14 | 8445 | **no** |
| 7103 a2 | 7.98e-10 | 4.64e-14 | 17175 | **no** |
| 7103 b1 | 4.79e-10 | 4.64e-14 | 10323 | **no** |
| 7103 b2 | 5.74e-10 | 4.65e-14 | 12345 | **no** |

#### V7

| Instance | Quiet trains identical | Zero-amplitude: same writes and fires | Max read diff | Max latency diff (mV-eq., tol. 0.005) | Max dose diff (mV, tol. 0.002) | Pass |
|---|---|---|---|---|---|---|
| 7101 | True | True | 0.062 µV | 0.0395 | 3.46e-05 | **no** |
| 7102 | True | True | 0.111 µV | 0.0667 | 5.88e-05 | **no** |
| 7103 | True | True | 0.055 µV | 0.0529 | 4.34e-05 | **no** |

#### V8

| Instance | OP nodes compared | OP identical | Rerun identical | Correlations (stored voltages) | Pass |
|---|---|---|---|---|---|
| 7101 | 1830 | False | True | 0.039, -0.041, -0.002, -0.037 | **no** |
| 7102 | 1830 | False | True | -0.026, 0.037, 0.004, 0.006 | **no** |
| 7103 | 1830 | False | True | 0.116, 0.045, -0.019, -0.038 | **no** |

## 7. The `SPLIT_A2.md` reading in detail

- Inputs: the work folders `a2/m1` to `a2/m8` only. Machine 5's 33 runs count as missing.
- V3: `v3_7103_window_a1_r213`, `v3_7103_fire_b_r237`, `v3_7103_pulse_a1_r245` and `v3_7103_pulse_b2_r253` are
  missing. Their four outputs are not established. The 30 other outputs give the same values as in section 6.
- V6: the draws of every instance are incomplete, so all four instances are not established.
- V5: `v5_nominal_hold_inj4`, `v5_7101_hold_inj4`, `v5_7102_hold_inj7` and `v5_7103_hold_inj2` are missing, among
  others. No V5 output can be computed. Under `NOTE_VERDICT.md` this makes V5's report incomplete and does not by
  itself decide the verdict.
- Section 3 constants: the trains `tr_7101_r294`, `tr_7102_r294` and `tr_7103_r294` are missing. The constants are
  not established, and amendment 3's point 5 applies.
- V4, V7 and V8 are identical to the governing reading.

## 8. The 33 runs of amendment 3

All ran under `74e93b4`/GO `341aac1`, through `vdeal.py`, with the plan's command, seed, round and position. The
queue and its claims are copied in [`a3/queue`](a3/queue) (from `7756a4d`).
- Each run's machine is recorded as "N (amendment 3 rerun)" in its own JSON, or in `meta.json` for a train.
- The 4 runs that the restart cut are rows 1 to 4: they are run once again, as rule 1 allows.
- No run was killed twice. No run was killed by OOM.

Start, end, wall time and peak memory are from each machine's `a3/mN/plan.log`. The hash is the run's
`raw_nodate_sha256` ([`NOTE_RAW_HASH.md`](NOTE_RAW_HASH.md)). The restart evidence is in section 2.

| # | Run | Machine | Start (UTC) | End (UTC) | Exit | Wall (s) | Peak (MB) | raw_nodate_sha256 |
|---|---|---|---|---|---|---|---|---|
| 1 | `v3_7103_window_a1_r213` | 3 | 16:29:08 | 17:29:56 | 0 | 3648 | 413 | `85ae0892d138744113b0f38708cd8c15975e9a61c40df241cc086858d4d90b16` |
| 2 | `v3_7103_fire_b_r237` | 3 | 16:29:10 | 17:26:48 | 0 | 3458 | 416 | `0395e3d8ba28c4c3ce9ecc06a388f3eb4bd13bbadd7f36bd8adb7ab2a60f4608` |
| 3 | `v3_7103_pulse_a1_r245` | 3 | 16:29:13 | 16:31:42 | 0 | 149 | 363 | `3161dbc6a1835e8466168185557a60c0eca94a96ce5b00479824c85107232592` |
| 4 | `v3_7103_pulse_b2_r253` | 3 | 16:29:17 | 16:31:47 | 0 | 150 | 363 | `b5b95e4079f081fabfdd345f23598579272dda74fccb7a8d059ec7d26a58557d` |
| 5 | `v6_nominal_zero` | 4 | 16:29:29 | 16:29:43 | 0 | 14 | 364 | `9639524b11df215d1ea42f91a39900f41d828f0ad4f988c8e215ee7dd094ba96` |
| 6 | `v6_nominal_r264` | 4 | 16:29:31 | 16:29:45 | 0 | 14 | 364 | `071436f5eee56582384ea64e3ec0d023bd6487c7f7c0887d9e2256f25056c445` |
| 7 | `v6_nominal_r272` | 4 | 16:29:33 | 16:29:47 | 0 | 14 | 364 | `36254b6ee788092ae48e25b12711082664976b7169e393ba739e0269fb762df4` |
| 8 | `v6_nominal_r280` | 4 | 16:29:35 | 16:29:49 | 0 | 14 | 363 | `6a3b6718488fbda743d847aefb489ca998890c9c84d7b67451afa8474ae73910` |
| 9 | `v6_nominal_r288` | 2 | 16:29:41 | 16:29:59 | 0 | 18 | 363 | `341cb3e6e837c0eb4c960465448ce2d5d0178091245531d839d866fe12d24c03` |
| 10 | `v6_7101_r267` | 2 | 16:29:46 | 16:30:02 | 0 | 16 | 364 | `85bc584eafc62db2850af4cdf9511b488b0406387257be1baa24a4b38a3585f3` |
| 11 | `v6_7101_r275` | 2 | 16:29:49 | 16:30:06 | 0 | 17 | 364 | `331ced3466f20ec6bb54ef7b8770922b7cd0f8091b0c8ef6b9371911df845afa` |
| 12 | `v6_7101_r283` | 2 | 16:29:52 | 16:30:08 | 0 | 17 | 364 | `4da38c2c47e443db6c1d733539aaf7c6037209bb0f0d1a420c6f287c8d4ed8f9` |
| 13 | `v6_7101_r291` | 4 | 16:29:58 | 16:30:11 | 0 | 13 | 364 | `e1ea31d24675caca9bd580819c15a304f9cda3598cafce660ba0194903f01215` |
| 14 | `v6_7102_r266` | 4 | 16:30:01 | 16:30:15 | 0 | 14 | 364 | `bd7bccb523f1541727943b18ba7205b432e2caa41de5a9c885b30b9b106403e0` |
| 15 | `v6_7102_r274` | 4 | 16:30:03 | 16:30:18 | 0 | 15 | 364 | `e387899d9f67f622b08795e1c4dd8974669c76860521f6d6f95016887a963906` |
| 16 | `v6_7102_r282` | 4 | 16:30:06 | 16:30:21 | 0 | 15 | 363 | `fed63071cf367fd57b78e7b53dd94f7b4d49cfe6ff2d58f07a259212cc60e4d8` |
| 17 | `v6_7102_r290` | 4 | 16:30:13 | 16:30:28 | 0 | 14 | 363 | `8cbfae0cd87146e58bd04c0dd7a491ecb2ed7ea966804b00570c0ea08649c7ea` |
| 18 | `v6_7103_r265` | 4 | 16:30:17 | 16:30:32 | 0 | 15 | 363 | `8cc32ca1c9860a3fe0320ea9dbdd2b6042745c4cc815d060f9c70dec73d4b143` |
| 19 | `v6_7103_r273` | 4 | 16:30:21 | 16:30:35 | 0 | 15 | 363 | `633968b43f35353d2d278f965d9859ea202aab50e1e5389f9afd0f75e7953e24` |
| 20 | `v6_7103_r281` | 4 | 16:30:23 | 16:30:38 | 0 | 15 | 363 | `5e77f7391b9eaf39c6feb773df14d55cf4db8b2cba3c4c75df8c036625819ff7` |
| 21 | `v6_7103_r289` | 2 | 16:30:30 | 16:30:47 | 0 | 17 | 364 | `ed3d2f29362ab813a593e159932f8ca2e4d370ebb8d3a28e65d73df10bf06373` |
| 22 | `tr_7101_r294` | 2 | 16:30:33 | 16:36:21 | 0 | 348 | 363 | `68876e4e116d52749deb6989c935a04ecaba47553eed82396184058089649a83` |
| 23 | `tr_7102_r294` | 4 | 16:30:36 | 16:36:46 | 0 | 369 | 364 | `3c528399bf80d9b3e9b6f559de9a6d67da645e862662c979104a67c3f357233f` |
| 24 | `tr_7103_r294` | 4 | 16:30:40 | 16:36:54 | 0 | 373 | 364 | `c1a9c29638279d1b68ec02df8b92e59f0a516a3de7b131554f0f2c5ad3fa2037` |
| 25 | `v5_nominal_hold_inj4` | 4 | 16:30:44 | 16:44:00 | 0 | 796 | 404 | `b7ea6ad76433bc4f213e6e64fbffe7090dfd78788b6ada43a41222932c7001c1` |
| 26 | `v5_nominal_hold_inj12` | 4 | 16:30:46 | 16:43:58 | 0 | 792 | 404 | `b0122adfcc2ea258e649a9fca2b89fe234539ea64d692640c14f9c06b92398fb` |
| 27 | `v5_nominal_hold_inj20` | 2 | 16:30:55 | 16:44:08 | 0 | 793 | 404 | `069a8de8c5bd606302b0107b926aac55d4b6f3c54741883d20d302eb956fa80b` |
| 28 | `v5_nominal_hold_inj28` | 2 | 16:30:59 | 16:44:15 | 0 | 796 | 404 | `bb803a2b223e2b41ecaad7ace4f7cab8ec54e6c57eda7cc73d6097d34344b311` |
| 29 | `v5_7101_hold_inj4` | 2 | 16:31:03 | 16:59:42 | 0 | 1719 | 483 | `def6b735500ec0ff17ac74e070668e14cd5ffd0dd384e508cd2266e1bb23e9fe` |
| 30 | `tr_7101_inj4` | 3 | 16:31:46 | 16:38:11 | 0 | 385 | 395 | `673210cc754ac6da42a3100694248fc262145be69e571259139f42a7a9039a72` |
| 31 | `v5_7102_hold_inj7` | 3 | 16:31:49 | 16:57:16 | 0 | 1526 | 483 | `b3fdbca1d5883081bd2b13f6df414c707ec37558ab5f8c26753c3122c2ee2f5f` |
| 32 | `v5_7103_hold_inj2` | 5 | 16:33:27 | 17:02:26 | 0 | 1738 | 483 | `7283f0715c63d48f855e1a5f969a609c24ba30233b09a5566f0dc6d375d3bc36` |
| 33 | `tr_7103_inj2` | 5 | 16:33:31 | 16:40:59 | 0 | 448 | 403 | `e5823d47357f04bf4890e98c4eab94d6f9253f5af63d4a302cf1b8310154a094` |

Per machine: 2 took 9, 3 took 6, 4 took 16 and 5 took 2. No claim of the queue is from
machines 1, 6, 7 or 8. Every run ended with exit 0.

## 9. Change to the analysis made after the results existed

`vanalyze.py`, in `v7`, as released, crashed on the first analysis: it took the mean of an empty list. It called
`constants.instance`, which needs at least one noisy train, and V7 has none.
- The fix calls `constants.port` for each port, with the quiet train and no noisy train.
- This gives the same quantity the code intended: the slope of the quiet train, `train_18_quiet.slope_per_mV`.
- It touches no tolerance and no other criterion.
- It was made after the results existed. It is declared here, and the diff is in the same commit as the results.

No other change was made to the analysis code or to any input.

## 10. Still to do (asked for this report, not yet measured)

- **Optimized extraction.** Campaign 4's frozen copy drops `preset` and reuses the trip value. Check that it
  reproduces `DEVNOISE_*.json` to the last digit, and give its time per cell.
- **Need-7 calendar.** Measure the need-7 calendar (`dnf.calendar(5, 5, 5, 5)`, about 20.5 ms; need 5 is about
  17.8 ms), quiet and under the model, four at a time. Record wall time and peak memory.
- **Slip in criteria section 4.** The 20.5 ms calendar is need 7, not need 5.

