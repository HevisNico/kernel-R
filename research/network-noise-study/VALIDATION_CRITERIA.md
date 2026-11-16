# Noise study: validation criteria of the device-noise model

Point 2 of [`COMMITMENT.md`](COMMITMENT.md) and point 1 of [`AMENDMENT_1.md`](AMENDMENT_1.md). This file is pushed
**alone, before any validation run**. The criteria apply **only to draws made after this push**. No transient
of phase 0 counts: phase 0 used the noise seeds 71011 and 71012, the numpy seeds 1000 to 1199 of
`noisegen.py psd`, and `trnoise` draws. None of them enters the validation, whose numpy-only draws start at
seed 2000.

Instances: the nominal cell (section `tt`, no mismatch seed) and the development instances 7101, 7102 and 7103
(section `tt_mm`, two cells `a`, `b`, as in phase 1). **No other mismatch seed is simulated**, and the scripts
refuse any other. Seeds 7501 to 7520 are reserved for campaign 4.

Environment: as pinned in `phase0/FEASIBILITY.md`, with each hash checked before the runs.

## 1. The model that is validated

For an instance, that is a deck built with `../network-circuit/net.py` and a mismatch seed:

1. **Extraction.** The frozen states are those of [`phase0/model.py`](phase0/model.py) (code as of this push). The deck of the instance
   is frozen, all cells together, in four states. Each port or cell in turn is the output:

   | State | Output |
   |---|---|
   | `hold` | the stored voltage |
   | `window` | the first stage of the window comparator, with the sensor node held by an ideal source where the comparator trips (DC sweep) |
   | `fire` | the first stage of the FIRE comparator, with the main charge held by an ideal source where it trips |
   | `pulse` | the main charge, held near 1.03 V through a noiseless 1 MΩ, with the port admitted at the peak current of a pulse |

   In every state:
   - the protection latch of each cell is held free by ideal sources. It is bistable at DC, and phase 0 saw `op`
     and `noise` settle on different states in the same deck;
   - the internal nodes of the NAND stacks get a noiseless 1e-12 S to ground;
   - the preset switches are noiseless 1e14 Ω resistors, except in `preset`.

   **The method** ([`phase0/devnoise.py`](phase0/devnoise.py), `devnoise.py extract`, with the code as of this
   push), the same for every instance. It does not use the noise analysis of a whole cell: phase 0 found that the
   operating point which ngspice's `noise` command solves for itself fails (gmin, then source stepping) on almost
   every state and instance, nominal included, where `op` and `ac` converge, and that its result is then computed
   about another point (the same op-amp transistor, at the same `op` point, came out 1.17 to 1.71 times noisier at
   `pulse` than at `hold` on 7102). For each cell and each state:
   1. **Isolation.** The cell is taken in the deck of the instance, under its seed, with every other cell out of
      the circuit but its mismatch draws kept: the other cells' transistors stay in place with their four terminals
      on ground (only `nfet_01v8`, `pfet_01v8` and `pfet_01v8_lvt` occur and are accepted), and their other
      elements are removed. A one-cell deck under `setseed` would draw another mismatch. Device noise is local, and
      the cells are joined only by the router outside the simulator and by ideal supplies. The isolated operating
      point of each cell must be that of the full deck within **1 µV on every node of the cell** (`op`, hold state).
   2. **Operating point** of the isolated cell (`op`, after the trip sweep where there is one).
   3. **The noise of each device at its own operating point**, in one `noise` run of a deck where every transistor
      of the instance stays in place (draws kept) but only the candidates are connected, each to ideal sources at
      the gate, source and body voltages of step 2 and at its drain through a 0 V probe; the probes' currents are
      summed by CCVS into the output, so that each device's transfer is exactly 1 Ω and its `.id` and `.1overf`
      parts are its channel thermal and flicker current densities. Every terminal is set, so this DC is trivial;
      it is checked: the drain current of each candidate equals its `op` current, |Δ| ≤ 10⁻³ |I_D| + 1 pA
      (magnitudes, as the sign of `@m[id]` follows ngspice's type and mode conventions).
   4. **Transfers**: by AC in the isolated cell deck, from a unit current between drain and source of each
      candidate (and across each design resistor) to the output.
   5. **Output density** Σ S_k |H_k|² (+ 4kT/R |H|² for the design resistors `rz`, `rda`, `rdl`, `rdp`, `rleak`).

   Candidates are the cell's transistors outside the logic gates (`inv`, `nand2`, `nand3`, `srlatch`); at every
   frozen state the logic outputs are held at the rails, which is checked (within 10 mV of 0 or 1.8 V). Any DC
   failure ("stepping failed") in the `op`, device or AC run fails the output.

   For each state and output, the devices that make 99 % of the output noise power over 10 Hz to 1.25 MHz are
   kept, with their white density A and flicker coefficient B (S = A + B / f^ef, `ef` from the model card).
   `preset` is extracted too, for V6 only. At the nominal hold point this method reproduces the whole-cell
   `.noise` of phase 0's pilot (the one point where that analysis was checked against a transient): the same
   four devices with shares 0.447 / 0.424 / 0.064 / 0.064, and A and B within 0.02 %.
2. **One source per device.** The model's devices are the union of the kept devices. Each gets one current
   source between drain and source. Its A and B are taken from the state where its share of an output is largest.
   **Source count**: phase 0 found the same 23 devices per cell on the nominal cell and on 7101, 7102 and 7103
   (per port: op-amp `xm1`–`xm4`, window comparator `xm1`–`xm4`, mirror `xmin`, `xmout`; per cell: FIRE comparator
   `xm1`, `xm3`, `xm4`), so **25 sources per cell** with the two shot terms of item 3: 75 in a three-cell network
   run. An instance whose union differs gets its own union; the count is recorded with its extraction.
3. **The declared non-device term** (owner's decision): per port, the shot noise of the mirror's input current, a
   white current of density 2qI with I = 173 nA (the peak of `bip`, from the parameters of `cell.spice`; the 300 nA
   of `noise.py` is not the peak of the cell's pulse), at the place of the injected mirror source
   (`gnm`, between `dq` and the stored node). It is the noise of the ideal current `bip`. The mirror transistors
   `xmin` and `xmout` are devices of the model and keep their own noise.
4. **Noiseless, and listed as such**:
   - the bias currents `ibs`, `ibo`, `ibm` and `idis`;
   - the pulse current `bip`, except item 3;
   - the references and supplies `vdd`, `vr0`, `vfire`, `vreopen`, `vcm`, `vhi`, `vlo`, `vpre` and `vinit*`;
   - the controls and their 10 kΩ filters, and the 1 kΩ injection resistors;
   - the behavioural sources;
   - the ideal leak `rleak` of the main charge (thermal noise kept only if extraction ranks it; it is a resistor);
   - the preset switch, in both its states.
5. **Samples** ([`phase0/noisegen.py`](phase0/noisegen.py)): every source is sampled outside the simulator, every
   NT = 0.4 µs, and drives, as a voltage on its own node, a VCCS between the device's drain and source (item 5c).
   The simulator draws no random number
   for the noise. A source has three parts:
   - **white**, from `SeedSequence([noise_seed, source_index])`;
   - **1/f^ef, shaped over at least twice the run**, from the same generator. It holds the frequencies from
     1/(m NT) up, where m ≥ 2 × the samples of the run;
   - **the slow part**, from 1/T_c up to 1/(2 m NT). It is a sum of 20 components per decade: a cos + b sin per
     log-spaced band, with a and b Gaussian of the band's variance. It comes from
     `SeedSequence([instance_key, source_index, 1])`: one realization per instance and source, taken at the run's
     virtual time.

   The parameters:
   - T_c = 1e5 s;
   - a run's virtual start is its position k in the instance's list of runs × 1 000 s. k counts from 0, and every
     run of the instance counts, measures and network runs alike;
   - instance_key is the mismatch seed, and 90000 for the nominal cell;
   - source_index is the position of the source in the sorted list of its names: device sources first, then the
     shot terms.

   So the runs of an instance share the slow 1/f realization, each at its own time. Two runs differ by what 1/f
   noise does over 1 000 s. Without that part, nothing slower than about 1/(2 T_run) would be present, and the runs
   would be quieter between themselves than the device models say.

   T_c and 1 000 s are declared choices, not measures. Below 1 Hz the density is the model's B/f^ef extrapolated,
   since the extraction does not go below 1 Hz.
5a. **T_c = 1e5 s and the gap of 1 000 s are fixed here, before any validation run, and are not changed after
   any result.**
   - **The justification is independent of the bench results**: what the same measurement would be on silicon.
     T_c is the span of one measurement session of a test chip on a bench, about a day (1e5 s ≈ 28 h). Within
     it the chip stays powered, and its 1/f noise runs continuously. Below 1/T_c the drift is outside one campaign.
   - The gap is the time between two consecutive runs of the same instance in such a session. On a bench, each run
     needs its reconfiguration (preset, reload of the calendar) and its readout, so a run takes minutes there,
     not 17 ms: 1 000 s ≈ 17 min.
   - **What they imply**, computed from the noise analysis alone (phase 0's pilot, nominal cell, `hold`, which the extraction reproduces within 0.02 %). The stored voltage has
     S = K/f^α with α = 0.843 and K = 6.3e-11 V² Hz^(α−1), fitted from 1 to 10 Hz. The slow part, below 1/(2 m NT)
     (9.5 Hz for a run of 17 ms), then gives each run an offset of **22.6 µV rms**, and two consecutive runs a
     difference of **31.2 µV rms**.
   - **Sensitivity** (information, not a tuning): with T_c from 1e4 to 1e6 s, the offset goes from 21.9 to 23.0 µV.
     With the gap from 100 to 1e4 s, the difference goes from 29.8 to 32.1 µV. With α < 1 the integral converges at
     low frequency, so these choices move the between-run constant by under 5 %.
   - The between-run constant of section 3 also holds the in-run part and the preset sample; this is only its part
     below 1/T_run. V5 reports that share as measured.
5b. **numpy pin.** The samples depend on numpy 2.3.5, and so does the reproducibility of a run from its noise seed.
   numpy does not guarantee its `Generator` stream (PCG64, `standard_normal`) across versions. The version is
   checked with the other hashes. Another numpy gives other draws of the same model, not the same run.
5c. **The source type.** The samples are read by **XSPICE `filesource` instances** (`analog.cm` of the pinned ngspice 42 package, SHA-256
   `98c7c296dfd04e81f568db91c8261a07f00d8d63e63e5cc1d331451ccda30941`, loaded by `codemodel` at start-up), **8
   sources per instance**, each instance reading its own text file sequentially (one row per sample time, `%.9g`),
   linear between samples (`amplstep=false`), sampled every NT = 0.4 µs. With an XSPICE device present, ngspice
   lowers trtol to 1 for the whole circuit; **`set xtrtol=7`** keeps the default of every other run. Why this type
   (phase 0; the code is `filesource` of [`phase0/cost3.py`](phase0/cost3.py), as of this push): campaign 4's need-4 run, four runs at a time, took 4 570 s with
   144 PWL sources, against 1 033 s with the 75 sources of the model as filesource (peak 717 MB), 1 316 s under the
   injected model and 814 s quiet ([`phase0/COST_C4_need4.json`](phase0/COST_C4_need4.json),
   [`phase0/COST_C4_need4_sources.json`](phase0/COST_C4_need4_sources.json)). One file of 76 columns stopped the deck at 1 µs ("timestep
   too small", even at zero amplitude); one column and groups of 8 do not. Phase 0 checked that the filesource
   returns the samples within 5e-9 of their rms across the stops and resumes of the router, and that campaign 4's
   need-4 run with the 75 sources **at zero amplitude** reproduces the quiet run: the same occurrences, writes and
   FIRE events, every stored voltage read by the router within 87 nV (tolerance 1 µV), FIRE dates within 0.1 µs
   (`phase0/ZEROCHECK_need4.json`). The full stored-voltage traces differ by up to 4.8 mV, only at write edges
   shifted by up to 0.1 µs between the two runs' time steps (median difference about 1 nV); reads and events are
   what the campaign uses.
6. **Noise seed of a run, by rule**: noise_seed = 10 × instance seed + round, the round counted from 1. For the
   nominal cell, noise_seed = 90000 + round. For the validation, the rounds of 7101 to 7103 start at 3, because
   71011 and 71012 were used in phase 0.

The model replaces the injected sources (`noise.json`) entirely: a run under it has no `trnoise` source.

## 2. Criteria

A criterion is checked on each instance (the nominal cell and 7101, 7102, 7103), unless the row says otherwise.
"Within x %" is on the ratio of the transient value to its reference. **The reference density** of an output is
the extraction's own, Σ S_k |H_k|² over every candidate and design resistor (section 1, step 5): what the model
claims, computed without any transient.

| | What | Draws | Passes when |
|---|---|---|---|
| **V1** | The generator alone (`noisegen.py psd`, numpy only, seeds from 2000): the mean periodogram of the samples against A + B/f^ef, for ef 0.84, 0.88 and 1.0; and the slow part, as the variance of a run's value and of the difference between two runs 1 000 s apart, against the integral of B/f^ef over its band | 400 seeds of 40 ms per exponent | every half decade from 316 Hz to 1.6 MHz within ±3 %; from 31.6 to 316 Hz within ±12 % (two bins next to a rectangular window); both slow-part variances within ±15 % |
| **V2** | The extraction, at each of the four states of the model (`hold`, `window`, `fire`, `pulse`) and each output; it must complete. (`preset` serves V6 only, through its output density) | none (`noise` of the device deck, AC) | the kept devices cover ≥ 99 % of the output power; per kept device, p95/p5 of A and of B·f^ef over the band ≤ 1.1; no single device of the logic gates holds more than 1 % of an output; the logic outputs at the rails (10 mV); no DC failure in the `op`, device and AC runs; every candidate's drain current in the device deck equal to its `op` current (10⁻³ relative + 1 pA); the isolated operating point within 1 µV of the full deck's; the extraction does not depend on the conditioning of the stack nodes (with and without it, the shares of the kept devices of the nominal cell are within 1 %) |
| **V2b** | Stationarity: a device kept in more than one state | none | its A and its B differ by at most 25 % between those states. A device that fails needs a source modulated by its bias, which this model does not have: the model is then **not validated** |
| **V3** | **Spectrum**, with the filesource sources of the model (not `trnoise`): mean periodogram (Hann) of each output in a transient of the frozen deck, against the reference density, by third of a decade from 4/T_draw to 464 kHz | `hold`: 32 draws of 80 ms (nominal), 8 draws of 80 ms (each development instance), all outputs at once. `window`, `fire`, `pulse`: 8 draws of 20 ms per output tested (nominal: port 1 and cell a; instances: port `a1`, port `b2`, cells a and b) | every band from 1 kHz up within ±10 %; below 1 kHz, every band within ±10 % or within 3 standard errors where those exceed 10 % |
| **V4** | **Low-frequency part**, on the `hold` draws of V3 (filesource sources), each draw at its own virtual time: the drift of a read (mean over 40 µs) over lags 0.36, 2, 5, 10 and 19 ms, and the band power from 25 Hz to 1 kHz, against the same from the reference density; and **between runs**, the rms difference of the run means of the stored voltage between two draws of an instance, against the reference density extrapolated as B/f^ef below 1 Hz with the virtual times of the draws | as V3 | nominal: every drift within ±10 %, the band power within ±15 %, the between-run difference within ±20 %; each development instance: ±20 %, ±25 % and ±30 %. The model's between-run difference **below 1/T_run** (its slow part alone) is reported against the reference value, whatever the verdict |
| **V5** | **Against the injected model**, descriptive, not pass/fail: the drifts and the between-run difference of V4, and the three constants of section 3, under both models; with the share of the between-run constant that comes from frequencies below 1/T_run under the model | as V4 and section 3, plus the same under the injected model | reported side by side with 0.090 / 0.064 mV (`NOISE.md`) and 0.111 / 0.094 / 0.009 mV (campaign 3, M5) |
| **V6** | **Out-of-band part**, at the `preset` point of each port: the variance across the integrating capacitor (stored node minus summing node) from the extraction's output density (Σ S_k\|H_k\|², devices only: the preset switch is noiseless, item 4) over 1 Hz to 100 MHz, against the variance of the stored voltage frozen by a transient preset (all sources on, each in its own run, sampled 1 µs after the end of the preset, against the same run without noise) | 32 draws of 50 µs per instance, all ports at once | within ±25 %. If the transient holds less than 75 % of that variance, the model is **not validated** as it stands. A sampled term would then be a corrected model, which needs its own justification (amendment 1, item 6) |
| **V7** | **Numerical floor** | 2 quiet trains, and 1 train with every source at zero amplitude (the same filesource instances and files, amplitudes 0), per development instance | the two quiet trains identical byte for byte; the zero-amplitude train gives the same writes and FIRE events as the quiet train and every read stored voltage within 1 µV; the train with zero sources gives, against the quiet train, every FIRE latency within 0.005 mV-equivalent (latency / slope) and every dose within 0.002 mV; no aborted run in the whole validation |
| **V8** | **Seeding** (owner's point 1) | on each development instance: 1 ms of the instance deck with the model, under 2 noise seeds and the first seed again | the operating point is identical to the last digit printed (16 digits) under both seeds and without the model; the first seed rerun gives the same stored-voltage waveforms byte for byte; the two seeds give noise (run minus quiet) whose correlation is below 0.1 in absolute value on every stored voltage |

**V2c — the cell-by-cell method against the full deck.** The reference is the same method run in the full
two-cell deck, without isolation (`devnoise.py extract --full`), on the nominal cell and on 7102, every state and
output. The device noise of step 3 depends only on the operating point; isolation can change only that point
(checked to 1 µV) and the transfers. If the reference does not complete on an output (its AC operating point
fails), that output is reported, and **V2c needs at least one completed output of each of the four states on each
of the two instances**; otherwise V2c fails. On the completed outputs the cell-by-cell method passes when:
- it keeps the same set of devices;
- every kept device's A and B agree within ±1 %;
- every share agrees within 0.01;
- the output rms of each band (1 to 10 Hz, 10 Hz to 1.25 MHz, above) agrees within ±1 %.

These tolerances were written before the comparison was looked at. The extractions are deterministic (no draw),
so they may be run in phase 0, but the comparison counts only as checked against these numbers.

**Condition on the method (owner).** The extraction must complete and pass V2, V2b and V2c on the nominal cell
and on all three development instances, 7101, 7102 and 7103. If it does not, the model is not validated.

**Rule for campaign 4.** A campaign-4 instance whose extraction fails V2 or V2b, or whose isolated operating point
fails the 1 µV check, gets no noisy runs. Its noisy runs are counted as **missing**, and its noise-free claims
stand.

**Verdict.** The model is **validated** if V1, V2, V2b, V2c, V3, V4, V6, V7 and V8 pass on every instance. V5 is
reported whatever happens. If the model is not validated, item 6 of amendment 1 applies: the default is the
simulator's noise, and a corrected model needs an independent justification, without looking at any campaign-4 data.
"The simulator's noise" of amendment 1 is, as the owner confirmed, the injected model of `../circuit/noise.py`
used in campaigns 1 to 3. ngspice 42 itself adds no device noise to a transient.

## 3. The constants for campaign 4 (owner's point 2)

From the validation runs only, under the model:

- **Trains**: per development instance, the noise-free train and **5 noisy trains of 10 reads per port**
  (`../network-circuit/phase1/noisechar.py`, calendar of 18 units), under noise seeds 10 × instance + round, rounds
  3 to 7. Each runs in its own process.
- **Rule**: the three constants are computed by the definitions of `../network-circuit/phase1/constants.py`.
  - **between-run**: rms of the run offsets of all ports, pooled over the three instances;
  - **within-run**: scatter of the FIRE latency about the mean of its run, divided by the slope, pooled;
  - **per-dose**: rms of (dose in a noisy train − dose without noise), pooled.

  A train that does not give the word of the noise-free train is excluded from the run offsets and the scatter,
  as in phase 1. It is counted and reported.
- **Campaign 4 uses, per constant, the maximum** of the validation value and 0.111 mV (between), 0.094 mV
  (within) or 0.009 mV (per dose).

These constants are computed and reported whatever the verdict. If the model is not validated, they are not used.

## 4. What the validation hands to campaign 4

- **How to generate the model of an instance**: `devnoise.py extract` on its deck with its seed, the rule of section 1
  for the sources, `noisegen.py` for the samples, the seed rule of item 1.6. The extraction is run once per
  instance, before its runs, and its output is recorded with its SHA-256.
- **Compute per run**: measured with the filesource sources on the trains of section 3 and on three-cell network runs
  of the nominal cell with campaign 4's calendar (`dnf.calendar(4, 4, 4, 4)`, about 17 ms, and the longest,
  `dnf.calendar(5, 5, 5, 5)`, about 20.5 ms), under the model and quiet, four at a time: the factor over a quiet run in the cost model of
  campaigns 2 and 3, the generation and parse time of the samples, and the peak memory per run (which limits how
  many runs fit at a time on a machine); and the cost of an extraction per instance.
- **The numerical floor**: from V7.

## 5. Compute of the validation

Estimated, four runs at a time per machine. The frozen 2-cell deck is about 1 600 s per 80 ms draw (measured with
PWL sources in phase 0; the filesource should not be slower):

| Part | Estimate |
|---|---|
| V3 and V4 `hold`, nominal (32 × 80 ms, one cell) | 1.8 h |
| V3 and V4 `hold`, three instances (8 × 80 ms, two cells) | 2.7 h |
| V3 `window`, `fire`, `pulse` | 2.5 h |
| V6 | 0.3 h |
| Trains of section 3, and V7 | 1 h |
| Extractions: the four instances by `devnoise.py`, four at a time (measured in phase 0: about 1 h 45), and the V2c references of the nominal cell and 7102 (about 2 h, two at a time) | 2 h |
| V1, V8 | 0.3 h |
| **Total** | **about 10.6 h of one 4-processor machine, or about 5.5 h on two** |

The extractions are deterministic (no draw). Those of phase 0, made with the code of this push, are rerun and must
give the same results to the last digit written; if they do not, the rerun counts.

The owner sets the budget. If it is smaller, the cuts are made in the number of draws of V3 outside `hold`, and are
pushed before the runs.
