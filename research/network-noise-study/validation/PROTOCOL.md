# Validation of the device-noise model: how the criteria are run

This file fixes, **before any noisy validation draw**, what [`../VALIDATION_CRITERIA.md`](../VALIDATION_CRITERIA.md)
(5a24d10) and [`../VALIDATION_AMENDMENT_1.md`](../VALIDATION_AMENDMENT_1.md) (4169e91) leave to the implementation.
It changes no criterion and no tolerance. The code is [`vrun.py`](vrun.py) (one run), [`vplan.py`](vplan.py) (the
list of runs) and [`vanalyze.py`](vanalyze.py) (the criteria), as committed with this file.

## The model of an instance

From `DEVNOISE_<instance>.json` of this folder (the validation's own extraction, which must equal phase 0's):
- the devices: per cell, the union of the devices kept at `hold`, `window`, `fire` and `pulse`; each with the A, B,
  ef and nodes of the state where its share of an output is largest;
- the shot terms: per port, 2qI with I = 173 nA, between `dq` and the stored node;
- the sources are sorted by name, the devices first, then the shot terms (`shot.x<c>.x<p>`); the position in that
  list is `source_index`. A deck that holds only some cells (an isolated cell) has only their sources, numbered in
  their own list;
- each source drives, through a VCCS of gain g = sqrt(A / 2NT) / 1 mV, a node whose samples come from
  `noisegen.samples(noise_seed, source_index, n, A/g², B/g², ef, slow=(instance_key, k))`, with **the first sample
  set to 0**: the operating point of a run is that of the deck without the model, as V8 requires. instance_key is
  the mismatch seed, and 90000 for the nominal cell;
- the samples are read by `cost3.filesource` (8 sources per instance, `xtrtol=7`); each run's samples files are
  hashed (SHA-256, recorded with the run) and deleted.

## Seeds, rounds and positions

noise_seed = 1000 × instance seed + round for 7101–7103, 90000 + round for the nominal cell (amendment 1). A run's
virtual position k (its virtual time is k × 1 000 s) is its round minus 3 (7101–7103) or minus 1 (nominal). The
rounds are given in this order, so that the positions follow the order of the list:

| Runs | Nominal: rounds | 7101–7103: rounds |
|---|---|---|
| V8: two seeds (the first again, the same round) | — | 3, 4 |
| V3/V4 `hold`, 80 ms | 1–32 | 5–12 |
| V3 `window`, `fire`, `pulse`, 20 ms, 8 per output: nominal `window a1`, `fire a`, `pulse a1`; instances `window a1`, `window b2`, `fire a`, `fire b`, `pulse a1`, `pulse b2`, in this order | 33–56 | 13–60 |
| V6, 50 µs | 57–88 | 61–92 |
| Section 3, the noisy trains | — | 93–97 |

Runs without noise (quiet, zero amplitude) and under the injected model (V5, seeded by the simulator's process
number, as in campaigns 1 to 3) have no round and no position. Seeds 7501–7520 are never simulated; `pilot.seeded`
refuses any mismatch seed but 7101–7103.

## The runs

- **V3/V4 (`frozen`)**: the frozen deck of `model.analysis_deck`. At `hold`, the nominal cell is one cell (as the
  criteria say), and each development instance is its two-cell deck, every stored voltage at once. At `window`,
  `fire` and `pulse`, the deck is the isolated cell of the extraction (V2c shows the isolation changes nothing),
  with the comparator's source at the extraction's trip value. `tran 0.2u T 0 200n`, the outputs linearized on
  0.2 µs.
- **V5 (`frozen … injected`, `train … injected`)**: the same decks and trains with the trnoise sources of
  campaigns 1 to 3 (`net.deck(noise=True)`) instead of the model: 32 `hold` draws of the nominal cell and 8 per
  development instance, and 5 trains per development instance.
- **V6 (`preset`)**: 50 µs of the instance deck (`net.deck`, two cells) from t = 0, `tran 0.1u 50u 0 200n`, and
  v(vmem) − v(sum) of each port at 3.1 µs (the preset ends at 2.1 µs). "The same run without noise" is the run with
  the model's sources at zero amplitude, so that the difference holds only the noise. One per instance.
- **V7, section 3 (`train`)**: the calendar of `noisechar.py` with 10 reads per port, two cells, through the
  router: two quiet trains, one at zero amplitude, five under the model (rounds 93–97), five injected. The
  noise-free train of section 3 is the first quiet train. The scans of `constants.py` (noise-free) are those of
  phase 1 (`../../network-circuit/phase1/MEASURES.json`), which are deterministic.
- **V8 (`seeding`)**: `op` (every node, 16 digits) and 1 ms of the instance deck with the model under rounds 3 and
  4, round 3 again, and the deck without the model (`quiet`).

## The extractions (`vextract.py`)

The four instances by `devnoise.py extract` (five states, cells a and b), the V2c references by `--full` (nominal,
7102) and the nominal cell by `--no-cond`, with the code of 5a24d10 (`--no-cond` added since, default unchanged).
Equality with phase 0: every output and the operating-point check, as written in the JSON files. V2, V2b, V2c: by
`../phase0/compare.py`. V2's conditioning check: at every output of the four states of the nominal cell, every kept
device's share with and without the conductance within 0.01 (1 % of the output power, absolute).

## The analyses (`vanalyze.py`)

- **The reference density** of an output is the extraction's `onoise` (devices and design resistors), plus the
  shot terms' Σ S|H|² from the same AC (amendment 1, item 2; `vanalyze.py shot`, stored in `SHOT_<instance>.json`).
  At `hold` the reference of a stored voltage is that of its isolated cell. Below 1 Hz it is extended as K/f^α,
  fitted on 1 to 10 Hz.
- **V3**: per draw, the Hann periodogram of the output minus its mean, P = 2 dt |FFT(x w)|² / Σ w²; their mean over
  the draws, by third of a decade on the grid 10^(n/3) Hz, every band wholly between 4/T_draw and 464 kHz, against
  the mean of the reference over the same bins. The standard error of a band is the standard deviation of the
  per-draw band means over √draws, relative to their mean.
- **V4**: a read is the mean over 40 µs (200 points); the drift at a lag is the rms of read(t + lag) − read(t) over
  every t of every draw; its reference is ∫ S(f) sinc²(f · 40 µs) 4 sin²(π f lag) df. The band power is the integral
  of the mean periodogram from 25 Hz to 1 kHz, against that of the reference. Between runs: the rms of the
  differences of the run means of consecutive draws (positions k and k + 1), against
  ∫ S(f) sinc²(f T) 4 sin²(π f · 1 000 s) df from 1e-9 Hz. The part below 1/T_run is reported from the reference,
  with the measured total.
- **V6**: per port, the variance over the 32 draws of u(draw) − u(zero), against the reference variance across the
  capacitor over 1 Hz to 100 MHz (the extraction's three band rms of `preset`, devices only, as the criteria say).
- **V7**: the quiet trains' waveforms (SHA-256 of the raw file) must be equal; the zero-amplitude train against the
  first quiet train as `../phase0/zerocheck.py` does (same occurrences, writes and FIRE events, every read stored
  voltage within 1 µV), and every FIRE latency within 0.005 mV-equivalent (Δlatency / the slope of the train in
  `constants.py`) and every dose within 0.002 mV.
- **V8**: the operating points compared on every node common to the decks with and without the model; the
  waveforms of round 3 and its rerun equal byte for byte (SHA-256 of the raw file); the correlation of
  (run − quiet) between rounds 3 and 4, per stored voltage.
- **Section 3**: `constants.instance` of `../../network-circuit/phase1/constants.py` on the phase 1 scans, the
  first quiet train and the five noisy trains; pooled over the three instances as the criteria say: between-run, the
  rms of every run offset; within-run, the pooled scatter; per dose, the rms of every dose deviation. The same under
  the injected model for V5.

## Two machines

The owner's budget runs the plan on two machines of four processors. Machine 2 (a second session of the same
environment) runs V5 (every injected draw and train) and V3 at `window`, `fire`, `pulse` of the nominal cell and
7103 (`vplan.py run WORK machine=2`); machine 1 runs the rest. Every run checks the pinned environment first
(ngspice, the PDK commit, numpy 2.3.5, `analog.cm`). The draws are the same on either machine (their samples follow
from the seeds alone). A frozen draw keeps, besides its waveform, the summary that V3, V4 and V5 use
(`vrun.summarize`: the mean; per lag, the sum of squared drifts of the 40 µs reads and their count; the
periodogram's mean over each band of the grid; its integral from 25 Hz to 1 kHz), so that machine 2 sends only
the summaries (`validation/m2/`), and the trains' `result.json`.

## Harness tests

Before the draws, the harness is tested on short runs under rounds 900 and up, which belong to no criterion and
whose results are not used.
