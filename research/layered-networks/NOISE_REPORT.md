# The injected noise model on the layered decks (plan step 3): implementation and validation

**Development only, nothing preregistered.** Dev seeds 9801 (NOT1) and 9802 (ANDOR3) only. No campaign or dry-run
seed was used. The deck is the 2x design point, with the C5 inverter not involved (neither spec has one in its noisy
path; NOT1's inverter keeps zero noise sources).

## The model, and its sources

`noise2.py`, a new file. No pushed file changed.

- **Sources.** Each R-cell port's zero sources `vnzc`, `vnzo` and `vnzi`, and the cell's `vnzm`, become trnoise
  sources: 7 per cell.
  - Method: research/network-circuit/net.py `deck(noise=True)` (evidence/function-family-campaign-predicted d7e4fcc2,
    lines 85–96).
  - Amplitudes: research/circuit/noise.json `params`, input-referred from the blocks' small-signal analyses
    (research/circuit/noise.py):
    - window comparator: vncw, vncf;
    - integrator op-amp: vnow, vnof;
    - mirror shot: inmw;
    - FIRE comparator: vnmw, vnmf;
    - sampling: tnz = 0.4 µs.
  - The inverters keep zero sources: net.py injects into R cells only, and the C5 instances were characterised
    without noise.
- **Seed.** ngspice 42 seeds trnoise from getpid(). The shim research/circuit/repetition/fakepid.c (compiled to
  build/fakepid.so, preloaded) returns `FAKEPID` = 10 × S + n, the rule of campaign 6 §4 and campaign (a) §4.
  - The mismatch draw stays `setseed S`, as before.
- **Constants.** Decision 5: b = 0.111 mV between runs, w = 0.094 mV within a run, d = 0.009 mV per dose
  (research/learned-dnf-circuit/DECISIONS.md; measured in campaign 3, network-circuit-ring-campaign-3 REPORT.md M5).
  They remain the budget constants (K3 = 3σ). The injected sources are the model.
- **The noisy run.** `noise2.py run SPEC OUT SEED ROUND [scale=1]`: training and tests only (the same calendar loop
  as instrument.cal_run), no scans.
  - It writes `OUT/noisy_record.json`, with the instrument's words, lessons, tests and slots layout, plus `round`,
    `noise_seed` (null when noise is off), `noise_scale` and `input_spice_sha256`.
  - ROUND 0 means noise off: dc sources and no shim.

## Validation

| Check | Result |
|---|---|
| **Zero-noise identity, noise off against the no-noise path** (`tests/check_noise_identity.py pipeline`) | **holds**: NOT1, all 6 training and test slots, and ANDOR3, all 24, are equal field for field to the pushed 2x records (dev/cal5_not1, dev/cal5_andor3), with the same words, lessons and tests |
| Zero-amplitude sources under the shim, against noise off | every stored voltage u and every routed emission is identical. **The latch dates differ by 1–10 ns** (in 4 of 6 slots): the trnoise sources add time points every 0.4 µs. Listed as an excepted difference; the noise-off path is the identity |
| Replay: the same noise seed twice (98011) | **byte-identical** records, every field outside EXCEPT (cost, round, noise_seed, noise_scale, input_spice_sha256) |
| Different seeds | records differ: u up to 83 µV apart (NOT1 rounds 1 and 2) and 133 µV (ANDOR3) |
| **Noisy completions** | NOT1: 3 of 3 rounds complete, word `ssFF` as without noise, outputs correct. ANDOR3: 2 of 2 rounds complete, all 8 outputs correct. c1_0's word becomes `sssFF` (noise off: `ssFF`): its crossing is at its stop (DESIGN_POINT_REPORT.md), it is not measured, and it has no prediction |

**Measured against the model** (`noise2.py bwd`, files `dev/noise/bwd_*.json`):
- Per port, x = u_noisy − u_off over the slots matched by kind, info and occurrence.
- Each cell is compared while its read outcomes agree with the noise-off run.
- The dose step is read only between consecutive slots in both runs.

| | NOT1 (3 rounds, 6 port-runs) | ANDOR3 (2 rounds, 16 port-runs) | model (decision 5) |
|---|---|---|---|
| b, run offset of the stored voltage (rms) | 0.061 mV | 0.046 mV | 0.111 mV |
| w, scatter within a run (rms) | 0.004 mV | 0.006 mV | 0.094 mV |
| d, spread of a dose step (rms, 6 and 24 doses) | 0.011 mV | 0.009 mV | 0.009 mV |
| FIRE latch shift against noise off (rms) | 0.42 µs (9 reads) | 4.5 µs (60 reads, including c1_0 at its crossing) | — |

- **d agrees with the model. b on the stored voltage is about half of it, and w is far smaller.**
- That is expected, not a failure of the path:
  - Campaign 3 read b and w from **FIRE latencies** converted to mV through a slope. They include the FIRE
    comparator's noise at the decision.
  - u is a 35 µs average of the stored voltage, which averages the white parts out.
- The latency comparison in mV needs that slope, which is **not measured here**. So decision 5's b and w are not
  re-measured by this validation.
- On the stored state, the injected noise is at or below the model (b), or equal to it (d). The model stays the
  stated, pessimistic budget constant.

## Cost

| | NOT1 | ANDOR3 |
|---|---|---|
| noise off, training + tests (CPU) | 1.5 min | 25.3 min |
| noisy run (CPU) | 2.0 min (×1.33) | 36.0 min (×1.42) |

- Validation in all: 1.8 CPU-hours (NOT1 11.5 min over 6 runs, ANDOR3 97 min over 3 runs). Development took about
  2 h.
- **Correction to CAMPAIGN_PLAN_DRAFT.md §5 and §7**: a noisy run costs about 1.4× the run without noise, not 1×.
  - ANDOR3 is about 36 min, not 26.
  - XOR3 is about 60 min [G, ×1.42 on 41.7], not 42.
  - On 12 machines, the noisy-run line grows from 37.1 to about 53 core-h, so the total is about 238 against the
    ceiling of 240.
  - On the 8-machine fallback (46/42), it grows by about 11 core-h, to about 170 against 160. So the 8-machine sizes
    would need a further cut, for example XOR3 46 → 40.
  - This is to be settled by the owner before the freeze; the plan file is not changed here.

## Open

- The XOR3 noisy path (inverters at zero noise, C5 inverter in front) has not been run: it is to be run in the dry
  run.
- The latency slope, if b and w are to be re-measured in mV as campaign 3 did.
- `noise_sha256`: not recorded. A run is fixed by `input.spice` and `noise_seed`, and replays byte-identically.
