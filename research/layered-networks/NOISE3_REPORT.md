# Inverter noise in the noisy runs (noise3.py), and the sealed stage-N entry point (controls3.py)

**Development only, nothing preregistered.** Dev seeds 9801 (NOT1) and 9803 (XOR3, C5 overlay) only. New files:
`noise3.py`, `controls3.py`, `tests/check_noise3_identity.py`. No pushed file changed.

## What is injected

Exactly what the C5 inverter's K3 gate budgets: research/inverter-instances `invinst/gate.py` `allowance()`, from
research/circuit/noise.json, with the placement given by the inverter-kit worker. Nothing else is injected: not the
latch, the reset gate, the leak resistor or the comparator bias.

| Component | Budget (σ, in x) | Injected |
|---|---|---|
| FIRE comparator input noise, on the threshold δ | fire_comparator.total_input_uV / vunit = 335.029 µV / 0.5 = **6.70e-4** | the inverter's zero source `v.xn<j>.vnzm` becomes `trnoise(vnmw tnz 1 vnmf)` = trnoise(3.166e-4 4e-7 1 1.095e-4). It enters the comparator reference through bvrm, rvrm and cvrm, as in the R cell and in cert_run.py's frozen cell |
| Shot charge of the two mirrors, on η and taken from Q | √2 · inmw · √(D·tu·tnz) / (cq·vunit) = **7.84e-4**, each mirror integrated over the whole slot [0, D] | two independent `trnoise(inmw tnz 0 0)` sources on their own 1 kΩ nodes. A behavioural current `bnz<x>` puts (n_h + n_j) × window into xn<j>.vq. The window `vkw<x>` is 1 on [T, T + D·tu] of each slot, set with the inverter's other gates, so no mirror noise acts outside the budgeted interval |

- The R cells keep noise2's sources.
- **Seed:** one FAKEPID = 10 × S + n for the whole run, recorded (`noise_seed`, `noise_model`).
- Each inverter's vq is saved. Per slot, x = (vr0 − vq)/vunit at T + τ and T + D is in the record's `inverter_x`.

## Validation

| Check | NOT1 9801 | XOR3 9803 |
|---|---|---|
| noise off (round 0) against the pushed no-noise record | all 6 slots equal | all 27 training and test slots equal |
| **zero-amplitude identity** (`check_noise3_identity.py`): every source present at 0, against noise off | **holds**: decks equal outside the noise lines; every u, emission, word, lesson, test and skew equal. Latch dates differ by −3 to +10 ns, from the added time points (listed) | words, lessons, tests, skews and emissions equal. **3 of 232 u values differ by 0.1 µV**, the record's last printed digit (the averaged voltage rounds the other way). Latch dates differ by −4 to +17 ns (listed). **So the identity holds within the record's resolution, not bit for bit** |
| **replay**, same seed 98011 twice | **byte-identical** outside EXCEPT | — (NOT1 only) |
| **noisy completions** | rounds 1–3: word `ssFF`, outputs NOT, all correct | round 1 (98031): words as without noise; outputs 00 silent, 10 FIRE, 01 FIRE, 11 silent, all correct; **S holds** (both skews silent) |

**The measured inverter perturbation against the budget** (`noise3.py budget`):
- The reference is the **zero-amplitude** run, which has the same time points as the noisy run. Against noise off, the
  interpolated x readings differ by up to 0.14 x at one reading near the reset edge (NOT1), so noise off is no
  reference for x.
- Per inverter and matched slot, Δx = x_noisy − x_zero.

| | NOT1 (3 rounds) | XOR3 (round 1) | expected from the model | K3 budget (3σ) |
|---|---|---|---|---|
| Δx at T + τ (rms) | 0.00040 (18) | 0.00038 (54) | σ_q·√(τ/D) = 0.00039 | — |
| Δx at T + D, silent slots (rms) | 0.00075 (3) | **0.00058 (27)** | σ_q = 0.00078, about 0.00062 after the leak over D | **η: 0.00235** |
| max \|Δx\| | 0.00115 | 0.00134 | | inside 3σ |
| FIRE latch shift, firing slots | 5.3 ns rms, max 11 | 5.4 ns rms, max 17 | | — (the gate budgets no emission time; δ shows only through x at the trip) |

- **The injected mirror charge matches the budget's σ_q**, reduced by the leak, and every reading is inside 3σ.
- **The comparator component** is on the trip level, not on x. Its effect shows as the few-ns latch jitter. It is not
  separately measured in x here; that would need the comparator's trip level saved.

## controls3.py, the sealed stage-N entry point

For the pipeline driver (`campaign_run.py`, research/layered-stage-d), on the coordinator's assignment.

- `controls3.py stagen SPEC OUT SEED ROUND seal_log=<40-hex> seal_branch=<branch> [scale] [overlay]`: noise3's
  stage N, with the skew slots.
- `controls3.py untrained SPEC OUT SEED seal_log=… seal_branch=… [overlay]`: controls2's U.
- **Refusal:** exit 2 before any session, with no OUT created, when seal_log is absent or not 40 lowercase hex, or
  seal_branch is absent. Checked on three refusals: no seal, "ABC", no branch.
- **Record:** a top-level `"seal_log": {"commit", "branch"}` in noisy_record.json and untrained_record.json.
- Checked on NOT1 9801: round 0 equals the pushed no-noise record, U holds, and seal_log is recorded in both.

## Cost (CPU minutes)

| | noise off | zero amplitude | noisy |
|---|---|---|---|
| NOT1 | 1.5 | 1.8 | 1.95 |
| XOR3 | 40.6 | 45.1 | 50.8 (×1.25) |

- Validation in all: about 2.6 CPU-hours.
- The inverter sources and the vq reads add little: XOR3's noisy run took 50.8 min here, against 55.4 under noise2
  alone (a different load).
