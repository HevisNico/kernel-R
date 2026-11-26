# Campaign plan for Wednesday: DRAFT (revision 2, after the owner's review)

**Draft: no simulation, nothing frozen, nothing preregistered.**
- Numbers come from the 2x development runs: DESIGN_POINT_REPORT.md (9801, 9802), XOR3_REPORT.md (9803),
  YIELD_CHECK_2X.md, and the inverter lot 2 (C5, 60/60).
- The rules are those of campaign (a) (`evidence/function-family-campaign-predicted`, PREDICTION.md §3–§6) unless
  stated otherwise.
- Marks: [K] measured; [I] inferred; [G] an estimate.

## 1. The groups

| Group | Function | Circuit | Why |
|---|---|---|---|
| 1. NOT in one layer | NOT1, y = ¬x | 1 inverter + 1 copy cell | smallest network with a front end; full chain proved on 9801 |
| 2. Layers without NOT | ANDOR3 | both + copy → either → copy | every R gate type over 3 layers (9802) |
| 3. Layers with NOT | XOR3, y = x0 ⊕ x1 | 2 C5 inverters + 4 R cells | needs the rails; proved at K0 on 9803 |

- One validated function per group.
- Another function enters only if it passes the dry run (§9).

## 2. The design: a direct test first

**The primary claim is the direct comparison, as in campaign (a).**

For each instance (one mismatch seed), the work runs in two sessions of the same deck and seed, so the cells are
physically the same.
- **Stage D (per-cell measures), before any network run.**
  - A calibration session: each cell scanned from its preset, the family's order. This is an ascent with
    both-direction repeats under rule v2, then the guarded fit and the gate at K0 and K3. Each inverter's gate is
    measured too.
  - **The prediction** is written and hashed before stage N starts:
    - every training word (`need` letters `s`, then `F`, per port and line);
    - every output on all `2^m` patterns;
    - eligibility at K0, and room at K3.
- **Stage N (the network run), without noise**: training, tests and the shift slots (§6).
  - The observed words and outputs are compared **directly** with the prediction.
  - **One differing letter or output, on one counted instance, refutes.**
- **Stage N under noise, on instances with room**: 3 noisy runs (rounds 1–3), each predicted to train and answer
  every pattern as stated. One difference refutes.
- **Secondary, a control** (close to comparison M8):
  - The kernel's recognition theorem is applied to the stage-N traces: `layered_recognition_at`, or
    `layered_inverters_chained` for groups 1 and 3. Stage D's anchors are applied to stage N's measured stored
    voltages.
  - It is reported per instance as agreeing or not with the direct verdict, and it decides no claim.
- **No prediction, no claim.** An instance without eligibility (or without room, for noise) has no prediction. Any
  run made on it is reported as observed and counts for nothing.

**New code, before the freeze.**
- Stage D as its own session: today's scans run in situ, after training.
- The predictor from the stage-D fit.
- The comparator.

These are built on the existing modules, as new files [G: about half a day of development, plus the dry run].

## 3. Draws and expected counts (12 machines)

Per-cell rates at 2x [YIELD_CHECK_2X]:
- K0: about 0.97 per cell;
- K3: both 0.72, copy 0.81, either (max rule) about 0.35;
- inverter: 60/60;
- the not-measured class: about 0.4 % per group.

Independence is assumed. Intervals are 90 % and widened for the rate uncertainty [G].

| Group | N | eligible K0, expected (90 %) | with room K3, expected (90 %) |
|---|---|---|---|
| NOT1 | 60 | 58 (55–60) | 47 (40–53) |
| ANDOR3 | 60 | 54 (49–58) | 10 (5–16) |
| XOR3 | 66 | 58 (53–62) | 10 (5–15) |

## 4. "Established", fixed now from the expected counts

Per group and level:
- **Counted instance**: eligible (K0) or with room (K3), and with its runs complete.
- **Refuted**: by one differing letter or output on any counted instance of the group at that level. The refutation
  is reported whatever the count.
- **Only where a prediction exists.** A difference refutes only on an instance that has a prediction: eligible at K0
  for the run without noise, with room at K3 for the noisy runs. A run outside eligibility or room has no prediction.
  It is reported plainly as observed, never as "predicted to fail", and counts for no claim and no refutation.

| Level | "established" | "held on k instances, not established" | "held on one instance" | "not established" |
|---|---|---|---|---|
| K0, no noise | **≥ 30** counted | 2 ≤ k < 30 | 1 | 0 |
| K3, noisy runs | **≥ 5** counted | 2 ≤ k < 5 | 1 | 0 |

- **Why these thresholds.**
  - At K0, 30 is about half of every group's expected count, and below the 8-machine counts of §7.
  - At K3, 5 lies below every group's lower 90 % bound or at it: P(fewer than 5) is about 10 % for ANDOR3 and XOR3
    [G]. NOT1's K3 also needs ≥ 5.
  - Campaign (a)'s minimum was 2. These are stricter because the samples are larger.
- **For all three groups** (the claim "NOT, monotone layers and both together"): established only when each group is
  established at that level. Otherwise it is worded per group.

## 5. Noise, decided now

- **The K3 runs inject noise**: campaign (a)'s injected model with decision 5's constants:
  - b = 0.111 mV between runs;
  - w = 0.094 mV within a run;
  - d = 0.009 mV per dose.
  - It is stated as the pessimistic model. Noise seed: 10 × S + n.
- **Noisy runs are predicted, and can refute, only on instances with room at K3.** Every cell has room, and the
  inverters' gate holds at K3. A noisy run made elsewhere, for example in the rehearsal's sensitivity reading, is
  reported as observed, never as a predicted failure, and counts for nothing.
- **To build.** This package has no noise sources (`deck.py`: "No noise sources"). So the work is:
  - a new module that drives each R cell's stored voltage per campaign (a)'s path. That path is to be read in its code
    for method, not wrapped;
  - the seed rule;
  - the recorded `noise_sha256`.
- **To validate before the freeze, in the dry run:**
  1. with all three constants at 0, a noisy run is identical to the run without noise (`input.spice` and the record);
  2. on one dev instance per group, the perturbation read on the recorded stored voltages has the stated b, w and d,
     within their sampling error (campaign 3's definition, as in campaign (a)'s sensitivity reading);
  3. the noisy runs of NOT1, ANDOR3 and XOR3 complete.
- **Cost.**
  - Development: about 3–4 h [G].
  - Validation: about 6 core-h [G].
  - In the campaign, each noisy run costs a training and the tests: NOT1 1.4, ANDOR3 about 26, XOR3 about 42 CPU-min
    [K, from the 2x runs].
- **The noise path also runs in the rehearsal** (§8).

## 6. Controls (campaign (a))

- **U, untrained.** One run per group, on its first eligible instance in seed order: the `2^m` test slots only, from
  the preset, with every R cell gated. **No R-cell output fires on any pattern.** The inverters still fire on absent
  inputs, which is expected and reported.
- **S, shift.** In each stage-N run, one skew slot per both cell: its two inputs arrive outside its window, and **the
  both cell stays silent.** That is 1 slot for ANDOR3 and 2 for XOR3.
- **Duplicate.** One instance per group is rerun on a second machine.
  - **Criterion, fixed now:** `input.spice` byte-identical. The record and the verdict files are identical except for
    the cost and wall-time fields, which are listed in the freeze. `session.log` is excluded, because it carries dates.
  - A failure is reported as a defect of the environment, and no instance is dropped.

## 7. Budget, and the machines

- **Cost per attempt** without noise, CPU-min [G, from the 2x runs, stage D replacing the in-situ scans]:

  | Group | Stage D | Stage N with shift slots | Total |
  |---|---|---|---|
  | NOT1 | 3 | 1.5 | 4.5 |
  | ANDOR3 | 40 | 27 | 67 |
  | XOR3 | 45 | 44 | 89 |

- **The D4 audit.** Stage-D solo scans on every 6th instance per group: +0.6, +45 and +30 min.

| | NOT1 | ANDOR3 | XOR3 | Controls | Total |
|---|---|---|---|---|---|
| no-noise attempts | 60 × 4.5 = 4.5 h | 60 × 67 = 67.0 h | 66 × 89 = 97.9 h | | |
| noisy runs (3 per instance with room) | 47 × 3 × 1.4 = 3.3 h | 10 × 3 × 26 = 13.0 h | 10 × 3 × 42 = 20.8 h | | |
| D4 audits | 0.1 h | 10 × 45 = 7.5 h | 11 × 30 = 5.5 h | | |
| U + duplicate | | | | 0.2 + 2.7 h | |
| **core-hours** | 7.9 | 87.5 | 124.2 | 2.9 | **≈ 222** |

- **Twelve machines** give 12 × 4 × 5.5 h = 264 core-h. **Ceiling: 240.**
- **Cut order if the ceiling binds**, with launches in published seed order:
  1. the audits;
  2. XOR3 instances past the 46th;
  3. ANDOR3 instances past the 42nd.
  - NOT1 is never cut.
  - A job not started is "not run", with its seed. It is not a failure and is not replaced.
- **Machines.** Only 8 have run together before.
  - **The rehearsal starts all 12.** A machine that fails `envcheck.py`, or does not finish its rehearsal share, is
    dropped before the campaign.
  - **Fallback, written now: on 8 machines, reduced sizes at the same duration** (5.5 h, ceiling 160 core-h), not a
    longer day. The reason is that the blinding window and the day's schedule stay as they are. The reductions are,
    in this order:
    - XOR3 66 → 46;
    - ANDOR3 60 → 42;
    - NOT1 stays at 60.
  - On 8 machines this totals about 159 core-h. The expected K3 counts become about 7 and 7: P(fewer than 5) is about
    20 % [G], so K3 is more likely to read "held on k instances".
  - With 9–11 working machines, the sizes are interpolated linearly between the two plans, rounded down, and fixed at
    the end of the rehearsal before the seed draw.

## 8. Seeds and the freeze

- **Fresh seeds.** A published draw after the freeze: SHA-256 of a public beacon value at a round fixed in the freeze
  commit, mapped to integers.
  - Excluded: every dev seed (8301–8310, 8501–8515, 9711–9770, 9801–9803), the dry-run, rehearsal and noise seeds.
  - The draw script is frozen and asserts the exclusion.
- **Frozen, by sha256:**
  - the code (this package, the Lean library, ngspice 42 pinned, SKY130 1232782c);
  - the gates (fit, budgets, cell validity, `CircuitInverterGate`, the inverter instance gate);
  - the configs (`config.json`, `calibration.json` with `d4_stage` 0.005 and the cap of 64,
    `config_inverter_c5.json`, the specs, the noise constants);
  - the design point (vhi 0.7, reltol 1e-5, areas);
  - the analysis script.

## 9. Premises, expectations and limits (PREDICTION.md)

- **Open premises, each "assumed, not proved".** The wording is reduced to "computes f, under these premises":
  - the leak along the trajectory (H_drift, measured);
  - the simulator's measured real hypotheses;
  - the latch, measured, not bounded;
  - the routed walk (the 0.4 µs grid and the launch rule, checked per trace, with no soundness proof);
  - D4 (`d4_stage` 0.005, audited).
- **Failure rule.** An instance whose observed premise fails, or whose run fails, is counted and reported under its
  first failing clause. It is never dropped and never re-run.
- **Expected in advance.** The inverter-fed outputs and the either cells will be the noisy ones: the either cell's K3
  room is about 0.35, from one instance that missed it by 266 units. The injected model is pessimistic.
- **Limits carried.** The shared stimulus in ANDOR3, the ngspice convergence line (counted per run), the router grid
  (0.02 tu), and the 200 ns maximum step (no effect on 9803).

## 10. Steps

1. **Full dry run BEFORE the freeze**, on dev seeds 9804–9806:
   - stage D, the prediction hash, stage N, the noisy runs with the zero-noise identity, U, S, the duplicate, the
     Lean control, the aggregation and the report;
   - fixes land before the freeze.
2. **Freeze**: a tag and a hash commit.
3. **CI** at the tag.
4. **PREDICTION.md**: §2–§9, with the established rule and the fallback.
5. **Reproduction** of the prediction record on a second machine, byte-identical.
6. **Rehearsal** (about 2 h, all 12 machines): rehearsal-only seeds, with every run kind (stage D, stage N, noisy, U,
   S, duplicate) and blinding. It fixes the machine count and the sizes (§7). Its outcomes count for no claim.
7. **Seed draw**, published.
8. **The campaign**, blinded: per-instance predictions, comparisons and verdicts sealed, with progress counts only.
9. **One analysis**, the frozen script, run once.
10. **Report and PR.**
