# Campaign plan for Wednesday: DRAFT

**Draft for the owner's review: no simulation, nothing frozen, nothing preregistered.**
- Numbers come from the 2x development runs: DESIGN_POINT_REPORT.md (9801, 9802), XOR3_REPORT.md (9803),
  YIELD_CHECK_2X.md, and the inverter lot 2 (C5, 60/60).
- Marks: [K] measured; [I] inferred; [G] an estimate.

## 1. The three groups and their functions

| Group | Function (spec) | Circuit | Why this one |
|---|---|---|---|
| 1. NOT in one layer | **NOT1** (`specs/not1.json`): y = ¬x | 1 inverter + 1 copy cell | the smallest network with a front end. Proved end to end at 2x on 9801 at K0 and K3, through `layered_recognition_at` and `layered_inverters_chained` |
| 2. Layers without NOT | **ANDOR3** (`specs/andor3.json`): 3 layers, both/copy → either → copy | 4 R cells, no inverter | every R gate type over 3 layers. 9802 measured 3 of 4 cells eligible at 2x (c1_0 not measured, crossing at its stop) |
| 3. Layers with NOT | **XOR3** (`specs/xor3.json`): y = x0 ⊕ x1 | 2 inverters (C5) + 4 R cells over 3 layers | the classic function a monotone cascade cannot do without its rails. Proved at K0 on 9803 through `layered_inverters_chained` |

- **One function per group.** The claims are about instances (mismatch draws) of a fixed design, and these three are
  the only specs validated through the whole chain [K].
- Adding functions (for example NAND2 or ¬x0∧x1 in group 1) is possible only if each passes the dry run before the
  freeze (step 9). Otherwise it waits for a later campaign.

## 2. Two levels, the draws, the expected counts

- **Level K0.** A K0 prediction on every eligible instance.
- **Level K3.** A K3 prediction on the subset with room.
- **Per-cell rates at 2x** [K/I, YIELD_CHECK_2X.md]:

  | Cell or gate | K0 | K3 |
  |---|---|---|
  | any cell | ≈ 0.97 | — |
  | both | — | 0.72 |
  | copy at layer 1 | — | 0.81 |
  | copy at layer ≥ 2 | — | 0.81 |
  | either (max rule) | — | ≈ 0.35 |
  | inverter (C5) | 60/60, Wilson ≥ 0.94 | 60/60, Wilson ≥ 0.94 |

  On top of these, a "not measured" class (crossing at the stop) of about 0.4 % per group [I].
- Instance rates assume independence. Intervals are 90 % binomial and widened for the rate uncertainty [G].

| Group | N drawn | p(eligible K0) | expected eligible (90 %) | p(room K3) | expected with room (90 %) |
|---|---|---|---|---|---|
| NOT1 | **60** | 0.97 | 58 (55–60) | 0.79 | 47 (40–53) |
| ANDOR3 | **72** | 0.90 | 65 (59–69) | 0.17 | 12 (6–19) |
| XOR3 | **84** | 0.88 | 74 (68–79) | 0.15 | 13 (6–19) |

- The sizes are set so that each 3-layer group expects **about 12 instances with room**, and the K0 level has more
  than 60 instances per group.
- The K3 counts are the weak point. The either cell's 0.35 comes from one instance that failed by 266 units (9803 c2_0).

## 3. Budget

- **Machines.** 12 machines × 4 cores × 5.5 h = **264 core-hours**. Plus a **rehearsal** of about 2 h on the same
  machines, budgeted separately: about 96 core-hours, of which about 40 are used.
- **Cost per attempt** without solo scans (D4 bounded by `d4_stage` 0.005) [K]:
  - NOT1 4.4 CPU-min;
  - ANDOR3 59.6;
  - XOR3 80.1.
- **The D4 audit.** Every 6th instance per group, in seed order, also runs the solo scans: +0.6, +45, +30 min.
- **Jobs.** One per core, and a job's CPU equals its wall time [K]. The longest job (XOR3 with solo, about 110 min)
  fits 3 times in the window.

| Group | Runs | Core-hours |
|---|---|---|
| NOT1 | 60 × 4.4 min (+10 audits) | 4.5 |
| ANDOR3 | 72 × 59.6 (+12 × 45) | 80.5 |
| XOR3 | 84 × 80.1 (+14 × 30) | 119.1 |
| **Total** | | **≈ 204** |

- **Compute ceiling: 240 core-hours** (91 % of the window). That leaves about 18 % for slower machines and the
  scheduler.
- **Cut order if the ceiling binds.** Jobs are launched in published seed order, interleaved across groups. When the
  ceiling is reached:
  1. no new D4 audits;
  2. no new XOR3 instances past the 60th;
  3. no new ANDOR3 instances past the 50th.
- NOT1 is never cut. An instance not started is reported as "not run" with its seed, not as a failure, and never
  replaced.

## 4. Seeds and the freeze

- **Fresh seeds** by a published draw after the freeze: SHA-256 of a public randomness-beacon value at a round fixed
  in the freeze commit, mapped to integers. The draw script is frozen too.
- **Excluded**: every dev seed used anywhere: 8301–8310, 8501–8515, 9711–9770, 9801–9803, the dry-run seeds and the
  rehearsal seeds. The script asserts the exclusion.
- **Frozen, with sha256 in the freeze commit:**
  - **code**: this package at its tag, the Lean library, ngspice 42 with its pinned binary, SKY130 at 1232782c;
  - **gates**: the fit, budget and cell-valid rules, `CircuitInverterGate`, and the inverter instance gate;
  - **configs**: `config.json`, `calibration.json` (including `d4_stage` 0.005 and the scan cap 64),
    `config_inverter_c5.json`, the specs;
  - **the design point**: vhi 0.7, reltol 1e-5, junction areas.

## 5. Per claim: predicted, observed, failure rule

| | Predicted before any network run | Premise observed afterwards | Conclusion |
|---|---|---|---|
| K0 claim (each eligible instance) | the function, the cascade, the design timing, the budget rules (K0 error = P's read budget + H + H_drift + H_D4), and the eligible-count interval of §2 | training calibration; read calibration at every pattern; cell validity at K0 (eligibility); for groups 1 and 3, the front, chain dates, scheduled, latencies, realised | the kernel's recognition theorem: trained, and output = f at every pattern |
| K3 claim (each instance with room) | the same at K3, and the room-count interval | the same clauses at K3 | the same theorem at K3 |
| Rates | the intervals of §2 | the counts | in or out of the interval, reported either way |

- **Failure rule.** An instance whose observed premise fails is **counted and reported** under the first failing
  clause, with the kernel's and the mirror's values. It is **never dropped and never re-run**.
  - A "not measured" cell (question-1 rule, scan failure) is reported as such.
  - A kernel–mirror disagreement is reported as a defect of the chain, not of the instance.

## 6. Open premises, and how PREDICTION.md states them

Each one is listed as **assumed, not proved**. The claim's wording is reduced to "computes f, under the premises
below".

| Premise | Statement |
|---|---|
| Leak along the trajectory | the stored-voltage leak is taken as measured in the scans (H_drift), a modelling step [I] |
| The measured real hypotheses | the simulator's values, dates and crossings are the simulation's claims, not facts about silicon |
| The latch | its delay is measured (the inverter lot: 0.00099–0.00105 tu), not bounded |
| The routed walk | the router's 0.4 µs grid and its launch rule are as implemented; `Checker.routed` is checked per trace, but the router has no soundness proof |
| D4 | parallel against solo bounded by `d4_stage` 0.005 stage (largest seen 0.00405 over 11 groups), audited on every 6th instance |

## 7. Expectations stated in advance

- **The inverter-fed outputs and the either cells will be noisy.**
  - The either cell carries the max-rule test budget, about 0.33 stage at K3. Its K3 room is about 0.35.
  - The inverter-fed reads add the front's timing to the chain.
- K3 results are therefore expected to be sparse and to vary across groups.
- **The injected noise is the pessimistic model.** The K3 budget uses the 3σ noise term of DECISION5. **To settle
  before the freeze:** whether K3 runs inject noise, and how, through this package's noise path. That path is not yet
  exercised in development.

## 8. Known small limits carried into the report

- **Shared stimulus in ANDOR3**: cells read stimuli from shared sources, so their inputs are correlated by design.
- **The ngspice convergence line**: the known convergence message, to be counted per run and reported.
- **The router grid**: emission dates are snapped to 0.02 tu.
- **The max step**: 200 ns in the network, against 5/20 ns in the inverter's characterisation. No effect was seen on
  9803 (XOR3_REPORT.md).

## 9. Steps, in order

1. **Full dry run of the whole chain BEFORE the freeze.**
   - On the campaign machines: one NOT1, one ANDOR3 and one XOR3 on new dev seeds (for example 9804–9806).
   - It covers job launch, the seed script, the noise path (§7), the kernel checks, the aggregation and the
     report generator.
   - Every fix found here lands before the freeze.
2. **Freeze**: a tag, and a commit of the hashes of §4.
3. **CI rerun at the tag**: all tests (deck identity, inverter C5 identity, scans, fit, Lean checks).
4. **Prediction record**: PREDICTION.md (§2, §5, §6, the cut order, the analysis script's hash), committed.
5. **Reproduced on a second machine**: the record and its derived numbers are regenerated, byte-identical.
6. **Seed draw**: published (§4).
7. **Rehearsal** (about 2 h): a short batch on rehearsal-only seeds, through the full pipeline including blinding.
   Rehearsal outcomes are excluded from the claims.
8. **The campaign**: blinded. Per-instance verdicts are written sealed. Only progress counts are visible until the
   last job ends or the ceiling is reached.
9. **One analysis**: the frozen script, run once.
10. **Report and PR.**
