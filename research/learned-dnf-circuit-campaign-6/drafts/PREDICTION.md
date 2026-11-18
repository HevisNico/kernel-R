# A circuit network that learns (A and B) or (C and D), campaign 6: predictions

**Draft for review, first version**, on the work branch `research/learned-dnf-circuit-campaign-6-wip`. Once both
coordinators have reviewed it and the owner gives his go, this text, byte for byte, becomes
`research/learned-dnf-circuit-campaign-6/PREDICTION.md`. It is then pushed alone on
`research/learned-dnf-circuit-campaign-6`, before any implementation of campaign 6 and before any simulation of a seed
from 7801. Nothing in it may be changed afterwards: a wrong rule is corrected by an amendment file, pushed alone before
the run or the computation it concerns.

**Sources.** Each rule names its source in brackets.

| Tag | Source |
|---|---|
| [SR] | the stopping rule, `STOPPING_RULE.md` (`2e26910`, SHA-256 `773a7811…035d`) |
| [SR-A1] | its amendment 1 (`566f237`, SHA-256 `3e006420…5d6b`) |
| [BR §x] | the development batch's report, `BATCH_REPORT.md` (`5746443`), section x |
| [MU §x] | `drafts/MAPPING_U.md` v3 (`9c7a96e`, SHA-256 `fd7afedf…414f`) |
| [BS] | `drafts/BATCH_SPEC.md` v10 (`b42e9f5`, SHA-256 `553c82ab…6ec5`) |
| [DN rule n] | the design note (`659d3a2`, SHA-256 `e1803c17…a18d`), rule n |
| [C5 §x] | campaign 5's `PREDICTION.md`, as copied verbatim into `research/learned-dnf-circuit-campaign-5/` (the file at `a2d8bad` that the stopping rule cites), section x |
| [new] | a rule this file sets |

---

## In one page

**The goal.** Three simulated SKY130 cells, each with its own manufacturing mismatch, are joined as a small network.
They are trained only by their own pulses, and should learn the function `(A and B) or (C and D)`. Before any network
run, each cell's answers are predicted from measures of that cell alone, and a Lean proof checks that the prediction
implies the learned function. The network runs then test the prediction.

**The per-cell method.** For each cell, the firing threshold of every read the network uses is found by a scan along
the cell's own training path, to 1/256 of a training step. This is campaign 3's method, which handled mismatch. The
scanned thresholds and the measured dose moves give each cell's "need": the number of training pulses after which it
fires. The development batch showed that this predicts training on all 9 instances it could scan.

**The instances.** Five fresh instances, seeds 7801 to 7805, are never extended and never rerun. An instance whose
measures complete, and whose prediction passes the frozen Lean gate, is eligible. Only eligible instances get network
runs. The batch had 6 eligible of 10, so about 3 eligible are expected here.

**The claims.**
- **Primary claim, without noise.** On each eligible instance, the network trains and answers all 16 input patterns
  exactly as predicted.
- **Claims under noise**, under the injected noise model only: per output, and per training port.
- **Controls**: an untrained network and a skewed coincidence.

**What counts.**
- "Established" means the prediction held on every eligible instance, with at least one eligible instance.
- One wrong letter or output refutes the primary claim.
- With no eligible instance, the claim is "not established".
- A claim under noise that has no counted run is "not established".

**Known in advance.** In the batch, cell c (the OR cell) had no room under the noise budget (K = 3) on any instance. So
the claims under noise that involve c will likely have nothing to count, and come out "not established". This is
counted by the rules below, which no result changes.

**The scope.** Simulation only: no silicon, no layout, one noise model. The claims are about the eligible instances,
which are selected by per-cell measures before any network run. They are not about mismatched cells at large.

---

## 1. The instances

- **`I = 5`**, by the stopping rule: `k = 6` eligible of the batch's 10, and `I = ceil(30 / 6)` [SR; BR §1].
- **Seeds 7801 to 7805** [SR]: 7801 to 7803 on machine `a`, 7804 and 7805 on machine `b`. The first `ceil(I / 2)` go
  to `a`, in seed order [SR].
- **Never extended, never rerun.** No seed outside 7801 to 7805 enters the campaign, and no started run is ever
  repeated [SR; C5 §9].
- **A run that does not complete** makes its instance not measured (a measure run) or makes its network claim missing
  (a network run). A run counts only when the launcher recorded it complete and its own record says it reached its
  last date [C5 §9].
- **The model section** is the batch's: mismatch on, the deck of the batch's code [BS].

## 2. The measures

Exactly the batch's measures, by the batch's code at the marker `085c6bc`, unchanged [BS; MU; BR §6]. Per instance,
nine runs:

| Run | What it does |
|---|---|
| guard-on calibration deck | campaign 5's calibration deck, with the guard on |
| guard-off calibration deck | the same deck, with the guard off |
| pair scan of `a` | the threshold of `a`'s pair read |
| pair scan of `b` | the threshold of `b`'s pair read |
| line 1 scan of `c` | the threshold of `c`'s line 1 |
| line 2 scan of `c` | the threshold of `c`'s line 2 |
| both-lines check of `c` | `c`'s both-lines FIRE at s = 0 |
| one-sided set of `a` | each port alone at W + h |
| one-sided set of `b` | each port alone at W + h |

- **The scans** use the ascent step **delta = 1/2**, option C, as chosen by the owner's rule and confirmed on
  2026-11-18 [BATCH_MARKER.json at `085c6bc`]. Each ascends, then bisects to 20 µV, with campaign 3's majority of three
  on disputed states [BS; DN rules 1–2].
- **The mapping** of the scanned thresholds to the gate's scores is `MAPPING_U.md` v3 on the stored-voltage axis, with
  its anchors, its errors `H` and `S = 0`, and its observational decoder [MU §1–3].
- **Measured** has exactly the batch's conditions [BS]:
  - all nine runs complete;
  - every bracket consistent;
  - crossings below 8;
  - every D > 0;
  - question 1;
  - the decoder on every deck read;
  - the both-lines reads;
  - the 20 µV `u(0)` test;
  - the one-sided bounds and their silence;
  - the both-lines check fired.
- **Amendment 1's rule, from the start** [SR-A1]. An instance on which the prediction code raises an error is not
  eligible, and its error is reported. The code that applies it is `predict6_guard.py` (`026919a`, SHA-256
  `368080e7…5664`), unchanged. The report uses `report6_guard.py` (`7fd74ca`, SHA-256 `59a3b480…bc2f`) where a report
  of costs is needed. Under `MAPPING_U.md`, the frozen geometric fit raises whenever a cell's `K − s*` is below about
  half a stage, so this can recur on any seed [SR-A1; BR §5.2].

## 3. Eligibility

Exactly as in the batch [BR §2; MU §5]:

- an instance is **eligible** when it is measured and campaign 5's frozen kernel gate holds under `K = 0`;
- the gate is checked on **its own Lean file**, written by `predict6.gate_each`, through campaign 5's `check.sh`;
- **Lean and the Python mirror must agree**: `gate_K0` is true only when `check.sh` passes on that file and
  `gate4.verdicts` holds at `K = 0`.

The eligible instances, their needs, budgets, room at `K = 3` and learning ports are those of the prediction record,
computed on machine `a` and pushed before any network run. There is no re-scoping afterwards [C5 §9].

## 4. The network runs, on eligible instances only

For each eligible instance, as campaign 5 defines them [C5 §5, §8]:

- **one run without noise**, with the two skew slots, on the calendar of the instance's needs;
- **three noisy runs**, rounds 1 to 3, under the injected model with decision 5's constants: `b = 0.111` mV between
  runs, `w = 0.094` mV within a run, `d = 0.009` mV per dose [C5 §2, §6];
- **one untrained control run** for the campaign, on the first eligible instance in seed order: the 16 test slots
  only, on the preset state, every cell gated [C5 §5; SR].

No network run is made on an instance that is not eligible [DN rule 5]. With no eligible instance, no network run is
made.

**Noise seeds** [C5 §6, the same rule]. The noisy run of round `n` of seed `S` has the noise seed `10 × S + n`: 78 011
to 78 013 for seed 7801, up to 78 051 to 78 053 for seed 7805. The rehearsal (section 7) uses 77 011 for seed 7701 and
77 061 for seed 7706. None of these numbers was ever used to fix the noise of a run. The ranges fixed before were:
- 1 to 707, 201 to 9 920, 706 002 to 706 082 and 900 000 to 900 002;
- 75 011 to 75 123 and 90 951 to 90 953 (campaign 4);
- 76 011 to 76 123, 76 911 to 76 933 and 90 961 (campaign 5).
The batch ran no noisy run [SR].

**Expected costs and limits** [SR; C5 §10.3–10.4]. A run's cost at another calendar is scaled by campaign 5's
`plan.dcost` ratio. The limit is `10 × ceil(2 × expected / 10)`.

| Run | Expected at need 4 | Limit at need 4 | At need 7: expected, limit | Source of the cost |
|---|---|---|---|---|
| without noise, with skew | 718 s | 1 440 s | 903.72 s, 1 810 s | the mean of campaign 5's rehearsal stage RQ, six runs at need 4 on development instance 7692 [SR] |
| noisy, injected model | 1 400 s | 2 800 s | 1 776.06 s, 3 560 s | set on the conservative side by the stopping rule (925 × 734 / 485) [SR] |
| untrained control | 132 s | 270 s | (no calendar) | the mean of RQ's two [SR] |

## 5. The claims and how each is decided

Each claim is the one campaign 5 preregistered, applied to this campaign's eligible instances [C5 §8]. **The verdicts
are separate**, and none changes another.

1. **Primary claim, without noise.** On every eligible instance, in its run without noise:
   - **L1:** each port of `a` and `b` writes `need` letters `s`, then `F`.
   - **L2:** each line of `c` over its teaching slots writes `need_c` letters `s`, then `F`.
   - **T:** on the 16 test patterns, `a` fires exactly on A and B, `b` exactly on C and D, and `c` exactly on
     `(A and B) or (C and D)`.

   It is refuted by one letter or output that differs, on one eligible instance. It is **established** when it holds
   on every eligible instance, with at least one. It is **not established** with no eligible instance, or when the
   run without noise of every eligible instance is missing.
2. **G, read-only**, with its own verdict, as in campaign 5 [C5 §8].
3. **H, hypotheses**: observed and reported, never refuting [C5 §8].
4. **N-out, the learned function under noise, per output** [C5 §8].
   - An output of `a` (`b`) counts when that cell has room at `K = 3`.
   - An output of `c` counts only when `c`, `a` and `b` all have room at `K = 3`.
   - One test pattern answered otherwise, in a counted noisy run, refutes that output's claim.
   - A claim with no counted output-run is **not established**.
5. **N-own and N-word, per port at `K = 3`** [C5 §8].
   - **N-own:** a learning port with own room, in a noisy run where it receives at least `need` pulses, writes exactly
     `need` letters `s`, then only `F`.
   - **N-word:** a learning port with room up to it reads exactly its zero-error word.
   - Each is refuted by one port-run that fails it, and is **not established** without a counted port-run.
6. **Controls** [C5 §8].
   - **U:** in the untrained run, no output fires on any of the 16 patterns.
   - **S:** in the two skew slots, `a` and `b` stay silent.
7. **Declared comparisons, not claims** [C5 §8]: M1 and M3 to M8, as campaign 5 defines them.
   - **M2** (the run without noise of measured instances that are not eligible) **has no data in this campaign**,
     because no network run is made on an instance that is not eligible [DN rule 5]. This is stated now, not
     discovered.

**Cell c at `K = 3`, stated before any data** [BR §2]:
- In the batch, `c` had no room at `K = 3` on any of the 9 instances it could predict. On the nominal cell, its K3
  budgets were 4 603 and 9 145 against `d_c = 13 943` per stage (`4495394`).
- So N-out of `c` will most likely have no counted output-run, and be "not established". N-own and N-word on `c`'s
  lines will most likely count few or no port-runs.
- These outcomes are counted exactly by the rules above. They are reported as what they are, the noise budget of `c`
  under decision 5's constants. No rule, constant or budget is changed after any data.

## 6. Execution, compute and stages

- **Sessions, machines and the environment.** As in campaign 5 [C5 §10.1–10.2]:
  - two cloud machines `a` and `b`, four runs at a time on each;
  - every long run detached;
  - sessions active in loops of at most 5 minutes;
  - `uptime -s` and the inventory recorded at the start and end of every stage;
  - the pinned environment checked by every script.
  
  The CPU model and the kernel are recorded and do not stop a launch, as ruled for the batch [BR §4]. The pinned
  environment, 4 processors, `avx512f` and the SkylakeX OpenBLAS core are checked and do stop it.
- **The stages, in a fixed sequence**, whatever the results [C5 §10.5]. The measures depend on each other: a scan needs
  the guard-on deck's dose, and a one-sided set needs both pair scans of its instance [BS]. So they are three stages:

  | Stage | Runs |
  |---|---|
  | M1 | the 10 calibration decks |
  | M2 | the 20 scans and the 5 both-lines checks |
  | M3 | the 10 one-sided sets |
  | Q | the runs without noise of the eligible instances, and the untrained run |
  | N1, N2, N3 | the noisy runs of rounds 1, 2 and 3 |

  Each stage is split by seed only if it does not fit the kit's bound of 14 400 s [C5 §10.5].
- **Measure limits** are twice the batch's means [SR], under `10 × ceil(2e / 10)`:

  | Run | Limit |
  |---|---|
  | guard-on deck | 1 610 s |
  | guard-off deck | 1 300 s |
  | pair scan | 990 s |
  | line scan | 940 s |
  | both-lines check | 80 s |
  | one-sided set | 440 s |

  The batch's slowest run of each kind used at most 0.59 of these limits [`RUNS.json`, `0248a644`].
- **Expected compute.** Measured by campaign 5's rule, `Σ (sum / 4 + ¾ max)` over stages and machines, with the batch's
  means [BR §1]:

  | Case | Expected compute |
  |---|---|
  | The stopping rule's figure: the measures costed as one stage, the network on 3 eligible instances | **17 112.13 s** [BR §1] |
  | This file's stages (M1 3 018.3 s, M2 3 188.9 s, M3 877.7 s; Q and N on 3 eligible instances) | **18 183.4 s** |
  | Worst case, all 5 instances eligible | **20 642.4 s** |
  | Rehearsal (section 7), outside the campaign | 3 192 s |
  | Worst case plus rehearsal | 23 834 s |

  Every figure is below 28 800 s. Each stage fits the kit's bound: the largest is the worst case's N stage, at
  9 132.5 s.

## 7. The rehearsal, before any launch

The design note requires a rehearsal under real conditions before any launch [DN rule 7]. Its proposed minimum
[new]:

- **What it exercises.** The network side of the frozen implementation. The batch has already run the measures under
  the campaign's conditions, with the same code and machines, four at a time [BR §4].
- **The instances.** Two eligible development instances, **7701 on machine `a`** and **7706 on machine `b`**. They use
  their collected measures and their pushed predictions [`0bd3b60`], and no measure is rerun. No campaign seed enters
  the rehearsal.
- **The runs**, through the launch kit:
  - on each instance, its run without noise with skew, at its own needs;
  - on each instance, **one noisy run** of round 1, with noise seeds 77 011 and 77 061. This is the first noisy run
    ever made on a mismatched cell;
  - on 7701, the untrained control run.
- **The cost.** 3 192 s expected over both machines. The limits are those of section 4.
- **The 0.75 rule** [C5 §11.4]. If any rehearsal run uses more than 0.75 of its campaign limit, or does not complete,
  nothing is launched until an amendment.
- **Also checked:**
  - the seed guard's refusals: a campaign seed outside the kit, and a development seed in a campaign stage;
  - the noise-model guard;
  - the collection;
  - the prediction record reproduced byte for byte from the evidence;
  - the analysis run end to end on the rehearsal's runs. Its verdicts are discarded, and none is a claim.

## 8. The code to freeze

- **Reused unchanged:**
  - campaign 5's 66 frozen files, except its workflow;
  - the batch's code at `085c6bc` (`batch6.py`, `scan6.py`, `predict6.py`, `report6.py`, `schedule6.py`,
    `check7692.py`);
  - `predict6_guard.py` at `026919a` and `report6_guard.py` at `7fd74ca`;
  - the launch kit (`launch.py`);
  - campaign 5's `collect.py`.
- **New, written only after this file is pushed**, then reviewed by both coordinators:
  - a seed guard for 7801 to 7805 and the rehearsal's seeds. `batch6.SEEDS` accepts only 7701 to 7710, so a campaign
    module must name the campaign's seeds without editing the batch's files;
  - the stage manifests of M1 to M3, Q and N1 to N3, for the launch kit;
  - a network runner that calls campaign 5's frozen network branches of `run4` (run without noise, noisy, untrained)
    under the new seed guard and noise seeds;
  - the prediction record for the network: `PREDICTED.json` from `predict6_guard`'s instances, with the needs and
    learning ports the network runner and campaign 5's `analyze.py` read.
- **Not yet checked:** whether campaign 5's `analyze.py` reads `predict6_guard`'s instance records unchanged. If it
  does not, the adapter is new code and is declared at the freeze.
- **The marker.** It names the frozen commit and every imported file's SHA-256, as the batch's marker did. It is pushed
  alone, and every runner checks it before any simulation.
- **CI** on the frozen commit:
  - `test_batch`, `test_guard` and `test_report_guard`;
  - the new code's tests;
  - campaign 5's `check.sh` on both of M8's paths;
  - the reproduction of this file's expected compute to 0.01 s.

## 9. Rules of the analysis

As in campaign 5 [C5 §9]:

- **One analysis**, at the end, frozen with the implementation.
- **No word, output or score of any network run is looked at before the last stage has ended on both machines.**
  Between stages, only each run's status is checked.
- The analysis first checks that the prediction record is exactly what the frozen code gives from the evidence. If it
  is not, every claim is "not established".
- This campaign is reported on its own, with nothing pooled with campaigns 1 to 5 or the batch.

## 10. Order

1. This file, pushed alone.
2. The new code, reviewed, frozen, with CI green, and its marker pushed alone.
3. The rehearsal (section 7) and its record.
4. M1, M2, M3.
5. The prediction record and the Lean gate, pushed before any network run.
6. Q, N1, N2, N3: only if at least one instance is eligible.
7. The one analysis, then `REPORT.md`.

## 11. What this campaign cannot show

- Nothing about silicon, a layout, wires between cells or a real router.
- Nothing about any noise but the injected model with decision 5's constants.
- Nothing about any function but `(A and B) or (C and D)`, or about more than three cells and four inputs.
- Nothing about cells that are not eligible: the claims are about instances selected by per-cell measures before any
  network run [DN rule 6].
- Nothing about outputs or ports without room. With cell c at `K = 3` as the batch found it, that likely covers every
  claim under noise that involves `c`.
- Nothing outside 27 C and the typical corner with mismatch.
- The per-cell measures and the network runs use the same simulator and the same deck. The claim is that the network
  does what its cells, measured alone, say it will [C5 §13].
