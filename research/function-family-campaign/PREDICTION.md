# A family of five functions on the trained AND-OR circuit, campaign (a): predictions

**DRAFT for the owner's review. Not pushed, not frozen.** When accepted, this file is the family campaign's
preregistration: `research/function-family-campaign/PREDICTION.md`. It is pushed alone on
`research/function-family-campaign`, with the owner's go, before any campaign code is frozen and before any
simulation of a seed from 8501. Nothing in it may be changed afterwards: a wrong rule is corrected by an amendment
file, pushed alone before the run or computation it concerns.

**Sources.** Each rule names its source in brackets.

| Tag | Source |
|---|---|
| [FD §x] | `research/function-family/FAMILY_DESIGN.md` v6 (SHA-256 `83e47d4f…a8b6`), section x |
| [TR §x] | `research/function-family/TOPUP_RULES.md` (`5d6ba264`, SHA-256 `d8242c6c…d96f`), section x |
| [MP §x] | `research/function-family/MACHINE_PLAN.md` (`5d6ba264`), section x |
| [FZ] | the frozen prediction code and its tests, `research/function-family/dev/` at `f2b3904c` (`PREDICT_FREEZE.txt`, SHA-256 `13ad8abb…f509`) |
| [TV] | the top-up's verdict, `research/function-family/topup-verdict/` at `0c003fbf` (`OUTPUT_SHA256SUMS` `bd6125e2…c9d`) |
| [C6 §x] | campaign 6's `PREDICTION.md` (`research/learned-dnf-circuit-campaign-6/`, at `ecfcd1c1`), section x |
| [C5 §x] | campaign 5's `PREDICTION.md`, section x, as campaign 6 cites it |
| [new] | a rule this file sets |

---

## In one page

**The goal.** Three simulated SKY130 cells, each with its own manufacturing mismatch, are joined as a small two-layer
network: two first-layer cells a and b, and one second-layer cell c. Each cell is trained only by its own pulses.
Five monotone functions of at most three inputs are studied, one per instance: X1 = A, X2 = A∧B, F4 = A∨B,
F2 = A∧(B∨C) and F3 = A∨(B∧C) [FD §0.1]. For each instance, the cells' answers are **predicted in advance** from
measures of each cell alone. Lean's kernel then **proves** that the prediction implies the function's truth table
at c. The network runs then test the prediction.

**The new element.** A one-input term is a **unary cell**: one port of a first-layer cell at amplitude 1.0
[FD §2.5]. Its port, 1 or 2, is chosen per instance from that cell's own measures, by a rule fixed before the
top-up [TR §1].

**The instances.** Fifteen fresh instances, seeds 8501 to 8515, three per member, assigned by a published draw.
They are never extended and never rerun (section 1).
- The size comes from the pre-B2 rule, applied per member on B2's ten instances and the top-up: `r_m` = 7, 6, 3, 2, 2
  for X1, X2, F4, F2, F3. No member is removed, so `I = ceil(30 / 2) = 15` [TR §2; TV].

**What is predicted, and what is not.**
- **An instance is eligible** for a member when it is measured and its gate holds at K = 0, by the kernel (section 3).
  On an eligible instance, the run without noise is **predicted** to train and to answer every pattern as the gate
  says. A difference refutes.
- **A cell has room** when the gate holds at K = 3 (TOPUP_RULES' sufficient condition). Where every cell of the
  instance has room, its noisy runs are **predicted** to answer every pattern under the noise model, and a failure
  refutes.
- **Without eligibility, or without room, there is no prediction.** K = 0 and K = 3 are sufficient conditions, not
  verdicts of failure. Any run made outside them is reported as observed, plainly, and counts for no claim.

**What counts.**
- A claim is judged on the counted runs of the instances it covers. A missing run is reported, and never counted as
  a pass.
- **A claim is established for a member** with at least 2 counted instances of that member, and for the family with
  at least 2 counted instances on each member kept [FD §0.5]. One wrong letter or output on a counted instance
  refutes it.

**Known in advance** [TV]. On B2's ten instances, the room shares were X1 0.7, X2 0.6, F4 0.3, F2 0.2 and F3 0.2.
With three instances per member, F4's, F2's and F3's noise lines are expected to read "held on one instance" or
"not established" (section 5).

**The scope.** Simulation only: no silicon, no layout, one noise model. The claims are about the instances, and the
ports, selected by per-cell measures before any network run, not about mismatched cells at large.

---

## 1. The instances

- **`I = 15`**, by TOPUP_RULES §2 on the top-up's verdict [TR §2; TV]:
  - `r_m` = X1 7, X2 6, F4 3, F2 2, F3 2;
  - no member has `r_m ≤ 1`, so all five are kept;
  - `I = ceil(30 / 2) = 15`, which is a multiple of 5.
- **Seeds 8501 to 8515** [FD §4; new].
  - On `main` at the time of writing, no `.py`, `.md` or `.yml` file names a seed from 8501 to 8515. The only match
    is the number 0.8505 in `research/sky130-layout/phase1/J_REPORT.md`.
  - No five-digit number from 85 011 to 85 153 appears either (the noise seeds of section 4).
  - Branches other than `main` were not searched.
- **The draw** [FD §4]: balanced, three per member.
  - The seeds are sorted by `SHA-256("kernel-R family draw 1|" + str(seed))`.
  - Members are assigned in the declared order X1, X2, F4, F2, F3, repeated.
  - The draw's only inputs are the seed list and the salt. It uses no measure, since none exists.
  - Computed for this draft:

  | Member | Seeds |
  |---|---|
  | X1 | 8501, 8504, 8512 |
  | X2 | 8502, 8508, 8513 |
  | F4 | 8505, 8507, 8514 |
  | F2 | 8506, 8510, 8515 |
  | F3 | 8503, 8509, 8511 |

  `DRAW.json`, `FAMILY.json` (each member's cascade, wiring and truth table) and `draw.py` go in this file's commit,
  with their SHA-256 [FD §4].
- **Never extended, never rerun.** No other seed enters the campaign, and no started run is repeated [C6 §1].
- **A run that does not complete** makes its instance not measured (a measure run), or its network claim missing (a
  network run). A run counts only when its launcher recorded it complete and its record says it reached its last
  date [C6 §1].
- **The design point** is B2's: twice the dose (`vhi = 0.7`), `reltol = 1e-5`, through `dosedev2.window` and
  `dosedev_tol.tolerance`, unchanged [FD §2.1; TR].

## 2. The measures

**The frozen code reads exactly the runs it read on B2 and the top-up** [FZ; TR §3.5.1]. Per instance, the runs of
its member:

| Member | Runs | Expected (s) |
|---|---|---|
| X1 | 2 decks, c line-1 scan; 2 unary decks, unary scans of a's ports 1 and 2, preset check of a; 2 pair scans (for K) | 9 645 |
| X2 | 2 decks, pair scan of a, one-sided set of a, c line-1 scan; pair scan of b (for K) | 5 346 |
| F4 | 2 decks, c line scans 1 and 2, both-lines check; 2 unary decks, 4 unary scans, 2 preset checks; 2 pair scans (for K) | 11 622 |
| F2 | B2's 9: 2 decks, 2 pair scans, 2 one-sided sets, 2 line scans, both-lines check | 6 476 |
| F3 | 2 decks, pair scan of b, one-sided set of b, 2 line scans, both-lines check; 2 unary decks, unary scans of a's ports 1 and 2, preset check of a; pair scan of a (for K) | 10 775 |

The expected times are the measured means at the design point:
- B2's runs: guard-on deck 1 662, guard-off 1 206, pair scan 701, line scan 600, both-lines check 54, one-sided
  set 476 s [K, `BATCH2X_REPORT.json`];
- the top-up's runs: guard-on unary deck 2 076, guard-off 1 376, unary scan 634, preset check 55 s [K, the three
  machines' `STATE.json`, 10, 10, 40 and 20 runs].

- **Every member measures both pair scans** [new; decided, O1]. TOPUP_RULES §3.5.2 takes layer 1's K from both pair
  scans "for every member", with K = 8 only when neither is consistent. The sizing verdict used both [TV]. So the
  campaign measures them on every instance, and the mapping is the one that sized it. This adds 701 to 1 402 s for
  X1, X2, F4 and F3. Decided on 2026-11-22 (O1).
- **The unary members run two pairs of decks** [FZ]. The frozen code reads the pair cells' and c's reads from the
  plain decks (`<seed>-cal-on`, `-cal-off`) and the unary reads from the unary decks (`<seed>-cal-on-unary`,
  `-cal-off-unary`). Reading everything from the unary deck would change frozen code, which this campaign does not
  do (decided, O2).
- **The unary port** of each unary cell is chosen by TOPUP_RULES §1, from that cell's two unary scans and its preset
  check only, before any network run. The frozen code applies it [TR §1; FZ].
- **The mapping, the checks, the budgets and the observation** are TOPUP_RULES §3.5, as frozen in
  `family_predict.py` (SHA-256 `00b6a516…`), with its implementation readings (a) to (g) [TR §3.5; FZ].
- **Measured.** Exactly the conditions of TOPUP_RULES §3.5.7: every run the member uses complete, scans consistent,
  doses positive, `u(0)` within 20 µV, question 1, the one-sided sets and preset checks, the decoder, and c's
  both-lines reads.

## 3. Eligibility and room

- **The gate.** For each instance, `family_predict.py` (frozen, unchanged) writes the member's generator spec and its
  Lean file. The generator's `gencheck.sh` checks it: campaign 5's `check.sh` steps 1 and 3, with forbidden tokens,
  warnings as errors and the axiom audit [TR §3; FZ reading (f)].
- **The kernel's verdict is the last word.** The mirror's verdict is reported beside it, and any disagreement is a
  defect of the mirror [TR §3.3].
- **Eligible**: measured, and the kernel's `checks` holds at K = 0.
- **Room**: the kernel's `checks` holds at K = 3. That is c with the one-port testing error, and every first-layer
  cell [TR §3.5.6].
- The prediction record (`PREDICTED.json`) is computed on one machine and pushed **before any network run**. It holds
  every instance's ports, needs, budgets, Lean verdicts and observation. There is no re-scoping afterwards [C6 §3].

## 4. The network runs

On each eligible instance [C6 §4; FD §8.4, choice B]:
- **one run without noise**, with the skew slots (one per pair term; a unary term has none), on its calendar;
- **three noisy runs**, rounds 1 to 3, **only on instances where every cell has room at K = 3** (decided, O6).
  They run under the injected model with decision 5's constants (section 6);
- **one untrained control run per member**, on that member's first eligible instance in seed order: its `2^M` test
  slots only, on the preset state, every cell gated [FD §5.2; new, decided (O5): campaign 6 had one per campaign].

No network run is made on an instance that is not eligible [C6 §4]. A member with no eligible instance has no
network run.

**The calendar is bound to the prediction** [FZ readings (b) and (c)]. The network code reproduces the dates of
`family_predict.observation`:
- layer 1: `max(need) + 3` slots, on the union of the terms, every first-layer cell writing;
- layer 2: `max(need_c) + 3` rounds, each with one slot per line in the order a then b, only c writing;
- the tests, in the order of `family_predict.patterns` (first input least significant);
- every slot 22 units apart.

In a teaching slot, the first-layer cell not being taught reads the taught term's inputs wired to it (F2's partial
read). It is predicted silent by its structure, and the prediction gives it no emission. The network code's tests
check this binding before it is frozen (section 8).

**Noise seeds** [C6 §4, same rule]. The noisy run of round `n` of seed `S` has noise seed `10 × S + n`: 85 011 to
85 013 for 8501, up to 85 151 to 85 153 for 8515. The rehearsal's noise seeds are given in section 7.

**Expected costs and limits** [FD §8; new]. The run without noise and the noisy run take the draft's F1 estimates at
the design point: 689 to 1 292 s and 1 179 to 2 676 s. These have never been measured at `1e-5`. They are scaled by
each member's slot factor against F1: X1 0.37, X2 0.47, F4 0.59, F2 0.76, F3 0.73 [FD §0.6, a guess]. The limits are
set from the rehearsal's measured costs, by the rule `10 × ceil(2 × expected / 10)` [C6 §4], in an amendment pushed
before the first network stage.

## 5. The claims and how each is decided

Each claim keeps campaign 6's definition [C6 §5], applied per member, with its own ports and its `2^M` patterns.
**The verdicts are separate**, and none changes another.

1. **Primary claim, without noise.** On every counted eligible instance of member f, in its run without noise:
   - **L1:** every learning port of layer 1 writes `need` letters `s`, then `F`;
   - **L2:** every selected line of c writes `need_c` letters `s`, then `F`;
   - **T:** on the `2^M` test patterns, each first-layer cell fires exactly on the patterns containing its term, and
     c fires exactly on f's truth table.

   The letters and outputs are those predicted in advance from per-cell measures, and proved by the kernel through
   `two_layer_monotone_recognition_one_sided` in that instance's Lean gate.
   - **Refuted** by one letter or output that differs, on one counted instance of any member.
   - **Per member**: "established for f" with at least 2 counted instances; "held on one instance of f, not
     established" with 1; "not established for f" with 0.
   - **For the family**: established when it holds on every counted instance, with at least 2 counted instances on
     each of the five members. Otherwise it is worded on the members that reached 2, and never as "for every
     function of the family".
2. **G, read-only**, with its own verdict, as in campaign 6. That includes F2's partial teaching reads, which are
   read-only for the cell not taught [C6 §5; FD §3.3].
3. **H, hypotheses**: observed and reported, never refuting [C6 §5].
4. **N-out, per output, under noise.** An output of a first-layer cell counts where that cell has room at K = 3. An
   output of c counts only where c and every first-layer cell have room.
   - Refuted by one pattern answered otherwise, in a counted noisy run.
   - Established, pooled, with counted runs from at least **N_N = 2 instances, from at least 2 members**; each member
     is reported [FD §0.5].
   - With fewer, the wording is "held on one instance, not established" or "not established".
5. **N-own and N-word, per port at K = 3**: as in campaign 6, with the same minimum N_N [C6 §5].
6. **Controls.** **U**: in each member's untrained run, no output fires on any pattern. **S**: in each skew slot, the
   pair cell stays silent [C6 §5].
7. **Declared comparisons, not claims**: comparisons M1 and M3 to M8, as campaign 6 names them, reported per
   member. **Comparison M2 has no data**, since no network run is made on an instance that is not eligible. (These
   names are campaign 6's; they are not machines or stages.)

**Outside eligibility or room, there is no prediction** [TR §3]. K = 0 and K = 3 are sufficient conditions. An
instance or output outside them carries no prediction, and is never called "predicted to fail". If a run is made
there (for example, an output without room inside a noisy run of an instance that has room elsewhere), its outcome is
reported as observed, plainly, with the reason it is outside, and it counts for no claim.

**Expected outcomes, stated before any data** [TV, the top-up's room shares; I]:
- At three instances per member, the expected number with every cell's room is about 2.1 for X1, 1.8 for X2, 0.9 for
  F4, 0.6 for F2 and 0.6 for F3.
- So the pooled N-out of c is likely to reach N_N = 2 through X1 and X2.
- F4, F2 and F3 are likely to read "held on one instance" or "not established".
- These are counted by the rules above, which no result changes.

## 6. Noise, the environment and the duplicate

- **Decision 5's constants, unchanged**: `b = 0.111` mV between runs, `w = 0.094` mV within a run, `d = 0.009` mV per
  dose [C6 §4]. The rehearsal's sensitivity reading measures `b`, `w` and `d` by campaign 3's definition. That counts
  nothing and changes no verdict: the verdicts are taken under decision 5's constants (section 7) [FD §8.3].
- **The numpy RECORD pin, amended** [TR §0; new]. The pinned venv's RECORD SHA-256 (`064003bd…`) cannot be rebuilt,
  because its RECORD file was never published. The pin becomes:
  - numpy 2.3.5, installed from the official wheel `numpy-2.3.5-cp312-cp312-manylinux_2_27_x86_64.manylinux_2_28_x86_64.whl`,
    SHA-256 `0d8163f43acde9a73c2a33605353a4f1bc4798745a8b1d73183b28e5b435ae28`;
  - in a venv outside the pinned path;
  - its installed RECORD equal to the wheel's RECORD, entry for entry (900 of 900), apart from the 4 installer lines
    (`INSTALLER`, `REQUESTED` and the two bin scripts);
  - every file on disk matching its RECORD hash.

  `dev/envcheck.py` checks this on every machine before any run, with Python 3.12.3, ngspice 42 and the device library
  at `1232782c` to their pinned hashes. A machine that fails runs nothing [MP §3].
- **The duplicate, with its criterion fixed** [MP §2; new].
  - **One duplicate**: M5, the lightest machine, reruns M1's guard-on unary deck of 8501 (`8501-cal-on-unary`)
    after its own decks, as `DUP/8501-cal-on-unary-dup`. Its result is not used by any prediction. No other machine
    runs a duplicate.
  - The two are compared with `topup.py compare`'s fields: `input_spice`, `record`, `result`, `noise_sha256` and
    `trace_raw`. **`trace.raw` is compared with its `Date:` header line excluded.**
  - **Why.** In the top-up, M1's and M3's runs of 8301's guard-on unary deck were equal in every field except
    `trace_raw`. The two `trace.raw` files, 182 933 244 bytes each, differed only in ngspice's `Date:` header line
    (09:46:52 against 11:17:25). With that line removed, both had SHA-256 `d6195367…` [TV `NOTES.txt`].
  - The top-up's criterion was not met to the letter, and its cause was found. This campaign fixes the criterion
    before any run, instead of rewriting the old one.

## 7. Execution, stages, budget and the rehearsal

- **Machines** [MP; new: six, by the owner's decision]: six cloud machines, M1 to M6, with the same paths and
  worktrees.
  - The instances are split in seed order, 3, 3, 3, 2, 2, 2:

  | Machine | Instances (member) | Measure runs, expected (s) |
  |---|---|---|
  | M1 | 8501 (X1), 8502 (X2), 8503 (F3) | 25 766 |
  | M2 | 8504 (X1), 8505 (F4), 8506 (F2) | 27 743 |
  | M3 | 8507 (F4), 8508 (X2), 8509 (F3) | 27 743 |
  | M4 | 8510 (F2), 8511 (F3) | 17 251 |
  | M5 | 8512 (X1), 8513 (X2) | 14 991 |
  | M6 | 8514 (F4), 8515 (F2) | 18 098 |

  - Seed order, not cost, decides the split, so that no measure chose it. The heaviest machine carries 1.85 times the
    lightest. M5 also runs the duplicate (section 6).
  - Each instance's network runs are made on the machine that measured it. A run's deck depends on its seed, its
    needs and its noise seed, not on the machine; only its wall time does [C6 §4].
  - Four runs at a time; every long run detached; sessions kept active.
  - `uptime -s`, `nproc`, `free` and `df` recorded at the start and end of every stage, on every machine.
- **Stages, in a fixed sequence, whatever the results** [C6 §6]:
  - **stage D**: the decks;
  - **stage S**: the scans, both-lines checks and preset checks, which need the decks' doses;
  - **stage O**: the one-sided sets, which need both pair scans;
  - then the prediction record and the gate, pushed;
  - then Q (the runs without noise and the untrained runs);
  - then N1, N2, N3.
- **Measure limits**: `10 × ceil(2 × mean / 10)` over the means of section 2. B2's slowest run used 0.57 of its
  limit, and the top-up's 0.60.
- **The budget, expected compute E** (E taken as 0.38 × run time for measures and 0.65 × for network runs [FD §8]):
  - measures: 131 592 s of runs, E about 50 000 s;
  - network runs: 15 without noise; noisy runs on about 6 instances with room, × 3 rounds; 5 untrained. That is about
    17 300 to 36 600 s of runs, E about 11 300 to 23 800 s;
  - **total E about 61 000 to 74 000 s, within the accepted bound of about 74 000 s of E** (decided, O3). The
    rehearsal sets the network limits by an amendment before any network stage. Six machines change the wall time,
    not the run time; E as defined here is not recomputed per stage and machine (not checked).
- **Expected wall time, on six machines** [I, from section 2's means, four runs at a time]:
  - stage D (decks): about 4 500 s on machines M2 and M3, the heaviest;
  - stage S (scans and checks): about 3 500 s;
  - stage O (one-sided sets): about 500 to 1 000 s;
  - the prediction record and the Lean gates: about 1 hour, computed on one machine;
  - Q and N1 to N3: about 1 to 2.5 hours, from the network estimates of section 4, which are guesses;
  - **in all, about 4.5 to 6 hours of wall time**, against about 7 to 9 hours on three machines [I].
- **The duplicate's added cost**: one guard-on unary deck on M5, about 2 076 s of runs, inside M5's stage D. With
  it, M5 carries about 17 070 s, still below M2 and M3.
- **The rehearsal, before any launch** [FD §8.3]. No campaign seed enters it.
  - **R-M**: the nominal cell through the campaign's measure stages, on each machine. That includes the unary decks,
    scans and preset checks.
  - **R-N**, on the top-up's instances 8303 and 8306, which have room for all five members [TV]:
    - one run without noise of each member;
    - the owner's **noise sensitivity reading**: 8 noisy runs of **F2**, 4 on 8303 and 4 on 8306. They measure `b`,
      `w` and `d` by campaign 3's definition, and the values are fixed before any noisy campaign stage. A declared
      comparison after comparison M8 says, per counted instance, whether it keeps room with the larger of each pair of
      constants. It counts nothing [FD §0.6, §8.3];
    - one noisy run each of X1, X2, F4 and F3;
    - one untrained run per member.

    The rehearsal's noise seeds are `10 × S + n`, n numbering that instance's noisy rehearsal runs [new]:
    - on 8303: F2 rounds 1 to 4, seeds 83 031 to 83 034; X1, 83 035; X2, 83 036;
    - on 8306: F2 rounds 1 to 4, seeds 83 061 to 83 064; F4, 83 065; F3, 83 066.

    83 031 to 83 068 were searched on 2026-11-22 on `main` (`14cc793a`), `research/learned-dnf-circuit-campaign-7-prep`
    (`b956efe4`) and `evidence/learned-dnf-circuit-campaign-7-prep` (`85199862`), each fetched by name. None is used
    as a seed: every textual match is a digit run inside a hash, a byte count or a decimal, and no match follows a
    `seed` key (decided, O4).
  - **The 0.75 rule.** If a rehearsal run uses more than 0.75 of its campaign limit, or does not complete, nothing is
    launched until an amendment. That amendment may change only limits and the stage split [C6 §7].
  - It must also show: each member's prediction record reproduced byte for byte; G on F2's partial teaching reads; a
    unary cell trained in a network run; the network costs that set the limits; and the analysis run end to end, with
    its verdicts discarded.
- **Evidence** [MP §4]. Each machine pushes its RUNS folder to its own branch `evidence/function-family-campaign-Mn`,
  n = 1 to 6, under the owner's identity:
  - files over 90 000 000 bytes split into `.part-000` and onwards;
  - `SHA256SUMS` over the unsplit files, and `PARTS.txt`;
  - the analysis machine fetches each branch by name, joins the parts, and checks every file before reading it. A file
    that does not match is reported, and its instance is not used.

## 8. The code to freeze

- **Reused unchanged**:
  - the frozen prediction code `family_predict.py` (`00b6a516…`), with its tests [FZ];
  - campaign 5's and 6's frozen files;
  - the generator (`research/learned-dnf-generator` at `4fca6256`);
  - `topup.py`'s deck and scan wrappers (`5d6ba264`);
  - `dosedev2`, `dosedev_tol` and `batch2x.PARAMS`;
  - Lean 4.35.0 (archive SHA-256 `7289597a…`).
- **The network-run code: a draft exists from before this file** [new]. At the owner's request, it was written on
  the local branch `research/function-family-campaign-net` (commit `fc18d516…`): `family_net.py` (`f625a56a…`) and
  `test_family_net.py` (`e62803e8…`), with 16 tests passing and no simulation. It was written without any campaign
  data, since none exists, and it reads none.
  - It is reviewed, completed and frozen by SHA-256 **only after this file is pushed**, with its freeze marker pushed
    alone.
  - Completing it includes: the seed guard for 8501–8515 and the rehearsal's seeds; the family noise-seed rule of
    sections 4 and 7; stage handling; and its draft's open points, which are the runner without a stage file, the record
    key, the untested injected-noise path, the accepted range of needs, and the per-cell binding check.
  - It must keep F1 reproducing `plans4.network` exactly, and pass the binding test against
    `family_predict.observation`.
- **New, written only after this file is pushed**, reviewed, then frozen by SHA-256 with a marker pushed alone:
  - a campaign wrapper that calls `family_predict.one_seed` on the campaign's seeds. The frozen `main` loops over B2's
    seeds only, and is not changed;
  - the stage manifests, the duplicate check with its new criterion, and the analysis adapter, with per-member
    reports and the family verdicts of section 5.
- **CI** on the frozen commit: the frozen tests, the new code's tests, and `gencheck.sh` on the synthetic gates of
  every member.

## 9. Rules of the analysis

As in campaign 6 [C6 §9]:
- **one analysis**, at the end, frozen with the implementation;
- no word, output or score of any network run is looked at before the last stage has ended on every machine;
- the analysis first checks that the prediction record is exactly what the frozen code gives from the evidence. If it
  is not, every claim is "not established";
- this campaign is reported on its own, pooled with nothing.

## 10. Order

1. This file, pushed alone, with `DRAW.json`, `FAMILY.json` and `draw.py`.
2. The network code's draft reviewed and completed, and the rest of the new code written; all of it frozen with CI
   green, and its marker pushed alone.
3. The rehearsal and its record; an amendment for the network limits.
4. Stages D, S and O, and the duplicate.
5. The prediction record and the Lean gates, pushed before any network run.
6. Q, N1, N2, N3, only on eligible instances, and N only where every cell has room.
7. The one analysis, then `REPORT.md`.

## 11. What this campaign cannot show

- Nothing about silicon, a layout, physical fan-out (F2's shared input is two ideal per-port sources [FD §2.3]) or a
  real router.
- Nothing about any noise but the injected model with decision 5's constants.
- Nothing about functions outside the five, about three-input functions that need more than two layers (A∧B∧C, A∨B∨C,
  majority: step 2), or about more than three cells.
- Nothing about instances that are not eligible, or outputs without room: there is no prediction there.
- Nothing outside 27 °C and the typical corner with mismatch.
- The per-cell measures and the network runs use the same simulator and the same deck. The claim is that the network
  does what its cells, measured alone, were predicted in advance to make it do, as proved by the kernel.

## Decided choices (2026-11-22)

Decided by the owner, as relayed by the coordinator on 2026-11-22. They are written into the text above.

- **O1.** Both pair scans are measured on every instance, so that the mapping is the one that sized the campaign
  (section 2).
- **O2.** The unary members keep two pairs of decks, since the frozen code reads the plain and the unary decks
  (section 2).
- **O3.** The compute bound is about 74 000 s of E. The rehearsal sets the network limits by an amendment before any
  network stage (section 7).
- **O4.** The rehearsal's noise seeds are fixed, and were searched (section 7).
- **O5.** One untrained run per member (section 4).
- **O6.** Noisy runs only on instances where every cell has room at K = 3 (section 4).
- **Six machines**, M1 to M6, split in seed order, with one duplicate on M5 (sections 6 and 7).

## Not checked

- The network costs at the design point: never measured, and the slot factors are guesses [FD §0.6].
- The network-run code exists only as a draft (section 8). This file's author has not reviewed it, and its binding to
  the prediction's calendar is a test it must still pass when completed. Its injected-noise path is untested.
- Seeds 8501–8515 and noise seeds 85 011–85 153 were searched on `main` only.
- The rehearsal's noise seeds were searched on three branches only (section 7), not on every branch.
- The draw table was computed in this session with Python's `hashlib`. `draw.py` does not exist yet.
- The expected outcomes of section 5 use B2's room shares, from ten instances, as rates.
- The per-stage kit bounds were not computed. The wall times of section 7 are estimates from mean run times, four at
  a time, not a schedule.
- Whether six machines are available with the same environment: not checked here. Each runs `envcheck.py` before
  any run, and a machine that fails runs nothing.
- That the untrained run of a member with a unary cell starts from a state where the unary port is silent is
  inferred from the preset checks, not shown.
