# A circuit network that learns (A and B) or (C and D), campaign 7: draft of the protocol

**A draft, local, not a preregistration.** Nothing in it has been run, pushed or frozen. It is a skeleton in the
structure of campaign 6's `PREDICTION.md`, written on 2026-11-20 in about 90 minutes, to be completed and reviewed
before anything is pushed. No campaign seed has been simulated.

Marks: **[K]** known, from a file or a run named here; **[I]** inferred, my reading; **[OPEN n]** a choice that is
the owner's, listed in section 12 with my recommendation.

Sources: campaign 6's `PREDICTION.md` [C6] and `STOPPING_RULE.md` [SR], on `main`; its code, on
`research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1`; `DOSE_REPORT.md` and
`DOSE_ADDENDUM.md`, on `research/learned-dnf-circuit-campaign-6-followup` at `56f9e83e`; and three local files:
`CAMPAIGN7_DESIGN.md` (`db6fd415…`), `BATCH2X_PLAN.md` (`573270f9…`) and the batch's report
`BATCH2X_REPORT.json` (`d29bdf1c…`) [B2].

## What the owner has decided, and when

All on 2026-11-20, read in the coordinator's transcript [K]:

| Time (UTC) | Decision |
|---|---|
| 11:12 | "Levier 1 seul": c's testing error is the one-port budget; no other change of rule |
| 13:48 | a development batch at twice the dose first, measures only |
| 14:20 | "Oui, écrire cette règle": a campaign 7 is sized on `k_all3` by campaign 6's method; 0 or 1 of 10 means no campaign on this design |
| 20:04 | keep the noise constants as they are ("ok pr les constantes de bruit"); prepare the campaign for one or two hours at most, then pause and resume the next day; "on tentera 6 machines" |

**Not decided** [K]: the compute bound. Campaign 6's own bound, `E <= 28 800 s`, **would refuse 15 instances**: the
measures alone are 42 989 s by its function (section 6). The owner was told so at 19:58 and answered by asking for
more machines, then by "on prépare la campagne". This draft writes a bound as a proposal [OPEN 1].

## In one page

**The goal.** As campaign 6: three simulated SKY130 cells, each with its own mismatch, joined as a small network,
trained only by their own pulses, should learn `(A and B) or (C and D)`. Each cell's answers are predicted from
measures of that cell alone; a Lean proof checks that the prediction implies the learned function; the network runs
test the prediction. **The target of this campaign is the claim campaign 6 could not count: the output of cell c
under noise (N-out of c).**

**What changes from campaign 6** [K for the facts, each in a published file]:
1. **Twice the dose** (`vhi = 0.7` in the deck; 2.708 mV per pulse on the nominal cell against 1.349 mV).
2. **`reltol = 1e-5`** instead of `1e-4`. At `1e-4` and twice the dose two identical cells differed by 32 µV; at
   `1e-5` they agree.
3. **The one-port rule**: c's testing error is the largest one-port budget of its two lines, not the two-port
   budget. The one-sided theorem asks the testing error only on reads of a single line or of none.
4. **The noise constants are decision 5's, unchanged**: `b = 0.111` mV, `w = 0.094` mV, `d = 0.009` mV.
5. **Six machines** instead of two.

**The instances.** Fifteen fresh instances, seeds 8401 to 8415, never extended, never rerun.

**What is expected, written before any data** [I from B2]:
- eligible without noise: all or nearly all (10 of 10 in the batch);
- with room for a, b and c at `K = 3`: about 3 of 15 (2 of 10 in the batch). The rate is poorly known: 2 of 10
  gives a 95 % interval of about 3 % to 56 %. At a rate of 0.2 the chance of at least 2 such instances is 0.83; at
  0.1 it is 0.45; the chance of none is 0.035 and 0.21.
- So **N-out of c most likely has 1 to 5 instances to count, and "not established" for lack of instances stays a
  real outcome** (about 1 chance in 6 at the batch's rate).

**Known in advance, and not in the campaign's favour** [K, `DOSE_REPORT.md` section on G6]. On the nominal cell at
twice the dose, eight noisy runs gave a within-run scatter 1.47 times decision 5's `w` in millivolts, and a
between-run scatter 1.16 times its `b`. The budgets of this campaign use decision 5's constants, as the owner
chose. A counted output that fails under noise refutes its claim; that can happen on an instance whose crossing
sits near the edge of its window.

**The scope.** Simulation only; one noise model; the claims are about instances selected by per-cell measures
before any network run.

---

## 1. The instances

- **`I = 15`** [K]: `k_all3 = 2` of the batch's 10 (instances 8303 and 8306), and `I = ceil(30 / 2)`, by section 8 of
  `BATCH2X_PLAN.md`. Lean's kernel agrees with every verdict behind that count (20 gate files, my own compile).
- **Seeds 8401 to 8415** [K for the search]. Free: no seed, noise seed or instance field with a value from 8400 to
  8499 or 84 000 to 84 999, and no path so named, on `main` or on the 23 other branches I hold. The only text match
  is a memory figure ("394.84375" MB) beside an instance field. 83xx is not used: 8301 to 8310 are the batch's
  development instances.
- **Never extended, never rerun** [C6 §1]. A run that does not complete makes its instance not measured (a measure)
  or its network claim missing (a network run).
- **The model section**: mismatch on, the batch's deck, with the two rewritten lines (section 2).

## 2. The measures

Exactly the batch's nine measures per instance [B2; C6 §2]: the guard-on and guard-off calibration decks, the pair
scans of a and b, the scans of c's two lines, c's both-lines check, the one-sided sets of a and b. By campaign 6's
frozen functions, with the deck rewritten on two lines: `vhi=0.7` and `reltol=1e-5`.

- "Measured" has campaign 6's conditions, unchanged [C6 §2].
- Amendment 1's rule from the start: an instance on which the prediction code raises is not eligible [C6 §2].
- The rewrite, and the seed guard, must become frozen campaign code (section 8). In the batch they were development
  wrappers applied at run time.

## 3. Eligibility

As campaign 6 [C6 §3], with the one-port rule:

- an instance is **eligible** when it is measured and the kernel gate holds under `K = 0`;
- the gate is checked on its own Lean file through campaign 5's `check.sh`, and Lean and the Python mirror must
  agree;
- the budgets handed to the gate are the frozen ones, except c's testing error, which is the one-port budget.

In the batch the one-port rule changed no verdict at `K = 0` (10 of 10 under both rules) [K].

`check.sh` takes about 11 minutes per gate file on one machine [K, campaign 6's follow-up]: about 2.75 hours for 15
instances if run on one machine, less if each machine checks its own. Not a simulation; not in `E` [OPEN 6].

## 4. The network runs

Per instance, campaign 5's runs [C6 §4], at twice the dose and `1e-5`:
- one run without noise, with the two skew slots, on the calendar of the instance's needs;
- three noisy runs, rounds 1 to 3, under the injected model with decision 5's constants;
- one untrained control run for the campaign, on the first eligible instance in seed order.

**Which instances get them** [OPEN 2]. Campaign 6 ran them on every eligible instance. Here nearly all 15 are
expected eligible, and a noisy run is the costliest run. Three choices, with `E` in section 6:
- **A**: every eligible instance gets all four runs (campaign 6's rule);
- **B (my recommendation)**: every eligible instance gets its run without noise; **the noisy runs are made only on
  instances where a, b and c all have room at `K = 3`**. The primary claim is judged on all eligible instances;
  every claim under noise is judged on the instances with room for all three;
- **C**: all four runs only on instances with room for all three.

Under B and C the claims under noise about a and b alone lose the instances where only they have room (in the
batch, 5 of 10 had room for a and b, 2 of 10 for all three). This is stated now, before any data.

**Noise seeds**: campaign 5's rule, `10 × S + n` for round `n` of seed `S`: 84 011 to 84 153 [K: free, same search].

## 5. The claims and how each is decided

Each claim is campaign 6's, word for word [C6 §5], with these points:

1. **Primary claim, without noise** (L1, L2, T): established when it holds on every counted eligible instance,
   **with at least 2 counted instances**; "held on one instance, not established" with 1; "not established" with 0;
   refuted by one wrong letter or output.
2. **G** and **H**: as campaign 6.
3. **N-out, per output, under noise. The target is the output of c.**
   - an output of a (b) counts when that cell has room at `K = 3`;
   - **an output of c counts only when c, a and b all have room at `K = 3`, c's room being judged with the one-port
     testing error**;
   - one test pattern answered otherwise in a counted noisy run refutes that output's claim;
   - the minimum of 2 instances applies: counted runs from at least 2 eligible instances, else "held on one
     instance, not established" (1) or "not established" (0).
4. **N-own and N-word**, per port at `K = 3`: as campaign 6, same minimum.
5. **Controls** U and S: as campaign 6.
6. **Declared comparisons** M1, M3 to M8: as campaign 6; M2 has no data.

The verdicts are separate, and none changes another. No rule, constant or budget is changed after any data.

## 6. Execution, compute and stages

**Six machines as three pairs** [I, my proposal; OPEN 3]. The launch kit refuses a stage without runs on both of
two machines, and campaign 6's stage code and tools name machines `a` and `b` in several places (`stages6.py`, `c6.py`, `diskcheck.py`). The smallest change that
keeps the kit unchanged: **three independent pairs, each running campaign 6's layout for 5 instances**.

| Pair | Machines | Seeds | On the first machine | On the second |
|---|---|---|---|---|
| 1 | a1, b1 | 8401 to 8405 | 8401 to 8403 | 8404, 8405 |
| 2 | a2, b2 | 8406 to 8410 | 8406 to 8408 | 8409, 8410 |
| 3 | a3, b3 | 8411 to 8415 | 8411 to 8413 | 8414, 8415 |

- Stages per pair, in campaign 6's fixed sequence: M1 (the decks), M2 (the scans and the both-lines checks), M3 (the
  one-sided sets), then the prediction record and the Lean gate, then Q and N1 to N3 with the two-shard rule.
- **No network run of any pair starts before the prediction record of all 15 instances is pushed**, and no word or
  output of any network run is looked at before the last stage of the last pair has ended (section 9).
- Four runs at a time on each machine; every long run detached; the session's turn kept running; `uptime -s` and
  the inventory at the start and end of every stage.

**Expected costs of a run** [K for the measures, I for the network]:

| Run | Expected | Limit (twice) | Source |
|---|---|---|---|
| guard-on deck | 1 662 s | 3 330 s | the batch's mean of 10 |
| guard-off deck | 1 206 s | 2 420 s | the batch's mean of 10 |
| pair scan | 701 s | 1 410 s | the batch's mean of 20 |
| line scan | 600 s | 1 200 s | the batch's mean of 20 |
| both-lines check | 54 s | 110 s | the batch's mean of 10 |
| one-sided set | 476 s | 960 s | the batch's mean of 20 |
| run without noise | 689 to 1 292 s | to be set by the rehearsal | 492 s (nominal cell, twice the dose, `1e-4`) × 1.4 to 2.1 for `1e-5`, × 1.25 for mismatch at the high end |
| noisy run | 1 179 to 2 676 s | to be set by the rehearsal | 842 s (mean of eight, same conditions) × 1.4 to 2.1, × 1.51 for mismatch at the high end |
| untrained run | 185 to 277 s | to be set by the rehearsal | campaign 6's 132 s × 1.4 to 2.1 |

In the batch the slowest run of each kind used at most 0.57 of these measure limits (decks 1 694 and 1 238 s, pair
768 s, line 668 s, one-sided 500 s) [K]. **No network run exists at `1e-5`, and none on a mismatched cell at twice
the dose**: the three network costs are estimates until the rehearsal (section 7).

**Expected compute `E`**, by campaign 5's rule, the sum over stages and machines of `sum / 4 + 3/4 max` [I: my
arithmetic, to be reproduced by the frozen code]:

| Part | E |
|---|---|
| Measures of one pair: M1 6 078 s, M2 4 372 s, M3 1 906 s | 12 357 s |
| **Measures of the three pairs** | **37 070 s** |
| Network, choice A (all 15 eligible, every run) | 34 900 to 77 000 s |
| Network, choice B (15 runs without noise; noisy runs on 3 instances, one per pair) | 13 700 to 28 800 s |
| Network, choice B if 6 instances have room | 26 900 to 58 900 s |
| **Total, choice A** | **72 000 to 114 000 s** |
| **Total, choice B, 3 instances with room** | **50 800 to 65 900 s** |
| Total, choice B, 6 instances with room | 64 000 to 96 000 s |

- For comparison, campaign 6's own function with the measures of each instance as its own stage gives 42 989 s for
  the measures of 15 instances; the staged plan above gives 37 070 s for the same runs.
- **Wall clock** with six machines in parallel: the busiest machine (3 instances) has about 7 000 s of measures and
  2 500 to 5 300 s of network under choice B, so **about 2.6 to 3.4 hours of runs**, plus the gate, the pushes and
  the waits between stages.
- The largest kit bound of a measure stage is M1's, 13 864 s for a pair, under the kit's 14 400 s [I].

**The compute bound, A PROPOSAL TO CONFIRM, not decided** [OPEN 1]: **`E <= 72 000 s`, summed over the six machines
(20 hours of machine time)**, for the campaign's stages, with the network counted on the expected 3 instances with
room. Plainly:
- campaign 6's bound of 28 800 s would refuse this campaign: its measures alone exceed it;
- under choice B the proposal holds at every estimate above (50 800 to 65 900 s);
- under choice A it holds only at the lowest estimate (72 000 s) and fails at the others;
- the bound is tested once, after the rehearsal has measured the network costs and before any campaign run. If `E`
  then exceeds it, nothing is launched without the owner.

## 7. The rehearsal, before any launch

Required by campaign 6's design rule 7, and here it also makes the first measurement of the network costs.

- **R-M, the measures through the kit, on the nominal cell**: one nominal instance on each machine of a pair, through
  the real M1, M2, M3 manifests. About 2 700 s per machine [I, from the smoke]. On one pair or on all three [OPEN 4].
- **R-N, the network runs, on development instances 8303 and 8306** (the batch's two instances with room for all
  three), with their collected measures and no measure rerun: on each, its run without noise and one noisy run of
  round 1 (noise seeds 83 031 and 83 061); on 8303, the untrained run. About 4 000 to 6 100 s over two machines [I].
  These are the first network runs at `1e-5`, and the first on a mismatched cell at twice the dose.
- **The 0.75 rule**, as campaign 6: a rehearsal run over 0.75 of its limit, or not complete, stops the launch until
  an amendment that may change only limits and the stage split.
- **The network limits are set from R-N**, by a rule written in the preregistration before R-N runs [OPEN 5].
- Also checked: the seed guard's refusals, the noise-model guard, the collection, the prediction record reproduced
  byte for byte, the analysis run end to end with its verdicts discarded.

## 8. The code to freeze

Section 13 gives the list with sizes. In short: campaign 5's and campaign 6's frozen files reused unchanged; new
campaign code for the two deck parameters, the seed guard, the one-port rule, the stages for three pairs, the
network runner, the prediction record, the analysis adapter, the report, and the publication per stage and
machine. All written after the preregistration is pushed, reviewed, frozen under a marker, with CI green.

## 9. Rules of the analysis

As campaign 6 [C6 §9]: one analysis, at the end, frozen with the implementation; no word, output or score of any
network run looked at before the last stage has ended on all six machines; the prediction record first checked
against the evidence, and every claim "not established" if it differs; the campaign reported on its own, nothing
pooled with the batch or with earlier campaigns.

## 10. Order

1. The owner's choices of section 12.
2. The preregistration, completed from this draft, reviewed, pushed alone.
3. The new code, reviewed, frozen, CI green, its marker pushed alone.
4. The rehearsal and its record; the network limits; the test of the compute bound.
5. M1, M2, M3 on the three pairs.
6. The prediction record and the Lean gate of the 15 instances, pushed before any network run.
7. Q, N1, N2, N3.
8. The one analysis, then `REPORT.md`.

## 11. What this campaign cannot show

- Campaign 6's list [C6 §11], unchanged: nothing about silicon, a layout, another noise model, another function, or
  cells that are not eligible.
- Nothing at the unchanged dose, and nothing about the frozen two-port rule: the claims under noise about c are
  made under the one-port rule.
- Nothing about noise larger than decision 5's constants. The nominal cell at twice the dose showed more scatter
  than they say; the campaign tests the claims under the injected model, not that model.
- `reltol = 1e-5` is not shown to be converged.
- With about 3 instances expected to count for c's output, a "held" would rest on few instances, and the minimum of
  2 may not be reached.

## 12. Open choices for the owner, each with my recommendation

1. **The compute bound.** Proposal: `E <= 72 000 s` summed over machines, network counted on 3 instances with room,
   tested once after the rehearsal. *Recommendation: confirm it together with choice 2-B; with choice 2-A a bound
   near 115 000 s would be needed.*
2. **Which instances get network runs** (A, B or C of section 4). *Recommendation: B.* It keeps the primary claim
   on every eligible instance and spends the noisy runs where the target claim can count.
3. **Six machines as three pairs with the unchanged kit**, or a new six-shard kit. *Recommendation: three pairs.*
   Less new code, and each pair is campaign 6's layout, which ran. Cost: three sets of stages to launch and watch.
4. **R-M on one pair or on all six machines.** *Recommendation: all six*, about 16 000 s of machine time in all: a
   machine that has never run the kit is the likeliest place for a first failure. Counted outside the bound.
5. **The rule that sets the network limits from R-N.** *Recommendation*: expected = R-N's time of that kind of run
   (the larger of the two instances); limit = twice; written before R-N runs.
6. **`check.sh` for the 15 gate files**: on one machine (2.75 hours) or each pair on its own first machine (under
   an hour). *Recommendation: each pair on its own.*
7. **Whether the rehearsal's cost is inside the bound.** Campaign 6 kept "worst case plus rehearsal" under its
   bound. *Recommendation: state the rehearsal separately, at most 28 800 s.*
8. **Publication of the batch before the campaign.** The preregistration cites the batch's count, so its report,
   plan, code and manifests should be on a branch before the preregistration is pushed; the 6 GB of waveforms
   separately, on the evidence branch, or not at all. *Recommendation: publish the small files now, before the
   pause (a few megabytes); decide on the waveforms tomorrow.* An idle container may be reclaimed overnight.

## 13. The code list, to freeze before any campaign run

Sizes are rough, by comparison with campaign 6's files of the same role (its `campaign6/` is 1 271 lines of code
and 704 of tests; its `tools/` 563 and 542) [I].

| Item | What | Starts from | Rough size, code + tests |
|---|---|---|---|
| The two deck parameters | the deck rewritten for `vhi=0.7` and `reltol=1e-5`, for measures and for network decks, as frozen code with its own refusals | `dosedev2.py`, `dosedev_tol.py` (development, published) | 150 + 200 lines |
| The seed guard | 8401 to 8415, the rehearsal's seeds, the pair and machine of each; refuses campaign 6's and the batch's seeds | `campaign6/c6.py` (181 lines), `batch2x.guard_seed` | 200 + 150 |
| The one-port rule | c's testing error as the one-port budget; c's room; the gate file per instance | `t1_gate.one_port`, `batch2x_report.one_instance` (development) | 120 + 200 |
| The measures and inputs | campaign 6's measure runner under the new guard and parameters | `meas6.py` (148), `inputs6.py` (108) | 280 + 200 |
| The stages for three pairs | manifests of M1 to M3, Q, N1 to N3 per pair; the two-shard rule; expected compute to 0.01 s; choice B's run list | `stages6.py` (356) | 450 + 300 |
| The network runner | campaign 5's network branches at twice the dose and `1e-5`, under the guard and the noise seeds | `net6.py` (82), `dosedev2.window` | 120 + 150 |
| The prediction record | `PREDICTED.json` for 15 instances, with room under the one-port rule and the run list | `predicted6.py` (166) | 200 + 150 |
| The analysis adapter | campaign 6's adapter, with c's count under the one-port rule and the minimum of 2 | `analyze6.py` (230) | 260 + 250 |
| The report | costs, `E`, the claims' table | `report6.py` (175), `batch2x_report.py` | 200 + 100 |
| Publication per stage and machine | the evidence of each stage of each machine on its branch; six machine names where the tools accept `a` or `b` | `tools/publish_evidence.py` (193), `diskcheck.py`, `marker_check.py` | 150 + 150 |
| The marker and CI | the frozen commit, every file's SHA-256; the tests; `check.sh` | campaign 6's marker and workflow | 100 |

About 2 200 lines of code and 1 850 of tests. I have no measured figure for how long campaign 6's equivalent took
to write and review. Each of the six machines also needs the pinned environment installed and checked before the
rehearsal.

## 14. Not checked

- Every `E` above is my arithmetic with campaign 5's formula, not the output of frozen code; the network costs are
  estimates from the nominal cell at `1e-4`.
- Whether the launch kit, unchanged, accepts three pairs run side by side (names of branches, of manifests, of
  evidence). I read where the code names two machines; I ran nothing.
- Whether six cloud machines can be had, and whether they are as fast as this one. The batch ran on one machine.
- Whether campaign 5's network branches accept the deck rewrite as the development wrapper applied it in steps C
  and D; those ran on the nominal cell only.
- The seed search covers `main` and the 23 other branches I hold, not branches I do not hold.
- The claims' text is cited from campaign 6, not restated in full; the preregistration must restate it.
- I have not re-read this draft against campaign 6's `PREDICTION.md` line by line.
