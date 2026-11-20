# Plan for a development batch at twice the dose

**A plan. No run of the batch has been made.** State at 14:50 UTC on 2026-11-20: the smoke of step 0 has run (on
the nominal cell, which is not an instance of the batch); wave 1 has not started. Section 8, the sizing rule, was
added at that time, before wave 1; and the expected times and limits of sections 3 and 4 were raised from the
smoke's timings (the first figures are kept in section 4). Development work: not preregistered, and it counts nothing for any
campaign. It follows the owner's choice of 2026-11-20 ("a batch at twice the dose first"): measures only, no
network run, on development instances, judged with the one-port rule, to count how many instances would have room.

Marks: **[K]** known, from a file or a test named here; **[I]** inferred, my reading.

## 1. The question, and the prediction written before any data

**The question.** On ten mismatched cells at twice the dose, on how many do cells a, b and c all have room under
noise (K = 3) when c's testing error is the one-port budget?

**The prediction** [I], written now, for `k_all3` (section 5):

- **About 2 instances of 10**, by two computations that do not use these instances. Arithmetic: a crossing has
  room in the middle 67 % of its step, and four crossings must all be in (0.67⁴ = 0.20). Campaign 6's own batch,
  rescaled: its 28 crossings divided by the dose ratio of the nominal cell give 2 instances of 10 (`c7_rescale.py`).
- **The caution.** At twice the dose a stage is twice the voltage, so the spread of the crossings counted in stages
  halves. They may then not fall evenly in their steps, and both computations lean on the nominal cell. The count
  could be far off in either direction: anything from 0 to 5 of 10 would not surprise me.
- Under the frozen two-port rule I expect fewer: the window per line of c is 51 % instead of 67 %.
- Needs: mostly 2, some 1 or 3. A need of 1 leaves a single silent stage; it is reported, not excluded.

## 2. The instances

**Ten fresh development seeds, 8301 to 8310** [K for the search]. They are free: no seed, noise seed or instance
field with a value in 83xx or 83 xxx, and no path so named, on `main` or on the 23 branches I hold.

Why not campaign 6's batch (7701 to 7710) again [I]: its stopping rule closed it ("never extended, and no run of
it is ever repeated"); and section 1 already says which of those instances are expected in their window, so their
count would not be blind. The mismatch is drawn as in campaign 6: the same section of the device library, the seed
given to the simulator.

The batch is never extended and no run is started twice.

## 3. The runs

Per instance, the nine measures of campaign 6's batch, by the same frozen functions, with two lines of the deck
rewritten: `vhi=0.7` (twice the dose) and `reltol=1e-5`. Three waves, in the frozen scheduler's order:

| Wave | Runs | Per run: expected, limit | Count |
|---|---|---|---|
| 1 | the guard-on deck and the guard-off deck of each instance | 1 689 s, 3 380 s; 1 161 s, 2 330 s | 20 |
| 2 | the pair scans of a and b; the scans of c's two lines; c's both-lines check. Only if both decks completed and are usable; the doses are those of the instance's own decks | 693 s, 1 390 s; 652 s, 1 310 s; 59 s, 120 s | 50 |
| 3 | the one-sided sets of a and b, at the frozen bound from the instance's two pair scans. Only if both are consistent | 439 s, 880 s | 20 |

- **90 runs** if every run completes. Four at a time. Each wave is launched once, in order; a wave refuses to
  start if the one before has not ended, or if it was started already.
- **Limits**: twice the expected time. The expected time is the mean of campaign 6's batch for that kind of run,
  times a slow-down per kind: 1.4 for pair and line scans; 2.1 and 1.8 for the guard-on and guard-off decks, 1.6
  for the both-lines check and 2.0 for a one-sided set, from the smoke (section 4).
- A run that fails or is cut at its limit stops nothing else. The runs that needed it are not started, and are
  listed. An instance without its measures is "not measured", as in campaign 6.
- No noise source and no noise seed: these are measures.

**Step 0, before the batch: a smoke on the nominal cell** (not an instance): its two decks, then c's both-lines check and
one one-sided set of a, with the same rewrite. No deck and no one-sided set had been run at `1e-5` before it. Expected
about 760, 570, 50 and 230 s; limits at twice. **It ran**, 14:19:20 to 14:43:44 UTC: all four complete, in 1 130, 716,
52 and 324 s; both decks converged; doses 2.707658 mV; needs 2, 2, 2, 2; the one-sided set silent; both lines fired.

## 4. How long

- **The batch** [I, from K figures]: 64 758 s of runs in all. Four at a time, wave by wave: about 7 100 s, 6 900 s
  and 2 200 s, so **4.5 hours at best, about 5 hours expected** on this one machine.
- **The smoke** took 24 minutes.
- What the figure rests on [K]: campaign 6's batch means at `1e-4` and the unchanged dose (804, 645, 495, 465, 37
  and 219 s); a slow-down of 1.3 to 1.4 measured on three pair scans at `1e-5`; and the smoke's four runs against
  the same nominal runs at `1e-4` and the unchanged dose:

  | Kind | Smoke | At `1e-4`, unchanged dose | Ratio | Slow-down used |
  |---|---|---|---|---|
  | guard-on deck | 1 130 s | 540 s | 2.09 | 2.1 |
  | guard-off deck | 716 s | 404 s | 1.77 | 1.8 |
  | both-lines check | 52 s | 32 s | 1.62 | 1.6 |
  | one-sided set | 324 s | 162 s | 2.00 | 2.0 |

- **What changed after the smoke, before any run of the batch** [K]. The first version of this plan used 1.4 for
  every kind: expected and limit 1 126 and 2 260 s (guard-on deck), 903 and 1 810 s (guard-off deck), 52 and 110 s
  (both-lines check), 307 and 620 s (one-sided set); 3.7 hours at best, 4 to 4.5 expected. The smoke showed the
  decks and the one-sided set cost more than that. The limits were raised because a run cut at its limit loses its
  instance for good. The pair and line scans keep 1.4: the smoke ran none.
- What it does not rest on: each ratio is one run, with two runs at a time, not four; no line scan was timed at
  `1e-5`; no mismatched cell was run at twice the dose; campaign 6's means are from two other machines.
- **The machine.** It restarts when the session is idle, and a restart stops the runs. The session's turn is kept
  running through each wave. If a restart happens all the same, the runs then in flight are lost and are reported
  as not complete; nothing is started twice, no state file is edited, and I report to the coordinator before going
  on.

## 5. What the batch reports

Per instance:
- its needs (a, b, c1, c2), and whether question 1 holds (the scan's need equals the deck's first firing stage);
- measured or not, eligible or not (K = 0), under each rule, with the reason when not;
- room at K = 3 for a, for b, and for c under each rule, with the reads that have none;
- each crossing's place in its step (below and above, in stages), the budget in stages, and whether the crossing
  sits in its window;
- its doses.

For the batch, two counts:
- **`k_all3`: the instances where a, b and c all have room at K = 3, under the one-port rule.** It answers the
  question. The same count under the frozen rule is given beside it;
- **`k_elig`: the instances eligible at K = 0**, the count campaign 6's stopping rule uses;
- the crossings in their window, of all crossings;
- each run's status and wall time, and the mean wall time per kind, for a later estimate of a campaign's cost;
- the Lean check of each predicted instance's gate file under each rule (the kernel must agree with every
  verdict), by my own compile of the files, as for the design note.

The batch itself decides nothing and starts nothing. What its count `k_all3` binds is written in section 8.

**Which count would size a campaign is the owner's choice** [I]. Campaign 6 sized itself on `k_elig`: enough
instances to expect 3 eligible ones. That fits a campaign whose main claim is the one without noise. A campaign
meant to reach the claim on c's output under noise needs instances where all three cells have room, so it should
be sized on `k_all3`; with `k_elig` it would again expect too few. **My recommendation: size on `k_all3`, and write
that rule before the batch runs**, so that the count binds and is not chosen after it is seen. If `k_all3` comes
out at 0 or 1 of 10, the same rule should say that no campaign follows on this design. **The owner chose this; the
rule is section 8.**

## 6. The code, and its tests

New files, beside the published ones, which are unchanged. No frozen file is edited.

| File | What | Tests |
|---|---|---|
| `batch2x.py` | the runs: the two decks, the scans, the both-lines check, the one-sided sets of a seed of this batch; the list of runs and limits; the three waves; the smoke | `test_batch2x.py`, 15 tests, no simulation |
| `batch2x_report.py` | section 5, per instance and for the batch; the gate files | `test_batch2x_report.py`, 4 tests, no simulation |

Already reviewed and reused unchanged: `dosedev2.py` (the deck rewrite, the runner), `dosedev_tol.py` (the
tolerance), `t1_gate.py` (the one-port budget and c's room).

**What `batch2x.py` wraps for the time of a call, and nothing else** [K]:
1. the deck's text, as before, now with the two parameters;
2. the frozen seed guard: **a run-time replacement of a frozen guard**, said plainly. Campaign 6's scan code
   refuses any seed but 7701 to 7710. For the time of a scan, `batch6.guard_seed` is replaced by a guard that
   accepts 8301 to 8310 and nothing else, not even the nominal cell, and the frozen guard is put back afterwards.
   Campaign 6's own measure code made the same change for its seeds by copying the scan's entry function with that
   line changed. The coordinator accepted the replacement, as it is how the deck's text is already wrapped. The
   tests that cover it: `Guard.test_this_batch_only`, `Guard.test_the_frozen_guard_is_replaced_for_the_block_only`
   (restored after the block and after an error; the frozen guard still refuses 8301), and the check after every
   test of `FrozenPaths` and `Smoke` that the frozen guard is back.

**What the tests show** [K]:
- the guard accepts this batch's seeds only, and the frozen guard is back after each call and after an error;
- for a seed of the batch, each frozen function hands the simulator the mismatched deck with exactly two lines
  changed, and the seed: both decks and all five kinds of scan;
- the smoke hands the nominal deck with the same two lines changed and no seed, and runs no scan;
- the list holds 90 runs, 9 per seed, with the limits of section 3; an instance without its decks or its pair
  scans gets no later run;
- each wave refuses to start out of order or twice;
- the doses computed from two decks of campaign 6's batch (7701 and 7706) are, string for string, the doses that
  batch's scans were started with;
- the report, run on campaign 6's batch, gives that batch's own record under the frozen rule (needs, budgets,
  eligibility, room), 1 instance with room for c under the one-port rule, none with all three, and 10 crossings of
  28 in their window;
- **the window test is the frozen room** [K]: on all 7 predicted instances of campaign 6's batch, "the pair's
  crossing is in its window" equals the frozen room of a and of b at K = 3, and "both lines in their windows"
  equals c's room under the one-port rule. So the per-crossing arithmetic of section 1 is exact on those
  instances, not only a reading of the checks.

A defect the tests caught before any run, to be listed in the batch's report: the first version took the doses with
a function that only works on the nominal cell's development decks, and would have stopped the batch after wave 1.
It now follows the frozen scheduler (both decks, `predict6.table`, `predict6.doses_V`).

## 7. Not checked, and open points

- No run of the batch has been made. The only run of this code is the smoke (section 3).
- The cost figures of section 4, as said there.
- Whether a mismatched cell's decks converge at twice the dose and `1e-5`. In campaign 6's batch one deck of 20
  failed to converge at the unchanged dose.
- `reltol = 1e-5` is not shown to be converged; only that at `1e-5` two identical cells agree.
- The half bracket of the scans at twice the dose is 1/512 stage on the nominal cell; the frozen prediction
  accepts it. A mismatched cell may give another.
- The report's Lean check is my own compile, not campaign 5's `check.sh` with its audit of axioms.
- Evidence: the batch's 90 run folders would be about 5 GB of waveforms. Whether and how they are published is
  not decided here.

## 8. The sizing rule, written before the batch

**The owner's choice** [K]. Asked by the coordinator whether to write, before the batch at twice the dose runs,
that a campaign 7 is sized on the instances where a, b and c all have room, and that 0 or 1 of 10 means no
campaign on this design, the owner answered **"Oui, écrire cette règle"** on 2026-11-20 at 14:20:26 UTC (read in
the coordinator's transcript). The option's text: the size computed on the instances where a, b and c all have
room, with campaign 6's method; 0 or 1 of 10 = no campaign on this design; written in the plan before the first
wave.

**The rule.**

1. **A campaign 7 on this design is sized on `k_all3`**: the number of this batch's ten instances (seeds 8301 to
   8310) where cells a, b and c all have room at K = 3 under the one-port rule.
2. **By campaign 6's method** (its `STOPPING_RULE.md`, section "The size"): when `k_all3 >= 2`,
   **`I = ceil(30 / k_all3)`** instances, so that 3 instances where all three cells have room are expected.
3. **If `k_all3` is 0 or 1 of 10, no campaign follows on this design.**

**What the words mean here** [I, my reading; to be corrected if the owner meant otherwise].

- "This design": the cells as they are, at twice the dose (`vhi=0.7`), with `reltol=1e-5`, and c's testing error
  taken as the one-port budget.
- `k_all3` is the count `batch2x_report.py` gives (SHA-256 `b6c3ee6a…`, tests `40662542…`), as the file stands
  before wave 1. As in campaign 6's rule: an instance that is not measured, or has no prediction, does not count;
  the batch is never extended and no run is repeated; a defect found in the code after the first run is reported
  and changes neither `k_all3` nor what the rule says.
- The rule gives a size or says "none". It does not start a campaign. A campaign 7 would still need its own
  preregistration, its expected compute (campaign 6's rule also had a compute test, which is not restated here),
  and the owner's go.

**When it was written** [K]. The owner's answer came at 14:20:26 UTC. The smoke ran from 14:19:20 to 14:43:44
UTC, on the nominal cell: it measured no instance and says nothing about `k_all3`. This section was written after
the smoke ended and before wave 1; no run of an instance of the batch exists at this time.
