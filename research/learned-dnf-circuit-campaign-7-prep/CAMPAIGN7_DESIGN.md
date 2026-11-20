# Design note for a next campaign: the one-port rule alone

**A design note, not a protocol.** Local, not pushed, no run made for it. It prepares the owner's choice of
2026-11-20 ("lever 1 alone"): a preregistered campaign whose only change from campaign 6 is the rule for cell c's
testing error. Nothing here is a claim.

Marks: **[K]** known, from a file named in section 8; **[I]** inferred, my reading.

## 1. The finding that the choice should see first

**With the one-port rule alone, cell c gets room under noise on about one instance in ten, and the claim it was
meant to open (the learned function under noise at c's output) stays out of reach** [K for the batch, I for the
arithmetic].

- On campaign 6's development batch (10 instances, 7 with a prediction), computed with the frozen functions and the
  one change: c has room at K = 3 on **1 instance** (7710), against 0 under the frozen rule. The output of c counts
  for the claim only when a, b and c all have room: **0 instances**, under either rule.
- The reason is simple arithmetic. Under noise, a crossing leaves room only if it sits in the middle 34 % of its
  training step. One number was quoted to the owner, "34 to 42 % of the step": that is per crossing. Cell c has two
  crossings (one per line), and the claim on c's output needs four (the pairs of a and b, and c's two lines):
  0.34 × 0.34 = 12 % for c, and 0.34⁴ = 1.3 % for all three.
- The batch agrees with the arithmetic: 10 of its 28 crossings sit in their window, 36 %.
- So a campaign of campaign 6's size (5 instances) would expect 0.04 instance counting for c's output, where the
  rule asks for 2. It would most likely repeat campaign 6's outcome on that claim: "not established".

Section 7 gives the choices this leaves, and my recommendation.

## 2. The rule change, exactly, and what justifies it

**The change** [K]. In campaign 6, c's testing error is a two-port budget: the noise of both of c's ports added,
at their needs (campaign 5's `predicted.py`, line 278). The new rule: c's testing error is the **one-port** budget,
the larger of its two lines' at their needs, plus the same measure terms H and S:

    testing_c = max over p of [ eps_c + ceil(3 s_cp sqrt(w² + b² + n_p d²)) ] + H_c + S_c      (K = 3)

and likewise at K = 0 with the frozen allowance. Everything else of the budgets is unchanged, c's training error
included (it is already a one-port budget).

**Why the Lean statement allows it** [K]. Campaign 6's gate uses the one-sided theorem. There, the testing error of
a second-layer cell bears only on reads with one line (as a lower bound on that line's score) and on reads with no
line. An observed read with both lines is checked against the threshold and by a comparison of scores, with no
error budget (`MonotoneOneSidedTarget.lean`, lines 24 to 51; the checker, `MonotonePremiseTargets.lean`, lines 101
to 107 and 164 to 170; `Disjunctions.check`, `MonotoneTarget.lean`, lines 59 and 68). So a one-port number is what
the statement constrains. The two-sided theorem would be different: it applies the testing error to every observed
read.

**What the gate says** [K]. On the nominal cell, the frozen generator's file with the one-port number passes
campaign 5's `check.sh` at both budgets (`DOSE_ADDENDUM.md`, section 2). On the batch's 7 predicted instances, the
14 gate files (each rule) compile with the pinned Lean: the kernel agrees with every verdict the Python gives, at
K = 0 and K = 3. This second check is my own compile of the files, not `check.sh`.

**What a protocol must still argue** [I]. The gate shows the number satisfies the statement. It does not show the
number is the right physical budget. The protocol must say why the noise of the port that receives no pulse does
not enter a single-line read of c. In the additive model it does not: only the pulsed port's gain enters the score.
But that is the model. A measure would settle it: the score of a single-line read of c with the other port's stored
voltage moved. Campaign 6's decks read each line with both ports at the same stage; its line scans move one port
only. Neither isolates this.

## 3. What else changes because of it

- **Code** [K]. No frozen file needs editing. `gate4.py` writes c's testing error from the instance's budgets, so
  it takes the new number unchanged. A new frozen file is needed for two things that campaign 5's code fixes: c's
  testing budget, and the room of c's test reads, which `predicted.room` judges with one number. `t1_gate.one_port`
  (development code, about 30 lines) does both as a wrapper; a campaign would freeze its own version, with tests.
- **Verdicts** [K]. Only `room_at_K3["c"]`, and through it the count for c's output, can change. Eligibility
  (K = 0) did not change on the batch: the same 6 instances under either rule.
- **Claims** [K]. One claim is touched: N-out for the output of c. N-own and N-word on c's lines use c's training
  reads, whose budget does not change. The primary claim and the controls do not change.
- **The both-lines read** [I]. Campaign 5's room also asks that the both-lines score exceed the larger single line's
  by the testing error. With the one-port number this is weaker than before; the development code kept the two-port
  number there, outside Lean. A protocol must choose and say which.

## 4. The expected share, on the development batch only

Computed by `c7_share.py` on the batch's own evidence (seeds 7701 to 7710), with the frozen functions and
`t1_gate.one_port`. It stops unless needs, budgets, eligibility and room equal the batch's own record: they do, on
all ten. Campaign 6's counted instances (7801 to 7805) were not read.

| Seed | Needs a, b, c1, c2 | Eligible (K = 0) | Room at K = 3: a | b | c, frozen | c, one port |
|---|---|---|---|---|---|---|
| 7701 | 4, 4, 5, 4 | yes | yes | no | no | no |
| 7702 | 4, 4, 3, 5 | yes | no | no | no | no |
| 7703 | 5, 3, 3, 4 | yes | yes | yes | no | no |
| 7704 | 4, 3, 5, 4 | no | no | no | no | no |
| 7705 | (no prediction: the calendar rule) | no | | | | |
| 7706 | 4, 4, 4, 5 | yes | no | yes | no | no |
| 7707 | (not measured: a deck failed) | no | | | | |
| 7708 | 4, 2, 5, 4 | yes | no | no | no | no |
| 7709 | (no prediction: the code failed) | no | | | | |
| 7710 | 4, 4, 4, 4 | yes | yes | no | no | **yes** |

- **c has room on 1 of 10** (1 of the 7 predicted). **a, b and c together: 0 of 10.** [K]
- Under the one-port rule, what stops c is no longer the test reads but the teaching reads: a line's crossing too
  close to an edge of its step (7701, 7708), or too close to the need (7702, 7703, 7704, 7706). [K]
- Budgets, in stages, on every predicted instance: 0.33 for a pair, 0.33 for a line's training, 0.66 for c's
  frozen testing, 0.33 with one port. [K]
- The arithmetic [I]: a crossing has room when it sits between 0.33 and 0.67 of its step, 34 % of the step. If
  crossings fall evenly in their steps, c has room with probability 0.34² = 0.12 and all three cells with 0.34⁴ =
  0.013. The batch's 28 crossings: 10 in their window (5 of 14 pairs, 5 of 14 lines).
- For comparison, the same arithmetic with twice the dose and the one-port rule (budget 0.164, `DOSE_REPORT.md`
  5.5): 67 % per crossing, 0.45 for c, 0.20 for all three. That is arithmetic on the nominal cell's budgets, not a
  measure on mismatched cells.
- A caution on that figure [I]. At twice the dose a stage is twice the voltage, so the spread of the crossings,
  counted in stages, halves: they may not fall evenly in their steps, and the 0.20 could be far off in either
  direction. The batch's own crossings give a second estimate that does not assume evenness: each divided by the
  dose ratio measured on the nominal cell (2.0065), with the budgets divided likewise, 19 of the 28 crossings fall
  in their window, and c has room on 2 instances of 10 (7703 and 7710), as do all three cells (`c7_rescale.py`).
  This assumes that a
  mismatched cell's crossing moves with the dose as the nominal cell's did (3.355 gives 1.672; 1.674 was measured);
  no mismatched cell was measured at twice the dose.

## 5. The stopping rule's figures, by campaign 6's method

- **k = 6** [K]: the eligible instances of the batch, the same six under the new rule. **I = ceil(30 / 6) = 5.**
- **E = 17 112 s** [K], about 4.8 hours, by `report6.expected_E` with the batch's mean wall times: the same as
  campaign 6, since the runs are the same. The rule's bounds hold (I ≤ 40, E ≤ 28 800 s).
- What 5 instances would be expected to give [I]: 3 eligible; 0.3 to 0.5 with room for c; **0.04 counting for c's
  output**. The chance that at least 2 count, which the claim needs: under 1 in 1 000.
- Larger sizes [K for E]: I = 10 gives E = 28 021 s, the largest size within the bound, and 0.08 expected instance
  counting for c's output. I = 30 gives 74 336 s, beyond the bound.
- **Seeds** [K]. 79xx to 82xx are taken: `main` holds noise identifiers 7901 to 7920, 8001 to 8020, 8101 to 8120
  and 8201 to 8220 (an earlier repetition study). **83xx is free**: no seed, noise seed or instance field with a
  value from 8300 to 8399 or 83 000 to 83 999, and no path named so, on `main` or on the 23 branches I hold. A
  campaign of 5 would take 8301 to 8305, with noise seeds 83 011 to 83 053 by campaign 6's rule.

## 6. What stays as in campaign 6, and what its incidents teach

**Unchanged** [K]: the circuit, the dose, `reltol = 1e-4`, the noise model and decision 5's constants, the measures
(two decks, four scans, the both-lines check, two one-sided sets per instance), the eligibility rule, the network
runs (one without noise with the skew slots, three noisy, one untrained), the claims' wording and minimum of 2
instances, the Lean theory and `check.sh`, the two-machine split, the stage kit, the evidence tooling.

**From the batch's declared items and from this follow-up** [K]:
- A deck can fail to converge (7707) and the prediction code can raise (7709). Both rules exist now: not measured,
  and not eligible. Keep them from the start.
- The report code failed once on runs without a wall time; the evidence end block missed the job logs once. A
  rehearsal of the whole chain, analysis included, on development seeds before the launch.
- Identity: one machine committed under the harness's name until it was seen. Set and check the author before the
  first commit; refuse any hook that asks to re-sign.
- Machines restart when idle, and messages cross. Detached runs, one written state file, and no decision taken on
  a message that may have crossed another.
- A push above 2 GB is refused, and a file above 100 MiB too: one stage and machine per evidence branch, files
  split by the campaign's tool.
- At twice the dose only: `reltol = 1e-4` shifts crossings by 10 to 21 µV. Not this campaign's concern if the dose
  stays.

## 7. Open choices for the owner, and my recommendation

1. **Lever 1 alone, as chosen.** It is the cleanest change, and the gate supports it. But by section 1 it will most
   likely leave c's output "not established" again, for lack of instances that count. It would establish the
   primary claim on fresh instances a second time, and little else new.
2. **Lever 1 with twice the dose.** The arithmetic gives 0.20 for all three cells instead of 0.013, so about 1
   eligible instance in 5; the batch's own crossings, rescaled, give 2 of 10. Either figure could be far off
   (section 4). It needs `reltol = 1e-5`, and it carries what is still open: the growth of `w` on one line of c,
   and no measure yet on a mismatched cell at twice the dose.
3. **A development batch first**, at twice the dose with the one-port rule, on development seeds: measures only,
   as campaign 6's batch was. It would replace the arithmetic of sections 4 and 5 by counts, and give k, I and E
   for a campaign that can reach the claim. No claim, no network run.

**My recommendation: 3, then 2.** Lever 1 alone cannot reach the claim it was chosen for at any size the stopping
rule allows; the owner chose it on a per-crossing figure that I should have turned into a per-instance figure
sooner. A batch at twice the dose is the cheapest way to know whether the combined change gives enough instances,
before any protocol is written.

If the owner keeps choice 1, the protocol should say in its first page that c's output is expected not to count,
with these figures.

## 8. Files, and what was not checked

| File | What | SHA-256 |
|---|---|---|
| `c7_share.py` | section 4 | `2c65ca474e150cf077809e295dcf28befa15563c56a9cfaa55d026c781b6e53d` |
| `c7/C7_SHARE.json` | its output, per instance | `3ed343c78f65562ad5050701ba3d51dec4057f15c5d28ad6ddfd8dc4e1a98af0` |
| `c7/Gate7_<seed>_frozen.lean`, `c7/Gate7_<seed>_oneport.lean` | the 14 gate files, for 7701, 7702, 7703, 7704, 7706, 7708 and 7710 | listed beside them |
| `c7_rescale.py`, `c7/C7_RESCALE_2X.json` | the rescaled estimate of section 4 | `4ac59326…affc`, `3a03d5c2…ad30` |
| `c7/compile_gates.sh`, `c7/COMPILED.txt` | my compile of the 14 files and its results | `131513e2…678d`, `b644c271…988e` |

Not checked:
- The 14 gate files were compiled by my own script (the theory as `check.sh` compiles it, then each file, warnings
  as errors). `check.sh` itself, with its audit of axioms, was not run on them.
- "Crossings fall evenly in their steps" is an assumption; 28 crossings are few to test it.
- The figures at twice the dose in sections 4 and 7 are arithmetic from the nominal cell, and from the batch's
  crossings rescaled by the nominal cell's dose ratio. No mismatched cell was measured at twice the dose, and
  eligibility at twice the dose was not estimated.
- The physical argument of section 2 is not made here, and the measure it suggests was not run.
- The seed search read text files; branches I do not hold were not searched.
- The batch's mean wall times were taken from its report, rounded to 0.01 s; E for I = 5 equals the report's.
