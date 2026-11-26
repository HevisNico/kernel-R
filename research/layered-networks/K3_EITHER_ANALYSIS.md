# Can the either cell get K3 room without a redesign? (analysis, no simulation)

**Development, nothing preregistered.** Sources: the stage-D fits of 9802 and 9803
(`dev/stage_d_andor3/fit_d.json`, `dev/stage_d_xor3/fit_d.json`), YIELD_CHECK_2X.md (the family's rates), and the
Lean library `research/learned-coincidence/LayeredMonotoneTarget.lean`.

Marks: [K] read in a named file; [I] inferred; [G] an estimate.

The family top-up and campaign (a) evidence were **not re-read here**. Their either-cell rates are taken from
YIELD_CHECK_2X.md, which was computed from them. Per-cell budget terms exist only for the two stage-D either cells.

## 1. What makes the either cell fail at K3

Two either cells have stage-D fits [K].

| Instance | Failing K3 clause | Training margin (stop margin vs trainError) | Max rule's test budget | Measurement terms H + H_drift + H_D4 |
|---|---|---|---|---|
| XOR3 9803 c2_0 | anchor (2,), slack **−364** | g1 **+2815**: passes | **binding** | 72 + 3 + 98 = 173 |
| ANDOR3 9802 c2_0 | g0 stop margin **−4199**; anchor (1,) −9034 | **binding** | adds a further 4835 | 58 + 3 + 150 = 211 |

**Counts.**
- The training margin fails one cell of 2 (9802).
- The max rule alone fails one cell of 2 (9803).
- Measurement uncertainty fails none of the 2. Its whole sum (173) is below the 9803 deficit (364).

**Budget terms of 9803 c2_0's anchor (2,) at K3** [K], in score units, with θ = 100 000:
- the score at the stop is gain₂ + dose × 3 = 47 427 + 3 × 19 586 = **106 185**, a margin of 6 185 over θ
  (s*₂ = 2.684, 0.316 stage below the stop);
- testError = **6 550**, made of:
  - test_base **6 377**: the max rule, that is, the both-lines budget at writes [3, 3]. The one-port budget would be
    **3 198**;
  - H 72: the half bracket, 0.00366 stage × d;
  - H_drift 3;
  - H_D4 98: `d4_stage` 0.005 × d;
- slack = 106 185 − 100 000 − 6 550 + 1 = **−364**.

## 2. The max rule is conservative relative to what Lean needs

In `LayeredMonotoneTarget.lean`, `testError` appears in three places [K]:
- `Cell.Valid`, silent masks: `score x + testError < threshold` for every x with `gate.eval x = false`. For an either
  gate that is only x = (), whose score is 0. This clause holds with any testError below θ;
- `Cell.Valid`, anchors: `threshold + testError ≤ score y` for y ∈ {(1,), (2,)}. These are single-port scores;
- `ReadCalibration` (lines 183 and 195–198):
  - a non-firing read must be an `AdditiveSlot` within testError. For an either cell the only non-firing mask is ();
  - a firing read must be a `FiringSlot`. That needs only `score w y − testError ≤ scoreAt y` for the single-port
    anchors y, plus the measured monotonicity `scoreAt y ≤ scoreAt input`.

**No premise bounds the two-port score Z₍₁,₂₎ against the model.** The both-lines budget, the second term of the max
rule, bounds a quantity the theorem never uses for an either cell.

So the one-port test budget already satisfies **every Lean premise as the library stands**:
- no new proof is needed, and the Lean time is 0;
- the generated per-instance files are checked as now, by `decide +kernel` on the new testError;
- the max rule was CALIBRATION_PROPOSAL.md's own choice ("merged by taking their max. This is conservative"). Lean did
  not require it.

**The gain, recomputed on the existing data.**
- 9803 c2_0, anchor (2,) at K3: −364 becomes **+2 815**. XOR3 9803 then has room at K3: every other clause and cell
  already holds [K].
- 9802 c2_0 still fails, on its training margin (−4199) [K].
- The family's rate for the either cell at K3 is **0.58** under the one-port rule, against about 0.35 under the max
  rule [K/I, YIELD_CHECK_2X.md].
- So K3 per three-layer instance goes from about 0.15–0.17 to about **0.24–0.27** [G]. The expected counts of plan §3
  become about 16 instead of 10 for ANDOR3 (N 60) and for XOR3 (N 66) [G].

**The catch is a rule, not a proof.** The owner decided on 2026-11-23 at 11:12 (DECISIONS.md): "The either cell's
testError keeps the max rule … No rule change after a failure is seen."
- Moving to the one-port rule now would be a change made after dev failures were seen (9802, 9803).
- It is the owner's call, and must be fixed before the freeze and before any campaign seed is drawn.
- In its favour: it is campaign (a)'s family rule for c, so it **restores** continuity with campaign (a). The max rule
  is the departure from it.
- What it gives up is the family's both-lines FIRE check as a budget term. That check can still be run and reported as
  a control.

## 3. Protocol levers that keep the cell and the design point

| Lever | Effect on 9803's −364 | Effect on the either cell's K3 rate | Cost per instance | Continuity with campaign (a) |
|---|---|---|---|---|
| **One-port test budget** (§2) | **+3 179 → +2 815** | 0.35 → **0.58** [K/I] | 0 | **restores it** (family rule) |
| Solo scans in every instance (H_D4 measured, not `d4_stage`) | H_D4 98 → about 1–40 [K, 2x reruns]: +60 to +97, still failing | +1–2 % [G] | +45 CPU-min (ANDOR3) | kept (the plan's D4 audit, done everywhere) |
| More bisection or repeated reads (smaller half bracket) | H 72 → about 36: +36 | < +1 % [G] | +5–10 slots per group, about +10 CPU-min | kept |
| One more training round (hold 3) | 0: the stop, the scores at the stop and the budgets do not change | 0 | +1 lesson slot per group | breaks the word format (s^need FFF) |
| Lesson spacing (slot length) | drift only (H_drift 3): ≤ +3 | 0 | longer runs | kept |
| Lesson dose | the K3 margin needs a crossing at least about 0.33 stage (max rule) or about 0.17 stage (one-port) from its stop, so the rate rises with a larger dose | larger with a larger dose [I] | 0 | **changes the design point** (owner's decision, 2x): not a protocol lever |

**Why measurement does not help.** The K3 budget is dominated by the injected noise model, 3σ of decision 5's
constants (about 0.16 stage per port). Measurement terms total about 0.009 stage.

## Ranked recommendation

1. **The owner decides between the one-port and the max rule for the either cell's testError, before the freeze.**
   - The one-port rule needs no Lean change.
   - It raises K3 from about 0.15 to about 0.25 per three-layer instance.
   - It restores campaign (a)'s rule, and it gives XOR3 9803 room.
   - It is a change of a decided rule after dev failures were seen. If the owner keeps the max rule, the plan §3 counts
     stand (about 10 per group).
2. **Solo scans everywhere** only if the budget allows. The gain is marginal (+1–2 %), for about +45 CPU-min per
   instance.
3. **Not recommended**: a higher hold, the lesson spacing, more repeats. Each has no effect, or one below 1 %. A larger
   dose is a design-point change, not a protocol lever.
