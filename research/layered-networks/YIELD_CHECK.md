# Yield check before M2

**No simulation. From pushed family data only. Development, nothing preregistered.**

Marks: [K] counted from a file named here; [I] inferred; [G] an estimate.

## Data

| Source | Instances | Cells used |
|---|---|---|
| Top-up verdict, `research/function-family-dev` (0c003fbf), `topup-verdict/PREDICTIONS.json`: B2's ten instances 8301–8310, every member | 10 | per seed: a and b as pair cells (F2), a and b as unary cells (F4), c with two lines (F4), c with one line (X1) |
| Campaign (a), `evidence/function-family-campaign-predicted` (d7e4fcc2), `predicted/PREDICTED.json`: 8501–8515, one member each | 15 | every cell of its member |

A cell has room at K when the generator mirror's `failing` list names no condition of it. On these files the mirror
agrees with the kernel on every instance (`kernel_agrees_with_mirror`; top-up `gate.kernel`) [K].

Every instance of both sources was measured. So "eligible" here means room at K0.

Each physical cell is counted once per role:
- c's data are shared by F2, F3 and F4, so the two-line c is counted from F4 only. F2 gives the same 4/10 [K].
- a and b appear both as pair and as unary cells. These are different reads and anchors of the same physical cell.

## Per cell type [K]

| Family role, as the layered gate | n | K0 | K3 | Binding clause at K3, in the failures |
|---|---|---|---|---|
| pair cell → **both** | 20 + 12 | 32/32 | **23/32 (0.72)** | "first: stops" and "first: positive margin" (the stop round's margin, threshold + trainError ≤ score at the stop): 5. "first: early silence" (the round before the stop, score + trainError < threshold): 4 |
| unary cell (layer-1 dose) → **copy** at layer 1 | 20 + 12 | 32/32 | **28/32 (0.88)** | early silence 3; stops and margin 1 |
| c, one line → **copy** at layer ≥ 2 (its own K) | 10 + 6 | 16/16 | **13/16 (0.81)** | "second: line training" 3; "line testing margin" 2 |
| c, two lines → **either** | 10 + 9 | 19/19 | **11/19 (0.58)** | line training 10; line testing margin 4 |

- **K0 never fails.** Over 99 cell samples there are no K0 failures. The usable bound is what the sample size allows
  (Jeffreys 95 %: per-cell failure below about 3–7 %).
- **K3 fails at the training margins.** The binding clause is almost always a training margin of `Cell.Valid` at the
  stop. The round before the stop has to stay silent with the budget below θ, and the stop round has to fire with the
  budget above θ. This is the K3 noise term, about 0.16 stage per side [K, `TOPUP_RULES.md` §1], against the distance
  of s* to the nearer whole stage.
- **Two lines are worse than one.** An either cell shares one dose θ/(s*₁ + s*₂) between its two lines, and its
  testing margin is evaluated on the one-port rule.

## Independence within an instance [K, top-up]

| Member | Cells | All with room at K3 | Product of the per-cell rates × 10 |
|---|---|---|---|
| F2 | pair a, pair b, c | 2 | 2.2 |
| F4 | unary a, unary b, c | 3 | 2.9 |
| F3 | unary a, pair b, c | 2 | 2.5 |
| X1 | unary a, c | 7 | 7.2 |
| X2 | pair a, c | 6 | 6.4 |

- **Consistent with independence.** Observed all-cells-with-room counts match the product of the per-cell rates on
  every member, within one instance out of ten. Ten instances cannot show a weak correlation.
- **Cross-check against B2.** B2 itself had k_all3 = 2 of 10 for F1 (two pair cells and a two-line c). The product
  gives 0.72² · 0.58 · 10 = 3.0.
- **One weak sign of cell-level correlation.** A physical cell that fails as a pair cell also failed as a unary cell
  twice (a of 8301, b of 8308) out of the 3 unary failures.
- **A coupling the layered gate drops.** The family's pair cells share K and the dose of their layer. The proposal
  anchors each layered cell on its own K, so that coupling does not transfer.

## Projected yield per instance [G]

Independence is assumed. The interval is 90 % on the product of per-cell Jeffreys posteriors (Monte Carlo); a
layer-1 copy is scored with the c-one-line rate (the proposal's anchor rule) or, in brackets, with the unary rate.

| Instance | Cells | K0 | K3 |
|---|---|---|---|
| NOT1 | copy | 0.97 (0.89–1.00) | **0.79 (0.62–0.93)** [unary: 0.86] |
| ANDOR3 | both, copy, either, copy | 0.91 (0.75–0.99) | **0.26 (0.13–0.41)** [0.28] |
| XOR3 | both, both, either, copy | 0.92 (0.80–0.99) | **0.23 (0.13–0.36)** |

The either cell is the main drag: 0.58 alone.

**Campaign size [I].** At K3, a 3-layer group needs about 4 attempts per instance with room. 30 such instances
would take about 120 attempts. At the proposal's 52 and 84 machine-min per ANDOR3 and XOR3 attempt, that is about
100 and 170 machine-hours. That is near the whole stated budget (5–6 h on 12 machines of 4 cores, about 290
core-hours). At K0 the attempts are about 1.1 per instance.

## Where the data do not transfer

These are upper bounds unless stated otherwise:
1. **Inverter-fed both cells** (XOR's two layer-1 cells). Their pulses arrive about 0.08 tu apart. Every family pair
   cell was read with simultaneous pulses. No data exist for their room or their crossing; the pair rate is used
   without support.
2. **The either cell's single testError.** Lean's `Cell` has one; the proposal takes the max of the family's two
   testing rules. That can only lower the 0.58.
3. **Fit on training stages only.** ε and D_p come from n ≈ 3–6 stages, not an 8-stage deck. ε may be larger.
4. **New "not measured" causes** that the family data cannot count:
   - decoder disagreements under network timing (the either cell's two arrivals, up to 0.7 tu apart in ANDOR3);
   - question 1 with scans started from the trained state;
   - parallel scans.

   They multiply the yields above by an unknown factor ≤ 1.
5. **Per-cell anchors.** The family shares K and the dose over layer 1; the proposal does not. The direction of the
   effect is unknown.
6. **The inverter.** Its layered clause is the observed law (`checkInverterRead`), with no score and no K. The
   inverter session's own K3 silence margin had a minimum of −0.00003 over 60 instances [K, its message]. If a
   campaign also requires that margin, each inverter is a further factor of about 59/60.
7. **Copy at layer 1.** Its rate depends on which anchor rule is used: 0.81 with its own K, 0.88 with the family
   unary rule.
8. **Other circuits.** The family cells are the same R cell, at the same amplitudes (0.49 pairs, 1.0 unary and c)
   and the same noise constants. Nothing here covers corners, temperature or other seeds' ranges.

## Data files

The counts are reproducible from the two JSON files named above: a cell is classified by the prefix (`first i`,
`second 0`) of each `failing` entry at K0 and K3. No file of this package reads them; the counting was a one-off
script, not committed.
