# Yield check at the family design point (vhi 0.7, reltol 1e-5, junction areas)

**Development, nothing preregistered.** This replaces the projections of YIELD_CHECK.md, which DIAGNOSIS.md showed
hold only at the family's design point, now the layered deck's (DESIGN_POINT_REPORT.md).

Marks: [K] counted in a named file; [I] inferred; [G] an estimate.

## Do the family rates transfer?

- **The deck.** The R cell is identical to the family's, line for line (`tests/test_deck_identity.py`). The design
  point and the solver options are the same [K].
- **The budgets in stages.** NOT1's K0 error is 0.0134 stage and its K3 error 0.164, against the family's 0.0133 and
  0.164 [K, DESIGN_POINT_REPORT.md]. The copy cells of ANDOR3 are 0.0136–0.0174 at K0 and 0.165–0.168 at K3 [K].
- **The new terms are small.** H_D4 is 1–72 score units, and the c2_0 line-2 value is the largest of them. At 1x it
  was up to 137 [K].

**So the per-cell rates of YIELD_CHECK.md transfer for copy and both cells, with one correction for the either cell.**

## The reruns against the family rates

| Cell type | Family K0 | Reruns K0 (measured) | Family K3 | Reruns K3 |
|---|---|---|---|---|
| copy, layer 1 (unary / c one line) | 32/32, 16/16 | NOT1 c1_0, c1_1: 2/2 | 0.88 / 0.81 | 2/2 |
| copy, layer ≥ 2 (c one line) | 16/16 | c3_0: 1/1 | 0.81 | 0/1 (margin 0.057 stage) |
| both (pair) | 32/32 | c1_0: not measured (crossing at its stop, ±0.002) | 0.72 | — |
| either (c two lines) | 19/19 (one-port rule) | c2_0: 1/1 (max rule, +92) | 0.58 (one-port rule) | 0/1 (training margin −4114 too) |

- **Consistent with the family rates.** With 6 cells, the reruns cannot correct any rate by more than they bound.
  Every measured cell is eligible at K0 (family: 0 failures in 99).
- At K3: 2 of 3 copy cells have room (family 0.81–0.88) and the either cell has none (family 0.58).

### Correction 1: the either cell under the max rule (owner's decision)

- The family's 0.58 at K3 is under the one-port testing rule. Under the max rule the test budget is that of both lines
  together: 9844 against 5008 on c2_0, about 0.33 stage on each side [K].
- A K3 pass then needs a crossing more than about 0.33 stage from both its integer neighbours, for both lines [I].
  - Under a uniform fractional part, that is about 0.34 per line, and the line-1 anchor is the binding one on c2_0.
- **Either cell at K3: about 0.3–0.4 [I], not 0.58.** At K0 the max rule costs about 0.013 stage of extra budget. The
  K0 per-cell rate stays about 0.97 or better [I].

### Correction 2: a "not measured" class

- c1_0 was not measured because its crossing is at its stop within the bracket (±0.002 stage) [K].
- For a uniform crossing, that happens with probability about 2 × 0.002 = 0.004 per group [I]. It is rare. Here it is
  this mismatch draw: the same crossing in mV at 1x and 2x [K].
- Such a cell has a stop margin of about 0 and would not be eligible in any case. It lowers K0 yield by about 0.4 % per
  group [I].

## Projected yield per instance [G]

Independence is assumed, as in YIELD_CHECK.md: layer-1 copy at 0.81 (c one line) and both at 0.72. The either cell is
taken at 0.35 (correction 1), with 0.58 (the one-port rule) in brackets.

| Instance | Cells | K0 | K3 | Observed (one dev instance) |
|---|---|---|---|---|
| NOT1 | copy | 0.97 | **0.79** | eligible, room ✓ |
| ANDOR3 | both, copy, either, copy | 0.90 | **0.17** [0.27] | not measured (c1_0); 2 cells without room at K3 |
| XOR3 | both, both, either, copy | 0.90 | **0.15** [0.24] | not run (inverter to re-measure first) |

- **K3 is about 0.15–0.17 per 3-layer instance under the max rule** [G], against YIELD_CHECK.md's 0.23–0.26, which was
  under the one-port rule. At 1x it was about 1 % (DIAGNOSIS.md).
- K0 is about 0.9, unchanged.

## Campaign size [I]

- **Cost per attempt at 2x, without solo scans** [K, DESIGN_POINT_REPORT.md]: NOT1 4.4 CPU-min and ANDOR3 59.6.
  XOR3 is not run: by cell count, about 70 [G], plus the inverter re-measurement once.
- **K3, max rule.** About 6–7 attempts per 3-layer instance with room, so 30 instances take about 200 attempts. At
  about 60–70 min each, that is about 200–230 core-hours for one 3-layer group, against the stated budget of about
  290 core-hours.
- **K0.** About 1.1 attempts per instance, so about 35 core-hours for 30 instances.
- **With solo scans in every run** (D4 measured per instance rather than bounded by `d4_stage`), multiply by about
  1.8 (ANDOR3: 104.9 against 59.6 min).
