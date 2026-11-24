# The yield lot: stage D only, before the freeze (rule written before any run)

**Development; owner's addition A of 2026-11-24 (relayed by the coordinator). Proposal, for the owner's approval.**
This file and the per-machine plans (`dev/yield_lot/PLAN_K01.json` .. `PLAN_K12.json`) are committed alone, before any
yield-lot run. Nothing in the lot is a claim: its seeds are dev seeds and count for nothing. Its only use is the
campaign sizes, by the rule below, fixed now.

## 1. Seeds

- **56 fresh dev seeds**: the first 56 integers from 6101 upward that are absent from the frozen-candidate exclusion
  list (`dev/predraw/EXCLUDED.json`, sha256 3b2811f9…, 13841 integers from all 201 branches). The noise seeds 10 S + n
  (n = 0..3) of each must also be absent.
  - That gives 6102 … 6225, listed in full in §6.
  - These are four-digit seeds, and the campaign draws in 10000–99999 (draw_seeds.py), so the two cannot overlap. A
    rescan at the freeze will in any case find them in this file and exclude them.
- **Assignment, in ascending order**: the first 24 to ANDOR3, the next 24 to XOR3, the last 8 to NOT1.

## 2. What runs

- Per instance, stage D only, through campaign_run3.py with `steps_until: "D"`:
  - the deck;
  - for XOR3 and NOT1, the kit's in-deck inverter gate (invinst.indeck, d599300);
  - stage_d5.py with the one-port rule and every mask read.
- No seal, no stage N, no controls.
- 12 machines, one plan each, balanced by expected stage-D CPU (yield_lot.py).
  - The expected total is about 48 core-h, about 4 per machine, about 1 h of wall time on 4 cores.
- The machine discipline of campaign_run2/3 applies: launch on an idle machine, an ENV.json per OUTROOT, and nothing
  that started is relaunched.
  - An instance whose stage D fails or times out is counted in n, as neither eligible nor with room. It is reported
    under its first failing step.

## 3. What is reported

Per group, from every machine's D/prediction.json (`yield_lot.py report`):
- `measured`, `eligible_K0` = k0/n and `room_K3` = k3/n;
- each rate with its 90 % Wilson score interval (z = 1.6449);
- the failing clauses, counted by clause and cell;
- the declared comparison, which counts for nothing: room under the max rule.

## 4. The sizing rule (fixed now)

- **Thresholds kept**: "established" needs ≥ 20 counted instances at K0 and ≥ 5 at K3. This is the owner's thresholds
  as relayed; the plan draft had 30 at K0.
- **Ceiling**: 280 core-h in all.
- **Rates used**: the lower ends L0_g and L3_g of the 90 % Wilson intervals of group g's eligible and room rates. These
  are conservative.
- **Size per three-layer group g** (ANDOR3, XOR3):
  - N0_g = ⌈20 / L0_g⌉, the size for K0;
  - N3_g = ⌈5 / L3_g⌉, the size for K3 (infinite when k3_g = 0);
  - N_g = max(N0_g, N3_g) when N3_g ≤ 80; when N3_g > 80 (or is infinite), N_g = N0_g and the group's K3 is declared
    in advance as "K3 not expected to be established". N_g is capped at 80.
- **NOT1** stays at **60**: it is never cut, as adopted.
- **Expected cost per instance** (core-min, plan_split.COST): gate + D + N0 + r3_g × 3 × noisy round, where r3_g is
  the point estimate k3/n. To this are added the D4 audits on every 6th instance, the U controls and one duplicate per
  group.
- **If the total exceeds 280 core-h**, cut one instance at a time, in this order, stopping as soon as the total fits:
  1. XOR3, from N_XOR3 down to N0_XOR3;
  2. then ANDOR3, from N_ANDOR3 down to N0_ANDOR3;
  3. then XOR3 and ANDOR3 alternately, XOR3 first, below N0.
  - A group cut below its N3 is declared **in advance** in PREDICTION.md as "K3 not expected to be established". One
    cut below its N0 is declared "K0 not expected to be established".
  - Every group is still run and reported by the established rule as it stands.
- **A group with k3 = 0** in the lot is sized for K0 only (N0_g), and its K3 is declared in advance as not expected to
  be established.
- **Rounding**: N are integers; the cuts take one instance at a time, XOR3 first.
- **The 8-machine fallback**: the same rule with the ceiling 8 × 4 × 5.5 = 176 core-h. NOT1 then stays at 60 only if
  it fits; otherwise NOT1 goes to 40, first.
- **The output** (`yield_lot.py size`) is the sizes, their expected counts at K0 and K3 (N × point rate) and the
  expected core-h. It is written to dev/yield_lot/SIZES.json and is the input of the draw.

## 5. What this rule does not do

- It does not change any gate, budget or threshold.
- It does not use the lot's predictions as evidence of anything.
- Its rates come from stage D alone, no network run. They are the rates of the prediction's existence, not of its
  correctness.

## 6. The 56 seeds

ANDOR3 (24): 6102, 6104, 6106, 6108, 6110, 6123, 6125, 6129, 6130, 6131, 6133, 6135, 6136, 6137, 6143, 6144, 6147,
6150, 6151, 6152, 6153, 6154, 6155, 6156

XOR3 (24): 6157, 6158, 6159, 6164, 6165, 6166, 6173, 6174, 6175, 6177, 6178, 6179, 6180, 6181, 6182, 6185, 6187, 6190,
6192, 6193, 6196, 6202, 6203, 6204

NOT1 (8): 6212, 6213, 6217, 6218, 6219, 6220, 6223, 6225
