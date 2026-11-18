# Campaign 6: what the development batch's code computes (draft for review, tenth version)

It implements the design note (`659d3a2`) under the stopping rule (`2e26910`). **[C]** marks a choice made here. The
batch decides only `k`. Its definition of eligible is, unchanged, the one campaign 6 would preregister.

## 1. Runs, machines, procedure

**Seeds and machines.** Seeds 7701 to 7710 only; any other seed is refused. Seeds 7701–7705 run on `a` and 7706–7710
on `b`.

**Toolchain.** Campaign 5's pinned toolchain, checked before every run (`c4.require_pinned`, the kit's `identity`):
Python 3.12.3, numpy 2.3.5, ngspice 42, the PDK at `1232782c`, OpenBLAS SkylakeX.

**Runs per instance.** Nine, using campaign 5's deck and mismatch draw, with no noise (option B or C, section 5; A is
excluded):

- campaign 5's two calibration decks, guard on and guard off. Declared deviation: `run4.py`'s own guard refuses these
  seeds. So `batch6.py cal` calls its cal branch's frozen functions and writes the same deck and the same record, plus
  one key; `test_batch.Equivalence` shows this without a simulator;
- then four robust scans and three one-sided checks: the two alone sets of layer 1 and `c`'s both-lines FIRE check
  (sections 2, 3 and 5, v9).

**Running them.**
- Four runs at a time per machine, detached (`setsid nohup`), while the session stays active in waits of at most
  5 min.
- Outside the kit **[C]**.
- `uptime -s` and the inventory at the start and end on each machine.
- Collection by campaign 5's `collect.py`.
- Every output is pushed as it is, on `evidence/learned-dnf-circuit-campaign-6-batch-<machine>`, with files above
  100 MiB in parts of 90 000 000 bytes listed in `PARTS.json`.

**Limits.** Each run is limited to `min(10 ceil(3 e / 10), 3 580)` s **[C: factor 3, as campaign 5's rehearsal]**:

- `e` = 925 s for a calibration deck (campaign 5's cost model), giving 2 780 s;
- `e` = 785 s for a scan (campaign 3's 520 s times 1.51), giving 2 360 s.

A run that does not complete, at its limit or otherwise, makes its instance not measured and so not eligible.

**Smoke**, declared, before the marker, on the nominal cell with the nominal calibration decks of campaign 5's RC.
It is pushed on `evidence/learned-dnf-circuit-campaign-6-smoke`.

- The whole instance at 1/4: the four scans and the three one-sided checks.
- The `a` pair and `c` line 1 scans at 1/2.
- Then the whole chain on its outputs: `predict6` (the wrapper, the instance's own Lean file, `check.sh`) and `report6`
  (k, I, E, and the B/C rule). So every path that computes `k` runs once before the marker.

**The 7692 check.** A declared check runs before the marker, on campaign 5's development seed 7692 (`check7692.py`, a
separate entry point; `batch6`'s guard is unchanged). It tests whether the leak deck draws the calibration deck's cell:

- `u(0)` and the first two joint-dose moves of each cell, against RM's 7692 guard-on deck;
- tolerances of 2 uV and 20 uV;
- beyond them: stop and report.

**The marker gate.** `schedule6.py batch` refuses to run unless the marker is pushed on this branch and names the
running code's commit and each file's SHA-256, with its `delta`.

Its wall times serve only the choice of section 5. No number of the report comes from it.

**v9: the change found by the smoke.**

- **What was found.** The declared nominal smoke at `5745fc2`, run before any batch seed, found a design error of this
  spec. `c`'s both-lines read fires at the preset and never crosses along the training path. Campaign 5's nominal table
  gives `Z` = 159 890 at stage 0, rising to 180 870 at stage 7, with FIRE at every stage. The read is only ever
  predicted to fire.
- **The change.**
  - The both-lines scan is replaced by a one-sided FIRE check: one read of both lines at `s = 0`, the lowest score
    along the path. If it fires, its own trip level lies below its score there, which is what the gate's fire-side
    check needs. The monotonicity assumption is then checked on the deck itself (section 3, point 6).
  - `c`'s threshold and spread come from its two line scans.
  - An instance is four crossing scans plus three one-sided checks.
- **What does not change.** The stopping rule. The B/C choice is recomputed by the owner's mechanical rule on the
  smoke's measured costs after this fix.

## 2. The scans

**Reads.**
- For `a` and for `b`: the pair read, port 1 alone, and port 2 alone.
- For `c`: line 1 alone and line 2 alone. Both lines (the second 0.3 unit late) are no crossing read; see v9 below.

Pulses are campaign 5's: 0.49 on layer 1 and 1 on `c`. A direct pulse stands for the routed one, and question 5
reports any difference. Each read is gated read-only. FIRE is campaign 5's: the latch rises through 0.9 V within
1.1 units.

**The training path.** Port `p` is held at `u_p(s) = u_p(0) - s D_p`, where:

- `u_p(0)` is its preset;
- `D_p` is the mean of the eight joint-dose moves `m_{p,k}` (`k = 0..7`, `move_mV` of the "joint dose" slots) in the
  guard-on deck, which is campaign 5's dose;
- the range is `s` in `[0, 8]`, which in mV is `u_p(0)` down to `u_p(0) - 8 D_p`.

Which ports move:

- Layer 1: both ports move together, for every read of the cell (port alone means "at the trained state").
- `c`: a line alone moves alone, the other line staying at `u(0)` **[C]**.

The cell is brought to `u(s)` by joint clock-only doses and per-port imposed leaks, each port within 2 uV, as
campaign 3's `move` does.

**The search.**
1. A coarse ascent from `s = 0` in steps of `delta`, a parameter: 1/4 for B, 1/2 for C (section 5).
2. Then bisection, until the bracket is at most 20 uV on the port of larger `D_p`.

**Disputed states**, as campaign 3. At the end of the search, the bracket is contradictory if some fired isolated
state has an `s` that is not larger than that of some silent one. Then:

- the fired state of smallest `s` is brought back, from where the cell then is, and read twice more;
- then the silent state of largest `s` is brought back and read twice more;
- one round only;
- each disputed state counts by the majority of its three reads.

The bracket is **consistent** if, after the majority, every state counted fired has a larger `s` than every state
counted silent.

**Outputs of a scan.**
- The bracket `[s_lo, s_hi]`, the threshold `s* = (s_lo + s_hi) / 2`, and the half bracket `h = (s_hi - s_lo) / 2`.
- The trip level `L`: the `Z` of the weakest fired state, campaign 5's `zint` of its `q_peak_before_fire`. Since v10
  it is reported only (question 3).
- Or "no crossing below 8".

## 3. Measured

An instance is measured if all of these hold, otherwise it is not:

1. All 9 runs complete, both one-sided sets stay silent up to their bound, and `c`'s both lines fire at `s = 0`
   (the both-lines FIRE check, v9).
2. Every bracket is consistent.
3. The four crossing scans (pair of `a`, pair of `b`, line 1 of `c`, line 2 of `c`) each cross below 8.
4. Every `D_p > 0`.
5. **Question 1:** for each of the four needs (pair of `a`, pair of `b`, line 1 of `c`, line 2 of `c`), `ceil(s*)`
   equals the first stage at which the matching read fires in the guard-on deck. A need above 7 cannot be checked
   and fails this test.

6. **The observational FIRE decoder** (v10, MAPPING_U.md 3). For every read of the guard-on deck, of every kind, the
   FIRE bit must equal `Z >= THETA`, where `Z` is its score on the u axis (section 4). Reads with
   `|Z - THETA| <= H_x` are exempt. Every both-lines read must also fire, with `Z(k) >= Z(0)` at every stage (v9).
7. **Each scan's own cell.** Every scan's and one-sided set's `u(0)`, both ports of its cell, must lie within 20 uV of
   the cell's `u` before the first read of its own guard-on deck.
8. **The one-sided sets' bounds.** Each set must have read both ports at its cell's bound `W_x + h_x` (section 4),
   exactly, as Fractions.

In the code, a declared wrapper builds the table with `P.load` and `P.table`. From `table`'s `bad` list it drops the
entries that begin "FIRE bit" (campaign 5's test against the nominal theta); point 6 replaces them. It keeps every
other entry, maps the scores (section 4) and passes the table to `P.instance`.

## 4. Eligible: the frozen gate, on the u-axis mapping (v10: MAPPING_U.md at `9c7a96e`, accepted by the owner)

**The scores** (campaign 5's `predicted.py` and `gate4.py`, imported and never edited).

1. **The axis.** Each port's coordinate at a deck read is `w_p = (u_p(0) - u_p) / D_p`, from the guard-on deck's `u`
   before the read. A read of mask `M` scores `Z = help + sum over p in M of (g_p + d w_p)`.
2. **Layer 1.**
   - `K = max over a, b of max(8 - s*_x, s*_x)`, `d = THETA / 2K`, `help = 0`, `g_x1 = g_x2 = d (K - s*_x)`.
   - The alone threshold is `W_x = s*_x + K` (`>= 8`, `>= 2 s*_x`).
3. **`c`.** `help = 0`, `d_c = THETA / (s*_1 + s*_2)`, `g_p = THETA - d_c s*_p`. The both-lines score at the preset is
   THETA, to the rounding of `d_c` (at most `(s*_1 + s*_2) / 2` units, about 4 on the nominal cell, inside its `H`).
4. **Integers.** `d`, `d_c` and `g` are rounded to integers, and then each `Z`, ties to even. Every field is a natural
   number, and every gain is below the rail.
5. **Campaign 5's pipeline**, unchanged on that table (`P.instance`): the needs, `Q <= 7`, the guarded fit, `epsilon`
   (now the dose-move variation and the rounding), the sensitivities, the budgets and the observation.
6. **Errors.** campaign 5's `K = 0` budget plus `H_x`, the pair's half bracket times `2d` (layer 1), or the largest
   line half bracket times `d_c` (`c`). `S_x = 0`: every kind is anchored at its own `u*`. The scans' `L` is reported
   only. `K = 3` adds the same `H_x`. The wrapper adds `H_x` to the budgets `P.instance` returns, then recomputes
   `P.room`, eligible, room_at_K3, counts_N_out and learning_ports.

**The one-sided sets.** Each reads both ports alone at `W_x + h_x`, `h_x` the pair scan's half bracket, in stages.
Each set waits for both pair scans of its instance, through `K`. It is "not started" if either has no consistent
bracket.

**Eligible** = measured, and the frozen gate holds under `K = 0`, with Lean and the Python mirror agreeing per checker
(campaign 5's `gate4.py lean` and `check.sh`, as its rehearsal's `gate_dev`). The check is per instance: each instance
gets its own Lean file and its own `check.sh` call, and passes only if its own file passes.

**The acceptance test of the redesign** (MAPPING_U.md 5), run once at this code before the marker, on machine a:

- one one-sided run per layer-1 cell on the nominal cell at `W_x + h_x`;
- one reach-only read at `s = 10`;
- the rest from the v9 smoke.

The nominal instance must be measured and eligible, its own Lean file passing `check.sh`. Otherwise the redesign
stops.

## 5. Affordability, and the choice of scan set (the owner's rule)

The table below was computed before v9 (five scans at an assumed 785 s). It illustrates only; the choice is made by
the owner's rule below, on the smokes' measured costs.

The table gives `E` by the stopping rule, computed with campaign 5's frozen `plan.split` and `plan.machine_expected`:

- `I = ceil(30 / k)`;
- the network on `ceil(k I / 10)` instances, the first of each machine, at 718, 132 and 1 400 s;
- limits `10 ceil(2 e / 10)`, within the kit's 14 400 s bound;
- measures at assumed costs, since the batch's own means are unknown before it runs:
  - calibration decks: RM's means, 721.0 s (guard on) and 587.2 s (guard off);
  - a scan: 785 s;
  - a one-sided set: 250 s;
  - a scan with the coarse ascent at 1/2: 685 s.

| `k` | `I` | E (A) | E (B) | E (C) |
|---|---|---|---|---|
| 2 | 15 | 51 329 stop | 40 841 stop | 35 049 stop |
| 3 | 10 | 37 919 stop | 31 319 stop | 27 426 **go** |
| 4 | 8 | 33 785 stop | 28 505 **go** | 24 958 **go** |
| 5 | 6 | 27 191 **go** | 23 231 **go** | 21 112 **go** |
| 6 | 5 | 24 509 **go** | 20 620 **go** | 19 803 **go** |
| 7 | 5 | 25 738 **go** | 21 850 **go** | 21 033 **go** |
| 8 | 4 | 23 056 **go** | 20 416 **go** | 18 643 **go** |
| 9 | 4 | 23 056 **go** | 20 416 **go** | 18 643 **go** |
| 10 | 3 | 19 145 **go** | 16 576 **go** | 16 105 **go** |

The three options:

- **(A) The 9 full scans** (sections 2 to 4 as written): 8 373 s of measures per instance. Go needs `k >= 5`.
- **(B) The crossing scans only.** In v9 these are four: the pairs of `a` and `b`, and `c`'s line 1 and line 2.
  - Each port-alone kind of `a` and `b` is checked instead by a one-sided set: one run per cell. The two ports are
    moved along the training path up to the state where each port's rescaled score reaches `THETA + H_x`, the
    measure's own error, and not the full budget **[C: the previous coordinator's refinement]**. Each port is read
    alone there.
  - The reads are only tests predicted silent, and the gate's silent check needs only `L_alone >= theta_x`.
  - A FIRE at or below that state makes the instance not measured. If the path never reaches that score by `s = 8`,
    the set runs to `s = 8` and shows the bound there.
  - The alone kinds then have no `L`. `theta_x` and `S_x` come from the pair scan alone. Point 6 checks the alone
    reads of the deck against the bound.
  - 5 733 s per instance. Go needs `k >= 4`.
  - Since v10 the one-sided bound is `W_x + h_x` on the u axis (section 4). The text above is v6's.
- **(C) B with the coarse ascent at 1/2 instead of 1/4**: 5 233 s per instance. Go needs `k >= 3`. The saving of
  about 100 s per scan is a guess, since no scan of this deck has been run.

**The risk of B and C.** Without a full scan of an alone kind, `theta_x <= L_alone` is shown only up to the one-sided
bound. That is what the gate's silent checks need, but question 3 then reports no spread for layer 1's alone kinds.

**The owner's rule for the scan set** (decided 2026-11-18, before any smoke):

1. A is excluded.
2. The code takes the ascent step `delta` as a parameter: 1/4 for B, 1/2 for C.
3. The declared nominal smokes measure, at both steps and before the marker, the wall time of each scan kind and of
   the one-sided set.
4. Each smoke cost is multiplied by 1.51 for mismatch, as in the stopping rule. The calibration decks stay at RM's
   means.
5. The least `k` giving go is recomputed for B and for C with those costs, by the same frozen `plan.split` and
   `plan.machine_expected` (`etable.py`).
6. **B is chosen, unless C's least `k` is strictly lower.** On a tie, B.
7. The owner confirms the result, and it is frozen in the marker (`delta` and the table) before any seed from 7701
   runs.

The batch's final `E` is computed from the batch's own measured costs (section 6). So a design chosen at `k >= 3` can
still stop if the scans cost more than the smokes suggest.

**B's assumption.** The one-sided set reads each port alone only at the bound state. It shows that nothing fires
below the bound only if firing is monotone in the score along the path. Question 5 reports every contradictory state
seen in the scans, as evidence on that assumption.

**Sensitivity to the scan cost**, which is the main unknown. The least `k` that gives go:

| Scan cost | A | B |
|---|---|---|
| 600 s | 5 | 3 |
| 785 s | 5 | 4 |
| 1 000 s | 6 | 5 |
| 1 200 s | none | 5 |
| 1 500 s | none | none |

"None" means that one instance's measures no longer fit one kit stage under campaign 5's split.

## 6. The report

**`k` and the decision.** `k` = the eligible count. Then `I = ceil(30 / k)` if `k >= 2`, then `E` by the stopping
rule:

- measures: 9 runs per instance on `I` instances, each run at the batch's mean wall time for its kind:
  - a complete run counts at its wall time;
  - a run stopped at its limit counts at that limit, so that a cut run does not lower the mean;
  - a run that failed otherwise has no wall time, and is left out and listed;
  - the two machines' `RUNS.json` are merged first (`schedule6.py merge`): no id twice, exactly the 90 runs, every
    status kept;
- network: on `ceil(k I / 10)` instances, at 718, 132 and 1 400 s;
- limits `10 ceil(2 e / 10)`, stages split as in campaign 5's section 10.5, and per stage and machine
  `sum / 4 + 3/4 max`.

The report then gives the decision. It gives every input, in exact arithmetic, and names the marker's commit and file
hashes.

**The five questions**, reported per instance:

1. `ceil(s*)` against the first firing stage, for each need, and the count of failures. This is the answer to
   whether campaign 3's method carries over to two-port and routed reads.
2. For each crossing, the margins `s* - (n - 1)` and `n - s*`, in stages and in mV, and the dominant term among the
   half bracket, the dose-move variation `max_k |sum_{j<k} m_j - k D_p|`, and the noise constants.
3. `L` per read kind and its spread.
4. Wall time per run kind and machine.
5. Bracket widths, contradictory states and their outcomes.

**Estimate.** About 84 000 s of compute. That is roughly 3.5 h of wall time on 2 x 4 slots, plus about 1 h of
smokes. The scan cost is the main unknown.
