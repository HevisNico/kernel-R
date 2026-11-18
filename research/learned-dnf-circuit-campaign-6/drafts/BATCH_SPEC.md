# Campaign 6: what the development batch's code computes (draft for review, sixth version)

It implements the design note (`659d3a2`) under the stopping rule (`2e26910`). **[C]** marks a choice made here. The
batch decides only `k`. Its definition of eligible is, unchanged, the one campaign 6 would preregister.

## 1. Runs, machines, procedure

**Seeds and machines.** Seeds 7701 to 7710 only; any other seed is refused. Seeds 7701–7705 run on `a` and 7706–7710
on `b`.

**Toolchain.** Campaign 5's pinned toolchain, checked before every run (`c4.require_pinned`, the kit's `identity`):
Python 3.12.3, numpy 2.3.5, ngspice 42, the PDK at `1232782c`, OpenBLAS SkylakeX.

**Runs per instance.** Nine, using campaign 5's deck and mismatch draw, with no noise (option B or C, section 5; A is
excluded):

- campaign 5's two calibration decks, guard on and guard off, by `run4.py --kind cal` unchanged;
- then five robust scans and two one-sided sets (section 2 and section 5).

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

**Smoke.** A declared nominal-cell smoke runs before the marker:

- each scan kind (`a` pair, `c` line 1, `c` both lines) and the one-sided set (`a`), each at both ascent steps,
  1/4 and 1/2;
- on the nominal calibration decks of campaign 5's RC;
- pushed on `evidence/learned-dnf-circuit-campaign-6-smoke`.

Its wall times serve only the choice of section 5. No number of the report comes from it.

## 2. The scans

**Reads.**
- For `a` and for `b`: the pair read, port 1 alone, and port 2 alone.
- For `c`: line 1 alone, line 2 alone, and both lines with the second 0.3 unit late (accepted).

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
- `c`: a line alone moves alone, the other line staying at `u(0)`; both lines move together for the both-lines scan
  **[C]**.

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
- The trip level `L`: the `Z` of the weakest fired state, campaign 5's `zint` of its `q_peak_before_fire`.
- Or "no crossing below 8".

## 3. Measured

An instance is measured if all of these hold, otherwise it is not:

1. All 9 runs complete, and both one-sided sets stay silent up to their bound.
2. Every bracket is consistent.
3. The five crossing scans (pair of `a`, pair of `b`, both lines of `c`, line 1 of `c`, line 2 of `c`) each cross
   below 8.
4. Every `D_p > 0`.
5. **Question 1:** for each of the four needs (pair of `a`, pair of `b`, line 1 of `c`, line 2 of `c`), `ceil(s*)`
   equals the first stage at which the matching read fires in the guard-on deck. A need above 7 cannot be checked
   and fails this test.

6. **Every deck read against the cell's own levels.**
   - For every read of the guard-on deck, of kind `r`, the FIRE bit must equal `Z >= L_r`. Both `Z` and `L_r` are
     rescaled, and `Z` is taken from the guard-off deck, as campaign 5 does.
   - A read with `|Z - L_r| <= H_x` is exempt.
   - The kinds are matched as follows:
     - `a` and `b`: `both` uses the pair scan; `port 1` and `port 2` must be silent wherever `Z < THETA + H_x`,
       the one-sided bound;
     - `c`: `port 1` and `port 2` use the line scans, and `both` and the 0.3-late `both` use the both-lines scan;
     - an `empty` read must be silent.
   - A disagreement outside the exempt band makes the instance not measured.

This rescopes campaign 5's FIRE/`Z` test from the nominal theta to the cell's own trip levels. In the code, a declared
wrapper builds the table with `P.load` and `P.table`. In `table`'s `bad` list it replaces the entries that begin
"FIRE bit" (that test, on the unscaled `Z`) with this test's entries, and keeps every other entry. It then rescales
the table (section 4) and passes it to `P.instance`.

## 4. Eligible: the frozen gate, on the scans' mapping

**Mapping onto the gate's fields** (campaign 5's `predicted.py` and `gate4.py`, imported and never edited).

1. Threshold.
   - Each cell's threshold is `theta_x = min L` over its scans (layer 1: the pair scan alone; `c`: 3).
   - Every score of cell `x`, the deck's `Z` and the scans' `L`, is multiplied by `100 000 / theta_x` and rounded to
     the nearest integer, ties to even.
   - So in the gate's units every cell's threshold is the gate's fixed `THETA = 100 000`, and the theory is
     unchanged **[C: per-cell units]**.
2. Campaign 5's pipeline, called unchanged on the rescaled table (`P.instance`):
   - the needs (first firing stage in the guard-on deck);
   - `Q1 = max(n_a, n_b) + 2` and `Q2 = max(n_c1, n_c2) + 2`, both at most 7 (so the needs are at most 5);
   - the guarded tuple (help, initialGain per port, one dose per layer), fitted on stages `0..Q`;
   - `epsilon`, the sensitivities, and the predicted observation.
3. Errors of cell `x`, both trainingError and testingError, at `K = 0`: campaign 5's budget plus two terms.
   - Campaign 5's budget: `epsilon + ceil(0.030 mV x the sum of the sensitivities)`.
   - Plus `H_x`, the half bracket: the largest `ceil(h_r x step_r)` over the cell's scans, where `step_r` is
     `(Z_r(7) - Z_r(0)) / 7` from the rescaled guard-off deck for read `r`.
   - Plus `S_x`, the spread: `max L - min L` over the cell's scans, rescaled.
   - The `K = 3` errors add the same `H_x + S_x` to campaign 5's noise budget. They are reported, as in campaign 5.
   - In the code, the wrapper adds `H_x + S_x` to the budgets that `P.instance` returns. It then recomputes `P.room`,
     `eligible` and `room_at_K3` from them, as `P.instance` does, before the gate is written.
4. maxWrites is `Q1` or `Q2`; the rail is `10 x THETA`.

**Eligible** = measured, and the frozen gate holds under `K = 0`, with Lean and the Python mirror agreeing per checker
(campaign 5's `gate4.py lean` and `check.sh`, as its rehearsal's `gate_dev`). Campaign 5's `room` is that mirror, with
both sides of every crossing: training silent before the need and FIRE at it, and the tests at the trained state.

**Settled: one threshold and one error per cell (option (a)).** The gate has one threshold and one error per cell.

- With `theta_x = min L`, the gate's silent checks are stricter than the cell's.
- A read of kind `r` predicted to fire must clear its own `L_r`. `S_x`, added to testingError, gives that.
- So the one-threshold default is checked by the gate itself, and eligible is exactly the gate.
- A per-read correction would need a condition outside the gate, or a threshold per read kind (a theory change).
  Neither is taken.
- The theory's single dose per layer (`a` and `b` share it) is kept, as in campaign 5. Its misfit goes into
  `epsilon`.

## 5. Affordability, and the choice of scan set (the owner's rule)

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
- **(B) The 5 crossing scans only.** These are the pairs of `a` and `b` and `c`'s line 1, line 2 and both lines.
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

- measures: 9 runs per instance on `I` instances, each run at the batch's mean wall time for its kind;
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
