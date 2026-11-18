# Campaign 6: the mapping on the stored-voltage axis (design addendum, one page, for review, third version)

The owner allows one bounded redesign of BATCH_SPEC.md section 4 (v9, `2b6cf6b`). Only the scores given to the frozen
gate change. **[C]** marks a choice.

**Why.** At v9 the nominal cell is not eligible (smoke diagnosis). Its pair score `q_peak` grows convexly with the
stage, while the kernel's guarded tuple is linear, so the fit residual `epsilon` (706 of a budget of 808) eats a margin
the scan measures at 0.36 stage. The training itself is linear on the stored-voltage axis:

- the check7692 doses moved each port by 1.339 to 1.356 mV, the same from one dose to the next within 0.1 uV;
- campaign 3 predicted training from a gap and a dose on that axis, `n x dose >= gap`.

**1. The axis.**

- **Stored-voltage coordinate.** Port `p` of cell `x` at a deck read of stage `k` has the coordinate
  `w_p(k) = (u_p(0) - u_p(k)) / D_p`. This is its measured `u` before the read (campaign 5's `u_before_mV`), in units
  of its own mean dose. It is the instrument's output, and is exact after it.
- **Scores.** A read of mask `M` gets `Z = help + sum over p in M of (g_p + d w_p(k))`. This is additive in the ports,
  with one dose `d` per layer, and nothing else enters.
- **The principle** (the reviewers' revision): no free unit, and no model margin beyond an observation. The model
  must agree with every deck read and with the one-sided bound.
- **Anchors** (θ at `u*`, the scanned threshold).
  - Layer 1: `K = max over a, b of max(8 - s*_x, s*_x)`, `d = THETA / (2K)`, `help_x = 0`,
    `g_x1 = g_x2 = d (K - s*_x) >= 0`.
    - Each pair crosses at its own `s*_x`, since `2 g_x + 2 d s*_x = THETA`.
    - Each alone kind's model threshold is `W_x = s*_x + K`. This is `>= 8` and `>= 2 s*_x`, so every deck alone read
      (`w <= 7`) is predicted silent.
  - `c`: `help = 0`, `d_c = THETA / (s*_1 + s*_2)`, `g_p = THETA - d_c s*_p >= 0`.
    - Each line crosses at its `s*_p`.
    - The both-lines model score at `s = 0` is exactly THETA, matching the observed both-lines FIRE there. The stage-0
      both-lines reads fall in the `H` band and are observed to fire.
  - Integers. `d` and `d_c` are rounded to integers, and then the scores, ties to even. This moves a crossing by at
    most `1 / (2d)` stage, about 0.00005 on the nominal cell.
  - Signs and rail. The kernel's fields are natural numbers: `g >= 0` because `K >= s*_x` and `s*_p <= s*_1 + s*_2`.
    Every gain is below THETA, far under the rail `10 THETA`.
- **How these rules were set.** They were set by evaluating the earlier proposals at the nominal smoke's `s*` (about
  3.36 and 3.58), before the acceptance test. A free unit with a symmetric split put the alone thresholds near 53
  stages. `g = 0` would have predicted the stage-7 alone reads to fire. The rules are general in `s*` and not tuned to
  the nominal values. The acceptance test is unchanged.
- **Unchanged.** Campaign 5's `P.instance` runs unchanged on this table: the guarded fit, `epsilon`, the sensitivities
  (`d / D_p`, so the 0.030 mV allowance is 0.030 mV in stages), the budgets, `room` and the observation.
- **What `epsilon` becomes.** Only the dose-move variation `|w_p(k) - k|`, about 0.01 stage, instead of the curvature
  of `q_peak`.
- **The other error terms.**
  - `H_x` is the half bracket times `2d` for a pair and `d_c` for a line.
  - `S_x = 0`, by construction, since every kind is anchored at its own `u*`.
  - The levels `L` and the per-cell rescaling of v9 are no longer used.

**2. The alone reads of layer 1, under C.**

- No scan per alone kind is needed.
- The one-sided set reads each port alone at `W_x` plus `H_x` in stages, one read per port. The model's alone
  threshold then equals exactly the observed bound.
- `W_x` is 8 when `s*_x <= 4`, and up to about 10 if some `s*` is near 5. So the scan deck must bring the cell to
  `s` of about 10: about 13.5 mV of doses, against 10.8 mV in the deck's own eight stages. This is not yet run; the
  smoke reached `s = 8`.
- The set now depends on both pair scans, through `K`. In the code, each one-sided set waits for both pair scans of its
  instance (`a` and `b`). It is "not started" if either has no consistent bracket. A test covers this. Its cost is one
  read per port, about the smoke's 137 s.
- `c`'s both lines (`THETA + d_c (w_1 + w_2)`) are predicted to fire at every stage, at THETA exactly at the preset.
  The both-lines check at `s = 0` and v9's deck rule check that.

**3. The FIRE decoder stays observational.**

- For every deck read of every kind, the FIRE bit must equal `Z >= THETA`, outside `|Z - THETA| <= H_x`. Otherwise the
  instance is not measured.
- On this axis that means:
  - every pair or line read fires exactly when its measured `w` is beyond its scanned `s*`;
  - every alone read of layer 1 and every empty read (score 0) is silent;
  - every both-lines read fires.
- `Z` is computed from the deck's `u`, and the FIRE bits come from the guard-on deck, independently. So the test can
  fail.
- Every other measured condition of v9 stays: question 1, the 20 uV `u(0)` test, the one-sided and both-lines
  checks, and the monotonicity of the both-lines reads (now in `w`).

**4. The physics.** The joint dose is a fixed charge per write. Its move is constant to 1 % (check7692, at 1.339 to
1.356 mV), so a cell's state is linear in the writes on the `u` axis. The scan measures where on that axis each read
fires, and that is campaign 3's method. `q_peak` is not linear in the writes: the nominal smoke's pair steps rise from
3 432 to 4 453. It stays only in the reports. Only the nominal smoke and the development seeds are cited here.

**5. The acceptance test**, fixed now and run once:

- **New simulation, in one session on machine a, at the code that implements this page.** One one-sided run per
  layer-1 cell on the nominal cell, at `W_x + H_x` as the rule computes it. The smoke read the alone ports at exactly
  `s = 8`, and on the nominal cell the bounds are about 8.012 (`a`) and 8.004 (`b`), so "silent at 8" does not show
  "silent at `W + H`". The two runs take about 137 s each.
- **A reach-only read, in the same session**, of the nominal cell at `s = 10`, about 13.5 mV. It decides nothing. It
  shows whether the scan deck can impose the state the batch may need. If it cannot, that is a defect to fix before
  the marker.
- **Everything else** uses the existing v9 smoke data: the scans, the decks, the both-lines check.
- Under this mapping, the nominal instance must be **measured** and **eligible**;
- the frozen gate must hold under `K = 0` on its own Lean file, with `check.sh` passing, so that Lean and Python
  agree.

If it does not, the redesign stops. The batch then runs as at `2b6cf6b` (plus the marker-gate fixes), or the diagnosis
is published, at the owner's choice. There is no second redesign.

**6. What does not change.**

- the stopping rule and the marker discipline;
- the scans, the decks, the both-lines check, the run set (nine runs), the limits and the cost table's inputs.

So the B/C result (C, `delta = 1/2`) is unchanged. Only a change of the one-sided read's cost would change it, and it
does not change.
