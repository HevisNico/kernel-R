# Campaign 6: the mapping on the stored-voltage axis (design addendum, one page, for review)

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
- **Anchors** (θ at `u*`, the scanned threshold).
  - Layer 1: `g_1 + g_2 + 2 d s*_pair = THETA`, with `help = 0` and `g_1 = g_2 = (THETA - 2 d s*_pair) / 2`
    **[C: the symmetric split]**.
  - `c`: `g_p + d s*_line p = THETA`, with `help = 0`.
  - `d = 1 000` per write and per port, for both layers **[C: a unit]**.
  - Scores are rounded to integers, ties to even, so each carries an error of at most 1/4 000 stage. The verdicts do
    not depend on `d` beyond that rounding.
- **Unchanged.** Campaign 5's `P.instance` runs unchanged on this table: the guarded fit, `epsilon`, the sensitivities
  (`d / D_p`, so the 0.030 mV allowance is 0.030 mV in stages), the budgets, `room` and the observation.
- **What `epsilon` becomes.** Only the dose-move variation `|w_p(k) - k|`, about 0.01 stage, instead of the curvature
  of `q_peak`.
- **The other error terms.**
  - `H_x` is the half bracket times `2d` for a pair and `d` for a line.
  - `S_x = 0`, by construction, since every kind is anchored at its own `u*`.
  - The levels `L` and the per-cell rescaling of v9 are no longer used.

**2. The alone reads of layer 1, under C.**

- No scan per alone kind is needed. The split puts each alone threshold at `s*_p = THETA / (2d) + s*_pair`, about 53.
- The one-sided set becomes a fixed read of each port alone at `s = 8` **[C]**. The smoke's bounds were already 8, so
  its cost is unchanged.
- The model's scores of the alone reads are a construction. Their observed content is that each port alone stays
  silent up to `s = 8`, which the set and the decoder (point 3) check.
- `c`'s both lines (`2 THETA - d (s*_1 + s*_2) + d(w_1 + w_2)`, about `1.93 THETA`) are predicted to fire at every
  stage. The both-lines check at `s = 0` and v9's deck rule check that.

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

**5. The acceptance test**, fixed now and run once on the existing nominal smoke data (v9), with no new simulation:

- under this mapping, the nominal instance must be **measured** and **eligible**;
- the frozen gate must hold under `K = 0` on its own Lean file, with `check.sh` passing, so that Lean and Python
  agree.

If it does not, the redesign stops. The batch then runs as at `2b6cf6b` (plus the marker-gate fixes), or the diagnosis
is published, at the owner's choice. There is no second redesign.

**6. What does not change.**

- the stopping rule and the marker discipline;
- the scans, the decks, the both-lines check, the run set (nine runs), the limits and the cost table's inputs.

So the B/C result (C, `delta = 1/2`) is unchanged. Only a change of the one-sided read's cost would change it, and it
does not change.
