# Campaign 6: what the development batch's code computes (draft for review)

It implements the design note (`659d3a2`) under the stopping rule (`2e26910`). It sets no campaign rule. **[C]** marks
each choice made here.

**Seeds and runs.** The batch runs seeds 7701 to 7710 only, 7701–7705 on machine `a` and 7706–7710 on `b`. All of
them use campaign 5's toolchain, its deck and its mismatch draw, with no noise. Each instance gets 11 runs:

- campaign 5's two calibration decks, guard on and guard off, unchanged (`run4.py --kind cal`);
- nine robust scans: for `a` and for `b`, the pair read and each port alone; for `c`, line 1 alone, line 2 alone, and
  both lines with the second 0.3 unit late **[C: the skewed pair, the less favourable of campaign 5's two]**.

The scans run after their instance's calibration decks. Four runs at a time per machine, detached, outside the kit
**[C: no campaign protocol to bind]**.

**The scan.** Every scan moves along the training path. Port `p` of a cell sits at `u_p(s) = u_p(0) - s D_p`, where:

- `u_p(0)` is the preset;
- `D_p` is the mean of the eight joint-dose moves of `p` in the guard-off deck, the measured dose move;
- `s` is a real number of stages.

Layer 1 thus reads each port alone at the trained state of both ports **[C]**. For `c`, a line alone is moved alone,
the other line staying at the preset; both lines move together for the both-lines scan **[C]**. The cell is brought
to `u(s)` by joint clock-only doses (writes enabled) and per-port imposed leaks, each port within 2 uV, as campaign 3's
`move` does. Each read is gated read-only and uses campaign 5's pulses: 0.49 on `a` and `b`, 1 on `c`, a direct pulse
standing for the routed one **[C]**. A read fires if it meets campaign 5's FIRE window.

The search, then the majority, as campaign 3:

- a coarse ascent in `s` from 0, in steps of 1/4, up to `s = 8`, then bisection until the bracket is at most 20 uV on
  the port of larger `D_p`;
- if contradictory states remain, one round reads each of the two disputed states twice more, and each counts by the
  majority of its three reads.

The scan writes:

- its bracket `[s_lo, s_hi]`, with threshold `s* = (s_lo + s_hi) / 2` and half bracket `h = (s_hi - s_lo) / 2`;
- its trip level `L`: the score `Z` (campaign 5's `zint` of `q_peak_before_fire`) of the weakest fired state;
- or "no crossing below 8".

**Measured.** An instance is measured if all of these hold, otherwise it is not:

- all 11 runs complete;
- every scan's bracket is consistent after the majority (every fired state lies above every silent state in `s`);
- every `D_p > 0`.

Campaign 5's FIRE/`Z` agreement test is not used: it compared readings with the nominal theta.

**Needs** (campaign 3's rule, `n x D >= gap` with `gap = s* D`): `n = ceil(s*)` for the pair of `a`, the pair of
`b`, line 1 of `c` and line 2 of `c`, each required in 1 to 7 **[C: the calibration stages]**.

**Budget of a read `r` of cell `x`, in stages, exact.** `B_r` is the sum of four terms:

- `h_r`, the measure's own error;
- the variation of the dose moves: `max_k |sum_{j<k} m_j - k D_p| / D_p` over `k <= 8` and the read's active ports;
- the noise-free allowance of campaign 5 (`K = 0`): `0.030 mV / D_p`, summed over the read's active ports;
- the one-threshold default: `(max L - min L)` over the cell's scanned kinds, divided by the read's score step per
  stage `(Z_r(7) - Z_r(0)) / 7`, taken from the guard-off deck **[C: that conversion]**.

The `K = 3` noise term, `3 sqrt(w^2 + b^2 + n d^2) / D_p` per active port, is reported. It does not decide
eligibility, as in campaign 5.

**Eligible** (room on both sides of every crossing). An instance is eligible if it is measured, all four needs exist,
and every inequality below holds (with `s*` of a port alone, or of both lines, taken as `+inf` when it never crosses):

- for `x` in `a`, `b`, with need `n`:
  - pair silent at `n - 1`: `s*_pair - (n - 1) >= B`;
  - pair FIRE at `n`: `n - s*_pair >= B`;
  - each port alone silent at `n`: `s*_p - n >= B`;
- for `c`, with needs `n_1`, `n_2`:
  - line `p` silent at `n_p - 1` and FIRE at `n_p`, in the same way;
  - both lines FIRE at `min(n_1, n_2)`: `min(n_1, n_2) - s*_both >= B`.

Campaign 5's rail and guarded-fit conditions are dropped **[C: no fit is made]**.

**Time limits.** Each run is limited to `min(10 ceil(3 E_r / 10), 3 580)` s **[C: factor 3, as campaign 5's
rehearsal]**. `E_r` is 925 s for a calibration deck (campaign 5's cost model) and 785 s for a scan: campaign 3's 520 s
times 1.51. A run at its limit is missing, and its instance is not eligible.

**Answers to the note's five questions** (all reported, none deciding):

1. For each of the four needs, `ceil(s*)` against the first firing stage of the matching read in the guard-on deck.
2. Each margin, in stages and in mV, and which of the four budget terms dominates.
3. `L` per cell and read kind, and its spread.
4. Wall time per run kind and machine.
5. Bracket widths, contradictory states, rounds of repeats, and their outcomes.

**The report.** It gives `k`, then `I = ceil(30 / k)` if `k >= 2`, then `E` by the stopping rule:

- measures: 11 runs per instance on `I` instances, each run at the batch's mean wall time for its kind;
- network: on `ceil(k I / 10)` instances, at the rule's 718, 132 and 1 400 s;
- limits `10 ceil(2 e / 10)`, stages split as in campaign 5's section 10.5, and the sum of
  `sum / 4 + 3/4 max` per stage and machine.

The report also gives the decision of the rule, and every input, in exact arithmetic. The code's commit and file
hashes are those of the pushed marker.

**Estimate.** About 10 x (1 315 + 9 x 785) = 84 000 s of compute. On 8 slots (two machines, four runs each), the
calibration wave takes about 40 min and the scans about 2.6 h, so roughly 3.5 h of wall time. The smokes come
before it: 4 scan kinds on the nominal cell, about 1 h on machine `a`. The scan cost is the largest unknown.
