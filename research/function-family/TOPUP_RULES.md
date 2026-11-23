# Rules of the top-up, written before any top-up data

**Status.** Development work for the step-1 family of `FAMILY_DESIGN.md` (section 0). It is not a preregistration and
claims nothing. These rules are fixed before the top-up's first run. No rule is changed after any top-up run has
started; a defect found later is reported and changes no count.

**Marks.** [K] known, from a file or a command named; [I] inferred; [G] guessed.

**What is already known, stated so that nothing hides behind it** [K]:
- **B2's results.** Its ten instances' runs and results are published (`research/learned-dnf-circuit-campaign-7-prep`
  at `b956efe4`). On them, `k_all3` = 2 (8303, 8306).
- **The smoke on 8303** (development, counts nothing), port 1 of a and of b at 1.0, gave:
  - a: s* 781/512, consistent;
  - b: s* 837/512, consistent;
  - both silent at the preset.

  The top-up measures 8303 again from scratch. The smoke's runs are not top-up runs.

## 0. The environment

- **What is met.** Python 3.12.3, ngspice 42 and the device library at 1232782c, each to its pinned hash
  (`dev/envcheck.py`).
- **What cannot be met: numpy's RECORD SHA-256** (pin `064003bd…`), because the pinned venv's RECORD file was never
  published.
- **The replacement check.** numpy 2.3.5 is installed in a venv outside the pinned path, where `c4.require_pinned`
  checks the versions only. Its installed RECORD must equal the official wheel's RECORD entry for entry, apart from
  the four installer lines, and every file on disk must match its RECORD hash. The wheel's SHA-256 is `0d8163f4…ae28`.
- `dev/envcheck.py` checks all of this on every machine before any run. Both RECORD hashes are recorded.

## 1. The unary port of each cell

For each instance, each of cells a and b gets **one unary port**, chosen from the top-up's own measures of that cell
alone, before any network run, by this rule.

**1. Eligibility of port p** (p = 1 or 2) of cell x. All three must hold:
- its unary scan completed;
- the scan found a crossing below 8 stages and is `consistent`;
- port p's read in the cell's preset check was silent.

**2. Its margin.** With `s*_p` the scan's crossing in stages, take the crossing's distance to the nearer whole stage:
`m_p = min(s*_p − floor(s*_p), ceil(s*_p) − s*_p)`. A scan's `s*` is the midpoint of its bracket, so it is never a
whole number [K, `scan6.scan`: `s_star = (s_lo + s_hi) / 2` with a half bracket of 1/512 or finer].

**3. The choice.**
- If both ports are eligible, take the one with the **larger margin**.
- **On an exact tie, take port 1.**
- If only one port is eligible, take it.
- If neither is, take port 1, and the cell is counted as it measures, almost certainly without room.

**4. What the choice uses.** Only the cell's two unary scans and its preset check. Not the budgets, not any gate,
not c, not the other cell, not any network run.

**5. After the choice.** In every later prediction, gate and network run of a member that uses x as a unary cell, the
term's input goes to x's chosen port. The deck reads and scan used are that port's.

**Why this criterion** [I]: room needs the crossing at least one budget from both ends of its step, about 0.164
stage at K = 3 (`FAMILY_DESIGN.md` 0.8). The budgets of x's two ports differ by much less than the margins do: on
8303, 0.161 to 0.162 stage for port 1 of a and of b (smoke, `room_check.txt`). So the larger distance to a whole stage
is the larger room, without computing a budget.

## 2. The size, by member

**1. `r_m`.** For each member m of the step-1 family (X1, X2, F4, F2, F3), and for each of B2's ten instances, the
instance has room for m when **m's gate at K = 3 under the one-port rule is true** (section 3). The gate is built
from:
- B2's measures;
- the top-up's measures;
- the unary ports of section 1.

  `r_m` is the number of the ten with room. An instance whose prediction fails or is unusable counts as no room. F2
  and X2 use no unary cell; their `r_m` is computed with the same instrument, not copied from B2's report.

**2. Removal.** A member with `r_m` ≤ 1 is removed from the family. If fewer than 3 members remain, **no campaign
follows on this family**.

**3. The size.** `I = ceil(30 / min_m r_m)` over the members kept, rounded up to a multiple of their number. This is
the pre-B2 rule of `PREPD/BATCH2X_PLAN.md` §8, `I = ceil(30 / k_all3)`, applied by member.

**4. It starts nothing.** The rule gives a size or "none". A campaign still needs its own preregistration, its
compute test, and the owner's go.

## 3. The room instrument

1. **The prediction** of each (instance, member) comes from the general path of `FAMILY_DESIGN.md` 7.1, frozen before
   it is run on any top-up data (point 4). It uses the mapping of `FAMILY_DESIGN.md` 2.4 and 0.2:
   - the unary anchor `g_u = θ − d s*_u` on layer 1's dose;
   - layer 1's K from B2's pair scans for every member;
   - c's one-line rule `d_c = θ / 2K_c`.

   Every formula is written out in section 3.5.
2. **Per cell**, the generator's mirror (`research/learned-dnf-generator`, `mirror.py`) evaluates each condition at
   K = 3. It reports which cell, and which condition, lacks room.
3. **The last word is the kernel's.** The member has room on the instance when the Lean file of its gate at K = 3,
   written by the generator, compiles with its `checks` theorem `= true`, with the checks of campaign 5's `check.sh`
   step 3 (forbidden tokens, warnings as errors, axioms).
   - Where the mirror and the kernel disagree, the kernel's verdict counts. The disagreement is reported as a defect
     of the mirror.
4. **Order.** The prediction code, the mapping amendment and the gate adapter are written, tested and frozen by
   SHA-256 before their first run on any top-up data. The top-up's runs may come first: they measure cells, and the
   rule of section 1 uses only them. No room verdict of any top-up instance is computed with code that is changed
   afterwards.

### 3.5 The mapping, fixed in full now

Everything the prediction code computes is fixed here, before any top-up data. Where it does what campaign 6 did, it
calls the frozen function by name:
- C5: `research/learned-dnf-circuit-campaign-5/predicted.py`, as `P`;
- C6: `research/learned-dnf-circuit-campaign-6/batch/predict6.py`, as `predict6`, at `ecfcd1c1`;
- FUP: `research/learned-dnf-circuit-campaign-6-followup/dev/t1_gate.py`, `one_port`, at `56f9e83e`.

Units are campaign 5's: scores in integer units of 1e-5 of the FIRE level, so `θ = THETA = 100 000` for every cell.
Stages are counted in each port's own mean dose.

#### 3.5.1 Where each number comes from

For instance s and member m:

| Cell kind in m | Its deck reads | Its scans and checks |
|---|---|---|
| **Pair cell** (a or b on two inputs) | B2's two decks of s (`s-cal-on`, `s-cal-off`): reads `empty`, `port 1`, `port 2`, `both` | B2's pair scan of that cell; B2's one-sided set of that cell |
| **Unary cell** (a or b on one input, on its port `p` of section 1) | the top-up's two decks of s (`s-cal-on-unary`, `s-cal-off-unary`): reads `empty` and `port p at 1.0` | the top-up's unary scan of that port (`s-unary-scan-xp`); the top-up's preset check of that cell, port p's read |
| **c** | B2's two decks of s: reads `empty`, `port 1`, `port 2`, `both`, `both, second 0.3 late` | B2's line scans of c; B2's both-lines check, for a c with two lines only |

- **Doses.** `D_xp` (mV) is the mean joint-dose move of the port over the 8 stages of the guard-on deck the cell's reads
  come from, as computed by `predict6.doses_V`.
- **Stored-voltage coordinates.** `w_xp(k)` come from that same guard-on deck, as computed by `predict6.deck_w`.
- **The FIRE bit and the latency** of each read come from that guard-on deck. Its Z is computed below.
- **The guard-off deck** of the same source is read only through `predict6.table`, as campaign 6 did; its Z is
  replaced.
- **The u(0) check.** Every scan and check used must have its `u0_V` within 20 µV of its source guard-on deck's u
  before the first read (`predict6.u0_check`, `U0_TOL_V`). A unary scan is checked against the top-up deck.

#### 3.5.2 The anchors

All scan values are exact rationals from the scan records (`s_star`, `half_bracket`).

1. **Layer 1's K.**
   - `K = max over the cells x in {a, b} whose B2 pair scan is complete and consistent of max(8 − s*_x,pair, s*_x,pair)`.
     This is computed **for every member**, whichever kind the cells have in it.
   - If neither pair scan is complete and consistent, `K = 8`.
   - With both consistent this is `predict6.layer1_K`, unchanged. So for F2, X2 and F1, d and the one-sided bounds are
     those B2 used.
   - This replaces the earlier proposal "K = 8 with no pair cell". Every instance of B2 has its two pair scans, and
     using them for every member leaves no choice to make.
2. **Layer 1's dose.** `d = round(θ / 2K)`.
3. **A pair cell x.** `help_x = 0` and `g_x1 = g_x2 = round(d (K − s*_x,pair))`, as `predict6.anchors` computes them.
   - Its alone model threshold is `W_x = s*_x,pair + K` (`predict6.layer1_K`).
   - Its one-sided bound is `W_x + h_x,pair`, which must equal the bounds B2's one-sided set ran at. They do, because
     K is the same.
4. **A unary cell x on port p.** `help_x = 0` and `g_xp = round(θ − d s*_xp)`, where `s*_xp` is the top-up's unary scan
   of that port.
   - The cell's other port is not an input of the cell in Lean, and its reads are not used.
   - `g_xp ≥ 0` holds because `s*_xp < 8 ≤ 2K` (`K ≥ 4`). The code asserts it.
5. **c with two lines** (F2, F3, F4). `help_c = 0`, `d_c = round(θ / (s*_1 + s*_2))` and `g_cp = round(θ − d_c s*_p)`, as
   `predict6.anchors` computes them.
6. **c with one line** (X1, X2): line 1, from a.
   - `K_c = max(8 − s*_1, s*_1)`, `d_c = round(θ / 2K_c)`, `help_c = 0`, `g_c1 = round(θ − d_c s*_1)`.
   - `g_c1 ≥ 0` holds because `s*_1 < 8 ≤ 2K_c`. The code asserts it.
   - Line 2 of c is not an input of c in Lean, and its reads are not used.
7. **Rounding.** Every `round` is Python's on a Fraction: to the nearest, ties to even (`P`'s convention, the
   docstring of `predict6.anchors`).

#### 3.5.3 The mapped table

- **The rule.** Every read `(cell, k, r)` that the cell uses gets `Z = round(help + Σ_{ports q of r} (g_q + dose · w_q(k)))`,
  with dose = d for a and b and d_c for c (`predict6.mapped`). Its FIRE bit and latency are kept.
- **The read-to-port map.** For a unary read `port p at 1.0`, the ports are `{p}`. Otherwise `predict6.PORTS_OF`.
- **Inside the code**, a unary read is renamed to the cell's single-port read of its own kind, `port p`, before the
  frozen functions see it. Its source stays the top-up deck. This rename is the only naming convention added.

#### 3.5.4 The needs, and question 1

| Cell kind | Need | Must equal the guard-on deck's first firing stage of | Otherwise |
|---|---|---|---|
| Pair cell | `ceil(s*_x,pair)` | `both` | not measured (`predict6.measure_instance`) |
| Unary cell | `ceil(s*_xp)` | `port p at 1.0` | not measured |
| c | `ceil(s*_p)` per selected line | `port p` | not measured |

- `Q1 = max(needs of the member's layer-1 cells) + 2` and `Q2 = max(needs of c's lines) + 2`.
- The member is not eligible if `Q1 > 7` or `Q2 > 7` (`P.instance`).

#### 3.5.5 The guarded tuple, epsilon, sensitivities

- **The guarded tuple.** `P.guarded`, generalised in one point only: a unary cell has one gain, `g_xp`, and its fitted
  reads are `empty` and `port p` instead of `P.GUARDED_READS_1`.
  - Layer 1: one dose shared by the member's layer-1 cells, over stages 0..Q1.
  - Layer 2: c alone, over 0..Q2, with reads `empty`, `port 1`, `port 2`, or `empty`, `port 1` for one line.
  - For F1 and F2 this is `P.guarded` exactly.
- **Epsilon.** As `P.instance`: per cell, the largest `|Z − G|` over its fitted reads plus `empty` (`EMPTY_IN_EPSILON`),
  over stages 0..Q of its layer.
- **Sensitivity.** `P.sensitivity`: the guarded dose over the port's mean measured dose, in mV.

#### 3.5.6 The budgets, H and S

`P.read_budget(eps, sens, writes, K, c4.DECISION5)`, with K = 0 and K = 3 and decision 5's constants (`b` 0.111,
`w` 0.094, `d` 0.009 mV). Two ports are added linearly; one port is one term.

| Cell kind | Training budget | Testing budget | H |
|---|---|---|---|
| Pair cell | `max over k = 0..need` of the two-port budget at `[k, k]` writes (`P.instance`) | the two-port budget at `[need, need]` | `ceil(h_x,pair · 2d)` |
| Unary cell | `max over k = 0..need` of the one-port budget of port p at `[k]` | the one-port budget at `[need]` | `ceil(h_xp · d)` |
| c | `max over its lines p and k = 0..n_p` of the one-port budget at `[k]` (`P.instance`) | the **one-port rule**: `max over its lines p` of the one-port budget at `[n_p]`, plus H + S, as `t1_gate.one_port` | two lines: `max_p ceil(h_p · d_c)`; one line: `ceil(h_1 · d_c)` |

- **S = 0** for every kind, since every kind is anchored at its own crossing (`predict6.measure_instance`, `Sx`).
- **H + S is added** to every training and testing budget at K = 0 and K = 3 (`predict6.augmented`). The c testing
  budget of the one-port rule already includes them, as in `t1_gate.one_port`.
- **c's both-lines read keeps the two-port testing budget** of `P.instance` plus H + S, as `t1_gate.one_port` does. It
  appears only for a c with two lines.

#### 3.5.7 The checks that make an instance "not measured"

These are `predict6.measure_instance`'s, by cell kind:
- a run not complete;
- a non-positive dose;
- a scan with no crossing or not consistent;
- the u(0) check;
- question 1;
- a one-sided set missing, at other bounds, or not all silent (pair cells only);
- the both-lines check missing or not firing (two-line c only);
- the decoder check: a mapped read with `|Z − θ| > H` whose FIRE bit disagrees with `Z ≥ θ`;
- c's both-lines reads not firing or not monotone (two-line c only).

**Added for a unary cell**: its preset check's port-p read must be silent, and the check must be complete. Anything
else makes the (instance, member) not measured.

#### 3.5.8 The observation

- **The source.** `P.observation`, generalised by the member's wiring (`FAMILY_DESIGN.md` 2.1), with the calendar of
  `FAMILY_DESIGN.md` 3.1.
- **Dates.** Slots of 22 units, the routing delay 3/2.
- **Emissions and scores.** One emission per predicted FIRE at its read's start plus that read's measured latency.
  c's emissions are every FIRE crossing over its calibration read's slot (amendment 1).
- **The teaching row of a first-layer cell not being taught** is the mapped read of its wired inputs among the taught
  term's, at its need. It is `empty` if none, and `port q` for F2's partial reads.
- **Test rows** use the same rule over each test pattern.

#### 3.5.9 The gate

- The generator (`research/learned-dnf-generator`, `emit.py`, generic style) writes one Lean file per (instance,
  member). It uses:
  - the member's cascade and its terms;
  - the guarded tuple;
  - θ for every cell;
  - the budgets above, at K = 0 and K = 3;
  - the observation;
  - c's reference scores, as `predicted.observation` gives them (`-`, `1`, `2`, and `12` for two lines).
- The verdict is the kernel's (section 3, point 3). The timing constants are `P`'s (`predicted.py` lines 38-40), as
  the generator's `legacy.py` passes them:
  - layer 1: `SKEW_A` 1/50, `DEADLINE_A` 11/10, `DURATION_A` 22;
  - c: `SKEW_C` 11/10, `DEADLINE_C` 11/5, `DURATION_C` 19.

#### 3.5.10 Implementation choices, each fixed now

| # | Choice | Fixed value |
|---|---|---|
| 1 | Port assignment of each member's inputs | `FAMILY_DESIGN.md` 0.1. For F2 the shared input is on a1 and b1. A unary input goes to the chosen port of section 1 |
| 2 | Which cell is the unary one | X1: a. F4: a and b. F3: a. X2 and F2: none |
| 3 | Pair cells' ports | Symmetric anchors (`g_x1 = g_x2`), so the input order on a pair cell changes no number |
| 4 | Unary read naming | `port p at 1.0` renamed to `port p` inside the code (3.5.3) |
| 5 | Lean input order | The member's inputs A, B, C, … as Lean ports 0, 1, 2, …; mask order as `spec.mask_index` |
| 6 | A run listed but missing on disk | Not measured |
| 7 | Exact arithmetic | Every number that becomes an integer is computed in Fractions, as `P` requires; no float after the deck's measures |
| 8 | Lean toolchain | Lean 4.35.0 from the archive the repository's CI pins, checked against its SHA-256 |
| 9 | How each file is checked | Campaign 5's `check.sh` step 3 (forbidden tokens, warnings as errors, axioms) on each gate file, after the theory is compiled once with check.sh's own commands |

#### 3.5.11 Testing and freezing the prediction code

- **Tested before it reads any top-up file.** The prediction code must be tested on:
  - B2's existing records: X2 and F2 on all ten instances, where their gates need no top-up data;
  - F1 on B2's ten, against B2's report's verdicts;
  - the smoke on 8303: the unary port 1 of a and of b, with B2's 8303 for the rest, as a dry run of X1, F4 and F3 on one
    port;
  - synthetic data: the generator's `synth.py` observations, one per member's shape.
- **Frozen by SHA-256.** It is then frozen by SHA-256, and the hash is sent to the coordinator.
- **Then it reads the top-up.** Only after that does it read any top-up file.
- **Defects.** Any difference between the code and this section 3.5 is a defect of the code. It is reported. A fix
  is a new frozen version, and every verdict is recomputed with it and reported beside the first.

## 4. What is reported

- **Per instance and cell**: both ports' s*, bracket, consistency, trip level and preset reads; the chosen port and
  its margin.
- **Per instance and member**: the gate's K = 0 and K = 3 verdicts, and the mirror's failing conditions.
- **Per member**: `r_m`, and whether it is removed.
- **The size**, or "none".
- **The duplicate's comparison** (`MACHINE_PLAN.md` 2).
- **Each machine's environment check.**
- **Every run's status and wall time** against its limit.

## 5. Not decided here

- The compute bound of a campaign.
- Whether a removed member could come back at a larger dose.
- The paired design.

Each is the owner's, after the top-up.
