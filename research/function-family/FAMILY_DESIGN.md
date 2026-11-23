# Design note: a campaign over a family of functions on the learned AND-OR circuit

**Status.** A written study for the coordinator and the owner. It sets no rule and preregisters nothing. No
simulation was run, nothing was pushed, no session was created, no file of any branch was edited. Date: 2026-11-21.
**Sixth version** (section 0.8 added to the fifth). It folds in the coordinator's inputs:
- the findings of `SECOND_FUNCTION_DESIGN.md` (a stopped session, SHA-256 `66d8d6bc…`, which I have not read);
- the remark on tied ports;
- the review of the first version, with its reading on ties.

The changes are listed at the end. Earlier SHA-256: first version `4b209db5…19d9`, second `88dd2210…c05d`, third
`9d1a3877…f565`, fourth `ddb6027f…2871`, fifth `8b12599a…80e8`.

**Marks.**

- **[K] known**: read in a file at the commit named, or printed by a command I ran (the command is named).
- **[I] inferred**: my reasoning or arithmetic on [K] facts. Not reviewed by anyone.
- **[G] guess**: plausible, not supported by anything I read.

**Refs.** All fetched by branch name on 2026-11-21.

| Short | Ref | Commit |
|---|---|---|
| `main` | `main` | `d50cdec0` |
| `IMPL` | `research/learned-dnf-circuit-campaign-6-impl` | `ecfcd1c1` |
| `FUP` | `research/learned-dnf-circuit-campaign-6-followup` | `56f9e83e` |
| `PREP` | `research/learned-dnf-circuit-campaign-7-prep` | `b956efe4` |
| `GEN` | `research/learned-dnf-generator` | `4fca6256` |

Paths: `LC/` = `research/learned-coincidence/` (on `main`); `DNF/` = `research/learned-dnf-circuit/`; `C5/` =
`research/learned-dnf-circuit-campaign-5/`; `C6/` = `research/learned-dnf-circuit-campaign-6/` (all three on
`IMPL`); `NC/` = `research/network-circuit/` (on `IMPL`); `FUPD/` = the follow-up folder on `FUP`; `PREPD/` = the
prep folder on `PREP`; `GEND/` = the generator folder on `GEN`.

**Five scripts of mine** support sections 1 and 2. They are in the scratchpad next to this note, outside any git
tree:
- `fam/enum.py`, the enumeration;
- `fam/reps.py`, the tables;
- `fam/rewire.py`, every map of the four first-layer ports to inputs;
- `fam/subrun.py`, the tied members' slots against F1's;
- `fam/slots.py`, the slot tables of 2.6.

All are pure Python and run no simulation.

---

## The findings, in plain words

**Step 1 as the owner decided it (section 0):**
- **The members.** The five two-layer monotone functions of 3 inputs: A, A∧B, A∨B, A∧(B∨C), A∨(B∧C).
- **Size.** I = 15 under the pre-B2 rule, three per member. A∨B and A∨(B∧C) may be removed by that rule after the
  top-up.
- **F1** stays as the code's regression anchor, not as a member.

The findings below are the third and fourth versions', on the four-member family.

1. **The family is small and can be listed completely.** There are 15 shapes up to renaming inputs: 6 with one
   output and 9 with two. The theory as stated forces at most 2 first-layer cells, whatever B is. The reason: every
   OR cell receives every first-layer line, and a cell has two ports.
2. **Recommended family: the four three-cell functions with one output.** They are `(A∧B)∨(C∧D)` (campaign 6's
   function), `(A∧B)∨(B∧C)` (a shared input), `(A∧B)∨C` (one one-input term) and `A∨B` (two one-input terms).
   Together they are every OR of two incomparable terms of at most two inputs. All four use the same three cells and
   the same deck builder.
3. **A shared input needs no change to the Lean theory and no new kind of physical read.** Layer 1 is trained with
   the union of the targets in one slot, so no cell ever gets a partial pattern while its writes are enabled. The
   partial reads happen while c is taught, with layer 1 write-gated. They are already rows of the Lean premises, and
   the existing one-sided sets measure their bound. Campaign 5's claim G already tests that a stored voltage does
   not move during a gated read.
4. **A one-input term must be a unary cell: one port, at the line amplitude 1.0** (section 2.5).
   - The cheaper alternative, both ports of a pair cell tied to the input, is a sub-run of campaign 6's run, port for
     port (`fam/subrun.py`). Tied `(A∧B)∨C` is F1's run with C = D, and tied `A∨B` is F1's run with A = B and C = D.
     They would test nothing campaign 6's function does not test.
   - **That is why the tie route is rejected although it costs nothing.**
   - The unary cell is the family's one physical unknown. No first-layer cell has ever learned from one port.
5. **What each member adds over F1** [I]:
   - F2, the shared input: the partial reads during teaching.
   - F3 and F4: the unary cell, a first-layer cell trained alone on one port at 1.0.
6. **New measures are needed only for the unary cells**: a calibration read at 1.0 per stage and a unary scan for each
   of a and b. F1 and F2 use campaign 6's nine measures.
   - B2's ten instances (8301-8310, the batch at twice the dose) can be topped up with those runs, about 45 000 s.
   - Before that, **one cheap smoke on the nominal cell** (section 8.1, about 1 320 s of wall time) is the first step
     to ask the owner for.
7. **Under the draw, the noise claims will be counted for the family as a whole, not per member.** At the batch's
   room rate (about 1 instance in 5):
   - 16 instances give about 3 instances to count under noise, and about 0.7 members with 2 or more counted
     instances, on average;
   - 32 instances give about 6, and about 2.0 members.
   So per-member noise claims will mostly read "not established". I propose wording that says this before any
   data.
8. **Sizing is partly post hoc.** F1's and F2's room on B2 is already known (2 of 10); F3's and F4's is not. Section
   6.3 gives the owner's rule written before B2, by member (I = 16 if every member has room on 2 of 10), and a
   family rule to be written before the top-up.

---

## 0. Step 1, as the owner decided: the five two-layer functions of 3 inputs

**This section supersedes sections 1.3, 4, 5, 6.3, 8.4 and 9 wherever they differ.** Sections 1 to 3 stay as the
analysis behind it.

### 0.1 The members

The owner's step 1 is the five monotone functions of at most 3 inputs, up to renaming, that two layers of two-port
cells can compute. The other three monotone classes of 3 inputs, A∧B∧C, A∨B∨C and majority, are step 2, on layered
networks.

Every member is drawn on the same three cells. The deck always holds a, b and c; a cell a member does not use is
never pulsed in its network runs.

| Id | Function (owner's form) | Cascade | a | b | c | Inputs → ports | Tests |
|---|---|---|---|---|---|---|---|
| **X1** | A | 1 1 1 | unary A (port 1 at 1.0) | not used | one line, from a (port 1) | A→a1 | 2 |
| **X2** | A∧B | 1 1 2 | pair A, B | not used | one line, from a (port 1) | A→a1, B→a2 | 4 |
| **F4** | A∨B | 2 1 2 | unary A | unary B | two lines | A→a1, B→b1 | 4 |
| **F2** | A∧(B∨C) ≡ (A∧B)∨(A∧C) | 2 1 3 | pair A, B | pair A, C | two lines | **A→a1 and b1**, B→a2, C→b2 | 8 |
| **F3** | A∨(B∧C) | 2 1 3 | unary A | pair B, C | two lines | A→a1, B→b1, C→b2 | 8 |

- **Renaming.** F2 and F3 here are the classes of sections 1.2 and 2.2, written in the owner's form. F2's shared
  input is now named A, and F3's unary term is a. Nothing in sections 2 and 3 depends on the names [I].
- **One-input terms** are unary cells, one port at 1.0, as section 2.5 recommends. With ties, X1 and F4 would be
  sub-runs of X2 and F1 (2.6).

### 0.2 X1 and X2: c with one line

**What c is** [K for the Lean, I for the reading]:

- In X1 and X2, `Cascade A 1 M` has A = 1. c has one Lean port, fed by a's FIRE on c's port 1, and its port 2 is
  never pulsed. `RoutedBatch` needs only that one line [K, `LC/TwoLayerTarget.lean:74-76`].
- c then learns a copy: it fires exactly when a fires. **No OR is learned.**
- What X1 and X2 test is:
  - layer 1's learning (X1: a unary cell; X2: a pair cell);
  - c's single-line learning from a routed pulse;
  - the whole chain through two cells.

**What it means for the claims** [I]:

- **The primary claim keeps its form.** L1 and L2 have one learning line on c, and T has `2^M` = 2 or 4 patterns.
  The claim's sentence "c fires exactly on f" holds with f = A or A∧B.
- **N-out of c** counts when a and c have room. There is no both-lines read, so c's testing error is the one-port
  budget by construction, with no rule needed.
- **The family claim's wording must not say "learns an OR" for X1 and X2.** I propose "learns f" throughout.

**What it means for the measures** [I]:

- X1 needs a's unary measures (deck reads at 1.0, unary scan, preset check) and c's line-1 scan.
- X2 needs a's pair scan, a's one-sided set and c's line-1 scan.
- Neither needs c's both-lines check or c's line-2 scan. B2 already holds every run X2 needs; X1 needs the top-up's
  unary runs.

**What it means for the mapping.** MAPPING_U anchors c on two lines: `d_c = θ / (s*_1 + s*_2)`, with both lines at
s = 0 exactly at θ [K, MAPPING_U §1]. With one line there is no both-lines read. The mapping amendment of 2.4 must
also give c a one-line rule. I propose the layer-1 form, `d_c = θ / 2K_c` with `K_c = max(8 − s*_1, s*_1)`,
`help = 0` and `g_1 = θ − d_c s*_1 ≥ 0` [I, not checked against MAPPING_U's principle].

**What it means for Lean.** Cascade 1 1 1 and 1 1 2 are new shapes for the generator. Its synthetic cases were
2 1 4, 2 1 3 (twice), 3 1 3, 2 2 4 and 0 1 2 [K, `GEND/README.md`]. One synthetic gate per new shape is compiled first
[I].

### 0.3 F1, campaign 6's function

- **Recommendation: F1 is not a campaign member. It stays as the code's regression anchor** [I]. The general path
  on F1, with campaign 6's 1x design point and attempt c1's evidence, reproduces its frozen files byte for byte
  (7.1, test (a)). That costs no simulation.
- **Why not a sixth member.**
  - The family statement "every two-layer monotone function of 3 inputs" would no longer describe the family.
  - F1 adds a 16-pattern network run, the costliest, and nothing physically new beyond F2 (2.6).
  - Its room on any instance equals F2's (6.1), so it adds no counted noise instance either.
- **The alternative** is F1 as a sixth member, for continuity with campaign 6, with its 4 inputs named as such in the
  claims. It would cost about one more member's share of every stage.

### 0.4 Room and size, by the pre-B2 rule per member

**Expected room per member** [I, the product model of 6.1: 0.75 per pair crossing, 0.65 per line crossing]:

| Member | Crossings | Room share | Expected r of 10 | P(r ≤ 1 of 10) |
|---|---|---|---|---|
| X1 | unary a, c line 1 | 0.42 | 4.2 | about 0.04 |
| X2 | pair a, c line 1 | 0.49 | 4.9 | about 0.01 |
| F4 | unary a, unary b, c 1, c 2 | 0.18 | 1.8 | **about 0.44** |
| F2 | pair a, pair b, c 1, c 2 | 0.24 | known on B2: **2** (= F1's, 6.1) | n/a |
| F3 | unary a, pair b, c 1, c 2 | 0.21 | 2.1 | about 0.35 |

The `P(r ≤ 1)` column is a binomial at the room share [K, my computation; I for the rates]. F2's count is known
because it uses B2's crossings, which B2 already measured; the others need the top-up.

**The rule, option (a) of 6.3, applied to five members:**

- A member with `r_m` ≤ 1 (of B2's 10, after the top-up) is removed before the draw.
- If fewer than 3 members remain, no campaign.
- `I = ceil(30 / min_m r_m)` over the members kept, rounded up to a multiple of their number.
- With `min r_m = 2` and five members, **I = 15, three instances per member**.
- **F4 is at real risk of removal** (about 0.44), and F3 too (about 0.35). The rule says so now, before the top-up.
- If both are removed, three members remain (X1, X2, F2), and I = ceil(30/2) = 15, five per member.
- X1's and X2's high room does not raise I: the rule sizes on the weakest member kept.

### 0.5 The draw and the claims, for five members

- **The draw**: balanced, by section 4's SHA-256 sort, over the members kept, in the declared order X1, X2, F4, F2,
  F3. Seeds 8501 upward, I of them. Whether 85xx is free is not checked.
- **The primary claim**: section 5.1's wording over the members kept, "learns f" (0.2).
  - Established with at least 2 counted instances on each member, so at least 10 in all for five members.
  - With 3 per member, an ineligible instance leaves 2; two of a member's three leave 1, and then that member reads
    "held on one instance, not established".
- **The noise claims**: N_N = 2 pooled, from at least 2 members.

**What is expected, stated before any data** [I, at the product-model rates, three instances per member]:

| | Value |
|---|---|
| Expected instances with room for every cell | about 4.6 |
| P(pooled noise claim reaches 2 instances) | about 0.97 |
| P(it reaches 4) | about 0.73 |
| Expected members with 2 or more counted noisy instances | about 1.2 of 5 (X1 0.39, X2 0.48, F2 0.14, F3 0.11, F4 0.08) |

The probabilities are binomial and Poisson-binomial [K, my computation; I for the rates]. **So the per-member noise
lines will mostly read "held on one instance" or "not established" for F2, F3 and F4.** That is stated now.

### 0.6 Costs

**Measures per instance** [I; every member uses the deck with the unary reads, one deck builder]:

| Member | Runs | Run time |
|---|---|---|
| X1 | decks, unary scan of a, c line 1, preset check of a | 4 596 s |
| X2 | decks, pair scan of a, c line 1, one-sided set of a | 5 123 s |
| F4 | decks, unary scans of a and b, c lines 1 and 2, both-lines check, 2 preset checks | 5 900 s |
| F2 | decks, pair scans of a and b, c lines 1 and 2, both-lines check, 2 one-sided sets | 6 954 s |
| F3 | decks, unary scan of a, pair scan of b, c lines 1 and 2, both-lines check, one-sided set of b, preset check of a | 6 427 s |
| Mean | | 5 800 s |

The decks with the unary reads are 1 939 + 1 407 s in every row.

**Network slot factors against F1's 34 slots** [G, slots ∝ cost]: X1 0.37, X2 0.47, F4 0.59, F2 0.76, F3 0.73, mean
0.58.

**Steps and totals** [I]:

| Step | Cost |
|---|---|
| Smoke on 8303 (the unary cell) | 5 runs, about 3 371 s of runs, about 2 561 s of wall time (section 8.1, and the code sent for review) |
| Top-up of B2 | 46 460 s of runs (8.2) |
| Gates on B2 | 50 predictions and gate files (10 instances × 5 members), no simulation |
| Rehearsal | about 39 000 to 57 000 s of machine time (8.3), with one run without noise, one noisy run and one untrained run per member |
| **Campaign (a), drawn, I = 15** | measures E about 33 000 s; network run time 16 100 to 33 700 s, E 10 400 to 21 900 s; **total about 43 500 to 55 000 s**, within the draft's 72 000 s |
| Paired, I = 15 (every member on every instance, superset measures) | **total about 98 000 to 154 000 s**. Each member's P(≥ 2 counted noisy instances) rises to about 0.78 to 1.0 |

**The noise sensitivity reading** (8.3): its 8 noisy runs, 4 on 8303 and 4 on 8306, use **F2** if F1 is not a member
[I]. F2 has F1's crossings and known room on both instances. That replaces open choice 9.14's F1.

### 0.7 Open choices for step 1, each with my recommendation

1. **F1**: the regression anchor only, not a member (0.3).
2. **c's one-line mapping rule** for X1 and X2: `d_c = θ / 2K_c` (0.2), written with the unary amendment, before
   the top-up.
3. **The size**: option (a), I = 15 with five members, with the removal rule as written. **F4 and F3 may be
   removed.**
4. **The draw**: balanced, as the owner decided. The paired design stays the alternative, at about 98 000 to
   154 000 s.
5. **The noise sensitivity reading**: on F2.
6. **The deck**: one deck with the unary reads for every member (one deck builder), rather than a deck per member.
   It costs 7/6 of a deck for X2 and F2, which do not need the unary reads.

### 0.8 What, fixed before the top-up, could raise the unary room rate

The question matters for the family: if the unary cells' room is low, F3 and F4 drop out, and step 1 is left with
X1, X2 and F2, of which only F2 learns an OR. Any choice below must be fixed before the top-up's data [I].

**What room is, for one crossing** [K for the definitions, I for the reading]:

- A crossing has room at K = 3 when it lies at least one budget from both ends of its step. In B2's report a
  crossing is "in its window" when both `below` and `above` are at least `budget_stages` [K,
  `BATCH2X_REPORT.json`, `crossings_in_their_steps`], about 0.164 stage for a one-port read at K = 3.
- With crossings spread over more than a step across instances, the share in the window is about `1 − 2 × budget`,
  about 0.67 [I]. B2's line crossings gave 13 of 20.
- The budget in stages is `3 × s × sqrt(w² + b² + n d²)` divided by the step `s × D`, which is
  `3 × sqrt(w² + b² + n d²) / D` [K for the budget, `FUPD/DESIGN_NOTE_WIDEN.md` B.1; I for the ratio]. The read's
  sensitivity `s` cancels.

**The candidates, in order of what I expect from them:**

1. **Choose the unary port per cell from its measures, by a rule fixed now** [I].
   - A unary cell needs one port, and either port will do. If both ports of a and b are scanned at 1.0, the rule
     "use port 1 if its crossing is in its window, else port 2 if that one is, else port 1" picks the port before
     any network run.
   - At 0.65 per port and independent ports, a cell's share rises to `1 − 0.35²` ≈ 0.88. F4's share would go from
     about 0.18 to about 0.33, and F3's from 0.21 to 0.28 [I, product model].
   - **Cost**: a second unary scan per cell (about 600 s each), and port-2 reads at 1.0 in the deck.
   - **The claims stay within their scope**: instances, and here ports, selected by per-cell measures before any
     network run. That is already the campaign's scope statement [K, the draft's "In one page"].
   - The wiring then differs per instance (A→a1 or A→a2). The draw is unaffected, since it fixes the function, not
     the port.
   - Whether the two ports' crossings are independent is not known. If they are correlated, the gain is smaller. B2's
     c1 and c2 were in their windows together on 4 of 10 instances [K, `BATCH2X_REPORT.json`], against 4.2 expected
     if independent at 0.7 and 0.6 [I].
2. **A larger dose** [I].
   - The budget in stages falls as `1/D` while `w`, `b` and `d` are fixed in mV. At 3x, about 0.164 × 2/3 ≈ 0.11
     stage, so a share of about 0.78 per crossing.
   - But it changes the design point of every cell and every member, which the owner fixed at 2x. It needs its own
     development runs at 3x (FUPD/DOSE_PLAN.md proposes a way), so it is a separate decision, not a tweak.
3. **The unary amplitude (1.0, chosen by analogy with c)** [I].
   - By the ratio above, the amplitude does not change the budget in stages to first order. It moves where the
     crossing falls (`s*`), not the width of the window.
   - So it is a lever only against the two hard failures:
     - a crossing below 0, which fires at the preset, so the need is 0 and the cell is ineligible;
     - a crossing beyond the deck's 8 stages.
   - The smoke shows where `s*` lies at 1.0. If it is near 0 or near 8, a lower or higher amplitude fixed now, the
     same for every instance, would help. Otherwise not.
4. **Not candidates**:
   - the noise constants, which are decision 5's, fixed by the owner;
   - the K of the budgets;
   - any choice made after seeing the top-up.

**Recommendation** [I]. If the smoke shows unary crossings inside the deck's range, fix candidate 1 (both ports
scanned, the port rule above) before the top-up, at about 1 200 s more per instance. That raises the top-up to about
58 000 s. Keep 1.0. Leave the dose to the owner.

---

## 1. The family

### 1.1 The constraints, and where each comes from

| Constraint | Source |
|---|---|
| A first-layer cell learns one conjunction of its target ports. A target has at least 1 input (unary terms allowed) | `checkConjunctions` requires `0 < card (target a)` [K, `LC/MonotoneTarget.lean:79-82`] |
| An OR cell selects lines; it fires when any selected line fires. `alwaysFire` gives constant true with zero lines | `Disjunctions`, `output` [K, `LC/MonotoneTarget.lean:10-20, 102-104`] |
| Terms used by any output must be pairwise incomparable: the line's own target must fire that line alone | `Cascade.reachable` [K, `LC/MonotoneTarget.lean:86-89`] |
| **Every OR cell receives every first-layer line** | `RoutedBatch`: `∀ a, right.arrival a = (left a).emissions.head?.map (· + delay a)` [K, `LC/TwoLayerTarget.lean:74-76`]; used for every OR cell `i` at every test [K, `LC/MonotoneOneSidedTarget.lean:44`]; its checker `checkRoute` [K, `LC/MonotonePremiseTargets.lean:88-91`] |
| A cell has two ports | [K, `DNF/dnf.py` docstring line 4: "the cell of `../circuit/cell.spice` has two ports"] |
| Terms ≤ 2 inputs, OR cells ≤ 2 lines | the generator's two-port flag [K, `GEND/spec.py`, `physical`] |

**Consequence** [I]. An OR cell has A Lean ports and only two physical ones, so **A ≤ 2 for every member, also when
B = 2**. Both OR cells of a B = 2 member receive both lines. A line an output does not select still arrives, and
must stay silent at its untrained gain [K, `Disjunctions.check`, `LC/MonotoneTarget.lean:67-69`].

**Why not A > 2 with unwired lines.** Layer 1 already uses a convention: an external input not wired to a cell is a
Lean port with gain 0. It "arrives" in the record at the pattern's date [K, `C5/predicted.py:382-383, 404`:
`arr1(start, x)` gives every input of `x` to every cell]. Extending that convention to layer 2 would allow A > 2, but
the recorded arrival of an unwired line is then the upstream FIRE plus 1.5. The dated decoder requires the OR cell's
FIRE to come after every arrival [K, `ThresholdRead`, `LC/MonotoneOneSidedTarget.lean:12-16`]. An unwired line whose
upstream fires late would make the premise false. The checker would refuse such instances; it would not accept a
wrong one [I]. I did not check c's latencies against that. **I exclude A > 2** (open choice 9.2).

**Further exclusions** [I]:

- **Unused inputs and unused cells.** They add a dimension or a cell that nothing reads.
- **Two outputs with the same function.** They add an identical copy.
- **The constant outputs.** Constant false (no line, not `alwaysFire`) never receives a pulse. It is silent by
  construction and tests no learning.
- **Constant true is not physically meaningful on this cell.** `alwaysFire` requires a FIRE on the read with no
  arrival [K, `FiringMaskRead`, `LC/MonotoneOneSidedTarget.lean:30-31`; `MONOTONE_DNF.md`: "a native realization of
  constant true needs a genuine read gate and a qualifying biased read of the empty mask"]. On the bench a cell acts
  only on a pulse: each port's timing signals are tied to "the start of that port's next pulse" [K, `NC/net.py`
  docstring lines 9-12]. A FIRE with no pulse would need an extra clock port, and that is another circuit.

### 1.2 Every shape

`fam/enum.py` enumerates every cascade under section 1.1 [K, printed: "42 labelled cascades, 15 classes"]. A class
is a set of cascades equal up to renaming inputs, reordering first-layer cells and reordering outputs. The
representative of each class is chosen to match the names already used in the repository (S1, S2, S4 of `GEND/`).

**Truth tables.** Each output is written as a 0/1 string over the patterns in the generator's mask order: input 0
(A) is the most significant bit, so for M = 3 the order is `-, C, B, BC, A, AC, AB, ABC` [K, `GEND/spec.py`,
`mask_index`]. The patterns where the output is 1 are listed after it.

**Cascades.** `Cascade A B M`. Terms are the first-layer targets. "lines" is the selected set of each output, by cell
index.

**One output (B = 1)**

| Id | Cascade | Terms | Lines | Function = truth table (true on) | Shared input | Cells |
|---|---|---|---|---|---|---|
| **F1** | 2 1 4 | {A,B}, {C,D} | [0,1] | (A∧B)∨(C∧D) = `0001000100011111` (CD BCD ACD AB ABD ABC ABCD) | – | 3 |
| **F2** | 2 1 3 | {A,B}, {B,C} | [0,1] | (A∧B)∨(B∧C) = `00010011` (BC AB ABC) | **B** | 3 |
| **F3** | 2 1 3 | {A,B}, {C} | [0,1] | (A∧B)∨C = `01010111` (C BC AC AB ABC) | – | 3 |
| **F4** | 2 1 2 | {A}, {B} | [0,1] | A∨B = `0111` (B A AB) | – | 3 |
| X1 | 1 1 1 | {A} | [0] | A = `01` (A) | – | 2 |
| X2 | 1 1 2 | {A,B} | [0] | A∧B = `0001` (AB) | – | 2 |

**Two outputs (B = 2), always two first-layer cells and two OR cells (c, d)**

| Id | Cascade | Terms | Lines (c; d) | out0 ; out1 | Shared input |
|---|---|---|---|---|---|
| D1 | 2 2 4 | {A,B}, {C,D} | [0]; [1] | A∧B `0000000000001111` ; C∧D `0001000100010001` | – |
| D2 | 2 2 4 | {A,B}, {C,D} | [0]; [0,1] | A∧B ; (A∧B)∨(C∧D) `0001000100011111` | – |
| D3 | 2 2 3 | {A,B}, {B,C} | [0]; [1] | A∧B `00000011` ; B∧C `00010001` | B |
| D4 | 2 2 3 | {A,B}, {B,C} | [0]; [0,1] | A∧B ; (A∧B)∨(B∧C) `00010011` | B |
| D5 | 2 2 3 | {A,B}, {C} | [0]; [1] | A∧B `00000011` ; C `01010101` | – |
| D6 | 2 2 3 | {A,B}, {C} | [0]; [0,1] | A∧B ; (A∧B)∨C `01010111` | – |
| D7 | 2 2 3 | {A,B}, {C} | [1]; [0,1] | C ; (A∧B)∨C | – |
| D8 | 2 2 2 | {A}, {B} | [0]; [1] | A `0011` ; B `0101` | – |
| D9 | 2 2 2 | {A}, {B} | [0]; [0,1] | A ; A∨B `0111` | – |

**Equivalences up to renaming inputs** [K, `fam/enum.py`; the count of labelled versions in brackets].

- Each row above is one class. The labelled forms of a class differ only in which input name goes to which port.
  The counts are: F1 (3), F2 (3), F3 (3), F4 (1), X1 (1), X2 (1), D1 (3), D2 (6), D3 (3), D4 (6), D5 (3), D6 (3),
  D7 (3), D8 (1), D9 (2).
- Examples of members of one class:
  - F2: `(A∧B)∨(B∧C)` = `B∧(A∨C)` (the generator's candidate 1) ≡ `(A∧B)∨(A∧C)` = `A∧(B∨C)`.
  - F3: `(A∧B)∨C` ≡ `A∨(B∧C)`.
  - F1: `(A∧B)∨(C∧D)` ≡ `(A∧C)∨(B∧D)`.
- **No two rows are equivalent to each other** [K, the enumeration's canonical keys are distinct].
- D6 and D7 have the same terms and the same out1. They differ in which term out0 copies, `A∧B` or `C`, so they
  are not equivalent.
- On the bench, renaming is physically empty: every port has its own ideal timing sources [K, `NC/net.py:97-107`].
  So the family should be drawn over **classes** with one fixed labelling and one fixed port assignment each [I].

**Where each feature appears** [I]:

| Feature | Members |
|---|---|
| A shared input (fan-out to two pair ports) | F2, D3, D4 |
| A one-input term (in F: a unary cell, one port at 1.0, section 2.5) | F3, F4, X1, D5 to D9 |
| An OR cell with one selected line, or one line only | X1, X2, every D |
| An OR cell with an unselected but wired line, which must stay silent at its untrained gain | every D |
| A line routed to two OR cells | every D |

### 1.3 The recommended family

**F = {F1, F2, F3, F4}** [I, my recommendation; open choice 9.1], with F3 and F4 built on **unary cells** (2.5).

- **What it is, in one sentence.** Every OR of two incomparable terms of at most two inputs, on three two-port cells.
  It is all the one-output members with two first-layer cells.
- **Seen from the wiring** [K, `fam/rewire.py`, printed].
  - Take every map of the ports a1, a2, b1, b2 to M ≤ 4 inputs that uses every input, with c selecting both lines.
  - The valid maps fall in four classes, by (size of a's term, size of b's term, overlap): (2,2,0) F1, 24 maps;
    (2,2,1) F2, 24 maps; (2,1,0) F3, 12 maps; (1,1,0) F4, 2 maps.
  - The refused maps: (1,1,1), that is `{A}` twice, 1 map; (2,1,1), that is `{A,B}` with `{A}`, 8 maps; (2,2,2), two
    equal terms, 4 maps. They are refused by `Cascade.reachable` [K, `LC/MonotoneTarget.lean:86-89`] [I].
  - **But a map that ties two ports of one cell to one input makes a run that is a sub-run of F1's** (2.5). As
    functions on the circuit, the rewirings give F1 and F2 only.
- **Why it means "a family".**
  - Four distinct functions, on 4, 3, 3 and 2 inputs.
  - Each structural variant of layer 1 appears once: disjoint pair terms (F1), terms that share an input (F2), a
    pair cell with a unary cell (F3), two unary cells (F4).
  - Campaign 6's function is a member. Its frozen evidence gives the code a byte-for-byte regression test (section
    7).
- **Why it can be measured.**
  - The same three cells and the same deck builder.
  - The same nine measure kinds as campaign 6, with one new kind for unary ports: a line scan of a first-layer
    port, plus a read at 1.0 in the deck.
  - Network runs as short as campaign 6's or shorter (section 8).
  - No new Lean theory: the generator already compiled Cascade 2 1 4, 2 1 3 (twice, S2 being `(A∧B)∨C` with a
    unary term) and the Cascade 2 2 4 of S4 [K, `GEND/README.md`, "Synthetic cases (b)"].
- **Why not the D members now** [I].
  - They need a fourth cell and a line routed to two cells.
  - They need a mapping rule for two OR cells sharing one layer dose (section 2.4).
  - Each D member has 5 or 6 crossings, against 4 for F1 to F4. That lowers their expected room share to about 0.12
    to 0.17 [I, a product of per-crossing rates: 0.75 for a pair crossing and 0.65 for a line crossing, from B2's 15
    of 20 and 13 of 20 crossings in their window [K, `BATCH2X_REPORT.json`]; it assumes independent crossings].
  - They are the natural second step once F is measured.
- **Why not X1, X2** [I]. Their OR cell has one line, so it is a copy and no OR is learned. With 2 crossings their
  room share would be about 0.45 to 0.56, by the same product. Mixing them in would raise the family's counts with
  the easiest members.

---

## 2. The circuit per member

### 2.1 What a member changes, and what stays

**Stays as it is** [K for the facts; I that they need no change]:

- **`NC/net.py` `deck`.** It takes any tuple of single-letter cells and gives each port its own timing sources and
  its own pulse amplitude [K, `NC/net.py:57, 97-107`].
- **`NC/net.py` `Session.pulse`** and the simulator pipe.
- **`C5/session4.py` `play`.** It plays any plan of gates, sources and edges. For each FIRE it pushes a pulse for
  every edge of that source whose window contains the FIRE, so one source may feed several ports [K,
  `C5/session4.py:68-74`]. Gates are set by port names of two characters, cell then port [K, `C5/session4.py:86`],
  so cell names must stay single letters.
- **The read-only gate** (`idis` set to 0 three units before a slot) and every timing constant of `DNF/dnf.py`
  (`SLOT` 22, `WINDOW` 1.1, `WIRE` 1.5, `LATENCY`, `SNAP`, `GATE_LEAD` 3, `SEPARATION` 16, `SETTLE` 12, `EXTRA` 3)
  [K, `DNF/dnf.py:20-29`].
- **The 2x design point** (`vhi = 0.7`, `reltol = 1e-5`), applied as `PREPD/dev/batch2x.py` applies it: a rewrite of
  the deck's text in which each name must occur exactly once [K, `PREPD/dev/batch2x.py:7-8, 42`;
  `FUPD/dev/dosedev_tol.py:10-12`]. In a campaign this becomes a frozen wrapper of `net.deck`, not an edit of it.

**Replaced by a member table** [K for the hard-coding; I for the replacement]:

- `DNF/dnf.py` has `INPUTS = dict(A=("a",1), B=("a",2), C=("b",1), D=("b",2))` (one port per input) and `LINES =
  {"a": ("c",1), "b": ("c",2)}` [K, `DNF/dnf.py:18-19`]. They become:
  - **`WIRING`**: input → list of (cell, port). Fan-out is a list of two.
  - **`ROUTES`**: first-layer cell → list of (OR cell, port). Two entries for a D member.
  - **`AMP`**: (cell, port) → amplitude, by the port's kind.
- `C5/plans4.py` builds sources from `dnf.INPUTS[n]` (one port) and edges from `dnf.LINES` [K, `C5/plans4.py:51-61`].
  Its replacement loops over `WIRING[n]` and `ROUTES[src]`.

### 2.2 The members of F, port by port

The port kinds, with their amplitudes:

- **pair**: 0.49, as a and b today [K, `DNF/dnf.py:20`].
- **unary**: 1.0, the line amplitude, on port 1. Port 2 is never pulsed (2.5).
- **line**: 1.0, routed with a delay of 1.5 [K, `DNF/dnf.py:20-23`].

| Member | a | b | c (OR) | Inputs → ports |
|---|---|---|---|---|
| F1 | pair A (1), B (2) | pair C (1), D (2) | line a (1), line b (2) | A→a1, B→a2, C→b1, D→b2 (campaign 6) |
| F2 | pair A (1), B (2) | pair B (1), C (2) | same | A→a1, **B→a2 and b1**, C→b2 |
| F3 | pair A (1), B (2) | **unary** C (1); port 2 never pulsed | same | A→a1, B→a2, C→b1 |
| F4 | **unary** A (1) | **unary** B (1) | same | A→a1, B→b1 |

**The deck changes per member** [I]:

- **The calibration deck** (`plans4.calibration`) reads, at every stage k = 0..7:
  - for a pair cell: empty, port 1, port 2 and both, at 0.49;
  - for a unary cell: empty and port 1, at 1.0 (the same reads c's lines get);
  - for c: unchanged.
  - Today the deck takes the amplitude by cell (`AMP_OR if c == "c" else AMP_AND`) [K, `C5/plans4.py:30`]. It must
    take it by port kind.
- **The network run's plan** (`plans4.network`):
  - Sources: every active input of a slot gives one source per entry of `WIRING`, at its port's amplitude. In F2 a
    pattern with B gives two sources at one date, on a2 and b1.
  - Edges: as today, one per first-layer cell to its port of c, gated on the slot's window.
  - Gates: from the calendar's `writes` (section 3).
- **The scans** (`C6/batch/scan6.py`) take `amp(cell)` and `kinds_of(cell)` by cell name [K,
  `C6/batch/scan6.py:63-68`]. For F3 and F4 they must take them by port kind: a unary cell gets a line scan at 1.0
  ("line1"). The scan itself already takes "a cell, a set of moving ports and a read kind" [K,
  `FUPD/DESIGN_NOTE_WIDEN.md` A.3, on `scan6.py`].
- **The one-sided sets** read a pair cell's ports alone at `W_x + H_x` [K, `C6/drafts/MAPPING_U.md` section 2;
  `scan6.py` docstring]. They are run for every pair cell: in F1 and F2 for a and b, in F3 for a. A unary cell has no
  alone read and needs none.
- **The both-lines FIRE check of c at s = 0**: unchanged, for every member of F, since c always selects two lines.
- **A preset check of each unary port** (new, cheap): one read of port 1 at 1.0 at s = 0, which must be silent, so
  that the need is at least 1. This is the unary analogue of c's both-lines check [I].

### 2.3 The physical fan-out, and what the bench does and does not model

- On the bench, an "input" is not a wire. Each port has its own ideal pulse sources [K, `NC/net.py` docstring
  lines 9-12, `:97-107`]. A shared input is therefore two ideal per-port events at one date and one amplitude, with
  no loading and no coupling between the two ports [I].
- So F2 tests a shared **logical** input with ideal fan-out. It says nothing about one physical driver loaded by two
  ports. The preregistration should say so [I].
- **The unary amplitude.** At 0.49, both ports of a pair cell are needed to reach threshold: in the mapping, a pair
  crosses at `2g + 2d s* = θ` and every alone read of the deck is predicted silent [K, `C6/drafts/MAPPING_U.md`
  section 1].
  - Whether one port at 0.49 could ever cross within the rail and `maxWrites` I did not check. I have no record that
    tries it.
  - At 1.0 a single port is c's regime: at 2x, c's line crossings in the batch lie at 0.66 to 2.40 stages [K,
    `PREPD/dev/batch2x/report/BATCH2X_REPORT.json`, `crossings_in_their_steps`, c1 and c2 of 8301-8310].
  - So I propose 1.0 for a unary port [I]. No input ever drives ports of two amplitudes: a unary term's input belongs
    to no other term, by the antichain condition [I].
  - On the nominal cell, a, b and c are the same circuit with no mismatch: section `tt`, against `tt_mm` for an
    instance [K, `C6/campaign6/net6.py:41`; `C5/c4.py:23`]. So a nominal unary port of a should behave as c's nominal
    line 1. The smoke of 8.1 checks the code path and that equivalence. The physical question proper is on mismatched
    cells (6.2).

### 2.4 The score mapping: what must be generalised

- MAPPING_U anchors layer 1 with one dose `d = θ / 2K`, `help = 0` and per-port `g_x = d (K − s*_x)`. Here `K` is the
  largest of `8 − s*` and `s*` over the pair cells a and b [K, `C6/drafts/MAPPING_U.md` section 1]. The kernel has one
  `dose` per layer [K, `LC/Target.lean:31`].
- **A unary cell on the same `d`** [I].
  - Take `g_u = θ − d s*_u`. Its one-port read then crosses at `s*_u`, and `g_u ≥ 0` whenever `s*_u ≤ 2K`.
  - A unary cell writes one port per silent round, and each pair-cell input is one port too. So **one shared `dose`
    fits both with no change of units** (2.5).
- **F4 has no pair cell**, so `K` must get a rule when layer 1 has none. My proposal: `K = 8`.
- Both points are a **mapping amendment, written before the top-up batch** (6.2). I did not check it against
  MAPPING_U's principle that the model agree with every deck read and with the one-sided bound.
- **For a D member** [I], layer 2 has one dose for two OR cells. `d_c = θ / (s*_1 + s*_2)` per cell [K, MAPPING_U
  section 1] would then be replaced by:
  - `d_2 = min_i θ / S_i`, where `S_i` is cell i's sum of crossings;
  - `help_i = θ − d_2 S_i ≥ 0`;
  - `g_ip = d_2 s*_other`.
  - This is a second amendment, for D members only. It gives a non-zero help, which no campaign has used.

### 2.5 Two ways to make a one-input term, and why the cheaper one is rejected

There are two physical realisations of a term `{C}` on a two-port cell: (i) **tied**, both ports of a pair cell on C
at 0.49; (ii) **unary**, one port on C at 1.0.

**(i) Tied is a sub-run of F1** [K for the comparison, `fam/subrun.py`, printed; I for what it implies].

- The script takes F1's port wiring (A→a1, B→a2, C→b1, D→b2) and each tied member's wiring:
  - F2 with B on a2 and b1;
  - F3 with C on b1 and b2;
  - F4 with A on a1 and a2, B on b1 and b2.
- It compares the set of ports each slot pulses: layer-1 training, the lessons, every test pattern.
- **F3 tied and F4 tied: every slot pulses exactly the port set of one of F1's slots.**
  - Tied F3 is F1 with C = D. Its 8 test patterns are 8 of F1's 16.
  - Tied F4 is F1 with A = B and C = D. Its 4 test patterns are 4 of F1's 16.
  - The training slot and the two lessons are F1's own.
- **F2 differs from F1 only in its two lessons**, `{a1, a2, b1}` and `{a2, b1, b2}`. Those are the partial teaching
  reads, and nothing else.
- So, as the coordinator read it, and I confirm:
  - tied members need no new Lean and no new measure;
  - for F3 and F4 they test nothing beyond F1. A tied run is F1's run with test slots left out. Its slots differ from
    F1's only in number and order, and that order matters only through the read-only tests, which claim G covers;
  - F2 adds only the partial teaching reads.
- In Lean this is the substitution pattern of `TwoRails` [K, `LC/TWO_RAILS.md` and
  `LC/TwoRails.lean`, `every_function_on_two_rails`, on `main`]. F1's statement holds on all 16 patterns, so it holds on the
  substituted subset. I did not write that derivation.
- **A remark of my second version is withdrawn.** I wrote there that a units rule (pair cells doubled) lets Lean
  express a tied cell as one input. The rule itself holds, by the homogeneity of `robustFire` and `robustSilence`
  [K, `LC/Target.lean:53-55`]. But it is not needed: F1's own Cascade 2 1 4 already covers a tied run.

**(ii) Unary is the family's one new physical element.**

- **The cell's read.** One port at 1.0. No first-layer cell has done this; c's lines have, as layer 2 [K, the batch].
- **Measures.** A deck read at 1.0 per stage, a unary scan, and the preset check (2.2).
- **Mapping.** The amendment of 2.4.
- **Lean.** It is expressible exactly with no change.
  - The unary cell's term has one input on one port. A silent round writes once on it, as on each input of a pair
    cell, so the shared layer `dose` fits (`portWrites`, `gain` [K, `LC/Target.lean:36-40`]).
  - `checkConjunctions` accepts a target of one input [K, `LC/MonotoneTarget.lean:79-82`].
  - The generator compiled `(A∧B)∨C` with a unary term, S2 [K, `GEND/README.md`].
- **Noise budget.** A one-port budget, as a line of c.
- **Partial reads.** None.

**Recommendation: (ii), unary at 1.0** [I]. The tie route is cheaper, but it re-measures F1 and makes F3 and F4
empty as tests.

### 2.6 What each member tests physically

Each slot is written as **(writers, pulsed ports, amplitude)** and compared with campaign 6's F1 run [K,
`fam/slots.py`, printed]. Every port is at 0.49 unless marked @1.0. F1's slots are:

- **L1**: a and b write; ports {a1, a2, b1, b2}.
- **lesson a**: c writes; ports {a1, a2}.
- **lesson b**: c writes; ports {b1, b2}.
- **16 tests**: nobody writes.

| Member | Layer 1 | Lesson a | Lesson b | Tests | Slots not in F1 |
|---|---|---|---|---|---|
| F2 | {a1, a2, b1, b2} = F1 L1 | {a1, a2, b1}: pulses as F1's test ABC, but c writes | {a2, b1, b2}: pulses as F1's test BCD, but c writes | 8, each one of F1's tests | **2** (the two lessons) |
| F3 tied | = F1 L1 | = F1 lesson a | {b1, b2} = F1 lesson b | 8, each one of F1's tests (C → CD) | **0** |
| F4 tied | = F1 L1 | {a1, a2} = F1 lesson a | {b1, b2} = F1 lesson b | 4, each one of F1's tests (A → AB, B → CD) | **0** |
| F3 unary | {a1, a2, b1@1.0}: new | = F1 lesson a | {b1@1.0}: new | 2 of 8 as F1 (-, A, B, AB), 4 new | **6** |
| F4 unary | {a1@1.0, b1@1.0}: new | {a1@1.0}: new | {b1@1.0}: new | 1 of 4 as F1 (-), 3 new | **6** |

**The coordinator's reading is confirmed** [K for the tables; I for what follows].

1. **With ties, F3 and F4 are F1's run, slot for slot, with fewer tests.** They test nothing physically beyond F1.
   - Their Lean gates are F1's Cascade 2 1 4 restricted to the tied patterns, a corollary of the `TwoRails` kind.
   - I did not write that corollary; the generator could also compile them directly.
2. **The paired design repeats F1's run for tied F3 and F4.** It adds compute, not evidence.
3. **Under ties, the only physically new member is F2, and only through its two lessons.** They pulse what F1 pulses
   in its tests ABC and BCD, but with c writing.
   - Physically, this is a first-layer cell receiving one port alone, gated read-only, while c learns.
   - In F1 that read happens only in the read-only tests.
4. **So under ties the honest family is "F1 and F2, with F3 and F4 as relabelings of F1".** A family whose members
   are physically distinct needs realisation (ii), a first-layer cell learning from one port at 1.0. It needs new
   measures and the mapping amendment of 2.4.

**The two designs side by side, for the owner** [I; costs from section 8]:

| | **T: ties** | **U: unary cells (recommended)** |
|---|---|---|
| Physically distinct members | F1, F2 (F3, F4 are relabelings of F1) | F1, F2, F3, F4 |
| What is new beyond campaign 6 | F2's partial reads while c is taught | that, plus a first-layer cell learning from one port at 1.0 (F3, F4) |
| Honest claim's scope | "two functions; two more as relabelings" | "four functions" |
| New measure kinds | none | a deck read at 1.0 per stage; a unary scan; a preset check |
| Lean | nothing new: F1's cascade, or the generator, for each member | nothing new in theory; the mapping amendment (2.4) in the prediction code |
| De-risking smoke | F2, one run without noise on the nominal cell: about 500 to 1 300 s | a unary port on the nominal cell, about 1 970 s of runs (8.1), or on 8303, about 3 200 s; plus the F2 smoke |
| Development runs | none: each member's gates on B2's measures (needs B2's waveforms, about 6.6 GB) | top-up of B2: 46 460 s (6 runs per instance); or a fresh batch of 10 at 8 254 s each: 82 540 s, E about 31 400 s |
| Campaign at size (a), drawn | I = 16, measures 16 × 6 476 s, E about 39 400 s; network as U's; **total about 50 600 to 62 400 s** | I = 16, **total about 48 000 to 60 000 s** (8.4) |
| What the noise claims can count | about 3 instances with room in all, the same instances for every member | about 3 in all; room differs by member |
| Main risk | a family in name only, for F3 and F4 | the unary cell may have little room, or none, on mismatched cells |

The fresh batch costs about 1.8 times the top-up and measures F1's runs again, which B2 already holds [I]. So for U
I recommend the top-up, after the smoke.

---

## 3. The calendar and the training premises

### 3.1 The calendar of a member

From `DNF/dnf.py:42-63` [K], made general [I]:

1. **Layer 1, one slot per round**, `max(needs of layer 1) + EXTRA` rounds.
   - All first-layer cells write.
   - The stimulus is the **union of the targets**: ABCD for F1, ABC for F2 and F3, AB for F4.
   - Each cell then reads exactly its own target, since a cell sees only its wired inputs (section 1.1).
   - This is campaign 6's rule, "layer 1, both cells in one slot" [K, `DNF/dnf.py:49-50`].
2. **Layer 2**, `max(needs of the lines) + EXTRA` rounds. Each round has one slot per selected line, in line order.
   - The stimulus is the line's target.
   - Only c writes. Every first-layer port is gated read-only.
3. **Tests.** The `2^M` patterns, read-only. Then the skew slots, one per pair term, with the second input 2 units
   late.

### 3.2 Where a partial pattern can occur

- **During layer-1 training: never** [I].
  - Every first-layer cell gets its full target in every training slot, because the union is presented.
  - The alternative, one first-layer cell per slot, would give b the read "B alone" while its writes are enabled.
    A silent read with writes enabled doses every port that received a pulse [K, `MONOTONE_DNF.md`: "a silent read
    doses every active target port"]. That would add a write the Lean count of layer 1 never sees: its count is
    rebuilt from that cell's own `firstTrain` reads only [K, `LearningCertificate`, `LC/TwoLayerTarget.lean:135-139`].
  - **So the calendar must keep one shared slot per round for layer 1.**
- **During layer-2 teaching: yes, in F2** [I].
  - Lesson "line a", stimulus AB: b receives B alone.
  - Lesson "line b", stimulus BC: a receives B alone.
  - In F1, F3 and F4 the cell not taught receives nothing, because no input is shared.
- **During tests: yes, in every member.** These are the patterns that are not a target (for example A alone in F1).
  Campaign 6 already made these reads [K, `C5/predicted.py:415-426`, `firstTest` rows by `mask_read`].

### 3.3 What `TrainingSeparation` and the calibration premises must show

**`TrainingSeparation`** is a statement about dates and durations only [K, `LC/MonotoneTarget.lean:145-159`]:

- layer-1 rounds are separated by the layer-1 duration;
- every `teach` read and every `secondTrain` read starts after the last layer-1 round;
- each lesson's reads end before any later lesson's reads start;
- every test starts after all of these.

Its rows already include one `teach` read per first-layer cell and per lesson ("∀ a"). In campaign 6 the row of the
cell not taught was an empty read at the lesson's start [K, `C5/predicted.py:404`: `rd(start, arr1(start,
TARGET[line]), [], Z(c, n[c], "empty"))`].

**In F2** [I]:

- The dates of that row are unchanged (start = the lesson's slot date). So `TrainingSeparation` changes in no date,
  and the kernel checks it on the predicted dates as before.
- What changes is the row's **content**:
  - the score becomes `Z(b, n_b, "port 1")` instead of `"empty"`;
  - the arrivals stay `arr1(start, {A, B})`, since inputs not wired to b are gain-0 Lean ports.
- So the prediction code must produce that row from `WIRING` (`mask_read` of the wired ports). Today it writes
  `"empty"` by construction.

**The calibration premise of that row.** `CascadeTrainingCalibration` requires a `CalibratedAdditiveRead` of every
first-layer cell on the taught line's pattern, at its settled count, with its **testing** error [K,
`LC/MonotoneSupport.lean:14-16`; `FUPD/DESIGN_NOTE_WIDEN.md` A.4, candidate 1]. For b's row in F2 this means:

- the read B alone, at b's trained stage, has a residual within b's testing error;
- its FIRE bit is its threshold comparison: it is silent;
- its pulse arrives within the skew bound.

**What makes it hold** [K for each premise, I for the conclusion]:

- `negativeMargin` already requires every pair cell to be robustly silent, with its testing error, on each target
  pattern minus one port, at its need [K, `LC/Target.lean:91-93`, used by `checkConjunctions`]. For b that is B alone.
- `Cascade.reachable` requires b to be predicted silent on AB [K, `LC/MonotoneTarget.lean:86-89`].
- **The one-sided set of b** reads each port alone at `W_b + H_b` stages and must find it silent. That is the bound
  this read uses [K, `C6/drafts/MAPPING_U.md` section 2]. Since `W_b = s*_b + K` and the read happens at about
  `n_b` ≈ 2 to 3 stages, the margin is about `K` stages, roughly 5 to 6 at 2x [I, from `K = max(8 − s*, s*)` and
  the batch's `s*` of 1.47 to 2.44 [K, `BATCH2X_REPORT.json`]].
- So **the one-sided sets must show exactly what they show today**: silence of each port alone at `W + H`. F2 adds
  no new measured bound. It uses an existing bound in a new place, during teaching.

**The bench's hypotheses H** [I, arithmetic]:

- In F2 each pair cell is pulsed in every teaching slot, not in every other one.
- Slots are 22 units apart. The least separation between pulse groups on one cell becomes `22 − SNAP` ≈ 21.98,
  above `SEPARATION` = 16 [K, `DNF/dnf.py:21, 25, 27`].
- Settlement is unchanged: the partial pulse is at the slot's start, like every other external pulse
  (`settled`, `DNF/dnf.py:98-103`).
- The general `separation` and `settled` must be computed from `WIRING`, which `pulses` does not do today [K,
  `DNF/dnf.py:66-79`, `INPUTS[n]` gives one port].

### 3.4 Can a stored voltage move during another cell's lessons?

**By design it should not** [K for the mechanism]:

- Every port of a cell not addressed by the slot has its dose current `idis` at 0 from 3 units before the slot [K,
  `C5/session4.py` docstring; `C5/plans4.py:11-13`; `DNF/dnf.py:26`].
- A gated read does not dose.

**What is known.**

- [K, `FUPD/NOISE_AUDIT.md:123-135`]: over 72 port-runs of campaign 6's attempt c1, "within a run, after the last
  write", the stored voltage moved by "below 0.0001 mV" (standard deviation). "Once a port has stopped writing, its
  stored voltage does not move during the rest of the run."
- That rest of the run included gated one-port reads: the tests such as A alone [I].
- At 1x a dose is about 1.35 mV, at 2x about 2.7 mV [K, `PREPD/CAMPAIGN7_PROTOCOL_DRAFT.md` "In one page"]. So
  0.0001 mV is about 0.004 % of a 2x step [I].
- **Not measured at 2x and `reltol = 1e-5`**, where no network run has been made [K, the draft's section 6: "No
  network run exists at `1e-5`"].

**How it is accounted for.**

- **Claim G already covers it.** Campaign 5's G reads: "In every run without noise, across every gated read, no
  stored voltage moves by more than 0.01 mV, and no write and no write' rises. In every noisy run, across every
  gated read, no write and no write' rises. One gated read that fails refutes G" [K, `C5/PREDICTION.md:569-571`, on
  `IMPL`].
  - F2's partial teaching reads are gated reads, so G judges them with no new rule.
  - I propose only that the analysis **reports them as their own subset of G**: per member, the gated reads during
    teaching on a cell not taught.
- **In the Lean premise**, any small move would enter the residual of the teaching row's `CalibratedAdditiveRead`,
  inside the testing error [I]. 0.01 mV is about 0.4 % of a 2x step, against a K3 budget of about 16 % of a step
  [K, `BATCH2X_REPORT.json`, `budgets_stages_K3`, about 0.164].
- **A hidden write is what G is for.**
  - A write in a slot where the port is gated would be about 2.7 mV.
  - The words would not always show it. Layer 1's count in the Lean model is rebuilt from its own training reads
    only, and the extra gain might flip nothing [I].
  - G's "no write rises" is the check that sees it [K, the same lines].

**In the rehearsal** (section 8.3): one run without noise of F2 is the first test of G on partial reads at 2x and
`1e-5`. If G fails there, the shared input is not ready, and the family falls back to F1, F3, F4 (open choice 9.1).

---

## 4. The draw

**Proposal** [I]:

- **Seeds.** I fresh instance seeds in a new range. I propose 8501 upward. The draft reserved 8401-8415 and the
  noise seeds 84 011 to 84 153 [K, the draft's section 1 and section 4]. Whether 85xx is free I did not check;
  campaign 6's search should be rerun.
- **Balanced allocation.** Each member of F gets `I / |F|` instances. `I` is a multiple of `|F|` under both sizes
  of 6.3.
- **The draw.**
  1. Sort the seeds by `SHA-256("kernel-R family draw 1|" + str(seed))`, with the seed in decimal ASCII.
  2. Walk the sorted list, assigning members in the declared order F1, F2, F3, F4, F1, …
  3. The result is a uniform random permutation of the balanced multiset, given the seeds and the salt [I]. It uses
     no Python random generator, whose streams depend on the version.
- **Published before any measure.** `FAMILY.json` (each member's cascade, wiring and truth table), `DRAW.json` (seed
  → member) and `draw.py`, with their SHA-256. They go in the preregistration's commit, before any run of any
  campaign seed.
  - The salt is fixed in this note now.
  - The draw's only inputs are the seed list and the salt. It cannot see a measure, since none exists [I].
- **What a seed fixes.** The seed fixes the cells' mismatch; the draw fixes the wiring. The two are independent
  [I].

**Alternatives** (open choice 9.3):

- **Weighted allocation** `n_m ∝ 1 / r_m` (section 6). This equalises each member's expected number of instances
  with room. It makes the member with the fewest expected the most frequent.
- **An independent uniform draw per seed.** This is the plainest "drawn at random", but it can give a member 0 or 1
  instance by chance [I].
- **The paired design (open choice 9.13).** Every member's network runs on every instance, which departs from the
  owner's decision of a draw. Under it, a draw is still useful for one thing: the order in which the members' runs
  are made on an instance, so that no member always runs first on a machine [I].

I recommend the balanced draw: it keeps every member's primary claim countable.

---

## 5. The claims over the family

Each claim keeps campaign 6's definition [K, `C6/PREDICTION.md:198-249` on `main`], applied per member with its
own ports and its `2^M` patterns.

### 5.1 The primary claim (without noise)

**Wording, proposed** [I]:

> **Primary claim.** For each member f of F = {(A∧B)∨(C∧D), (A∧B)∨(B∧C), (A∧B)∨C, A∨B}, on every counted eligible
> instance assigned to f by the published draw, in its run without noise:
>
> - **L1:** every learning port of layer 1 writes `need` letters `s`, then `F`.
> - **L2:** every selected line of c writes `need_c` letters `s`, then `F`.
> - **T:** on the `2^M` test patterns, each first-layer cell fires exactly on the patterns containing its term, and
>   c fires exactly on f.
>
> The letters and outputs are those predicted before the run from per-cell measures. The outputs are derived by
> `two_layer_monotone_recognition_one_sided` in that instance's Lean gate.

**Decided as follows:**

- **Refuted** by one letter or output that differs, on one counted instance of any member.
- **Established for the family** when it holds on every counted instance, with **at least N_P = 8 counted instances
  in total and at least 2 on each member**.
- **Per member:**
  - "established for f" with 2 or more counted instances;
  - "held on one instance of f, not established for f" with 1;
  - "not established for f" with 0.
- **If some member has fewer than 2**, the family-level verdict is worded on the members that reached 2. It reads
  "established on the members …; for f, …". It never reads "for every function of F". Every counted instance still
  counts in the total, and its failure still refutes.

### 5.2 The noise claims

**N-out of c, per member and pooled** [I]:

> Under the injected noise model with decision 5's constants (`b` 0.111, `w` 0.094, `d` 0.009 mV), on every counted
> noisy run, c answers all `2^M` patterns with f.

- **Counted runs**: as campaign 6. An output of c counts only when c and every first-layer cell of the instance
  have room at K = 3, c's room taken with the one-port testing error [K, `PREPD/CAMPAIGN7_PROTOCOL_DRAFT.md`
  section 5].
- **Refuted** by one pattern answered otherwise in one counted noisy run, on any member.
- **Established for the family** when its counted runs come from **at least N_N instances in total, from at least
  2 members**. N_N = 4 under the size 6.3(b), N_N = 2 under 6.3(a) (section 5.3).
  - The wording names those members: "established, pooled over …".
  - It does not say "for every member".
- **Per member**, as for 5.1:
  - "established for f" (2 or more instances);
  - "held on one instance of f, not established" (1);
  - "not established for f" (0).
- **N-out of the first-layer cells, and N-own and N-word per port**: the same rule, with the same minimum N_N in
  total, each member reported.
- **Controls**:
  - **U**, the untrained run: one per member. This is my proposal; campaign 6 had one per campaign [K,
    `C6/PREDICTION.md` §5.6]. The calendar differs per member.
  - **S**, the skew slots: per pair term.
- **Declared comparisons** M1 to M8: as campaign 6, reported per member.

**What is expected, stated before any data** [I, at a room rate of 0.2 for the draw, and the product model's 0.24,
0.24, 0.21, 0.18 for the paired line (6.1)]:

| Design | Instances with room | Pooled noise claim | Members with ≥ 2 counted noisy instances |
|---|---|---|---|
| Draw, I = 16 (6.3a), N_N = 2 | about 3 | P(≥ 2) ≈ 0.86 | about 0.7 of 4 (4 instances each) |
| Draw, I = 32 (6.3b), N_N = 4 | about 6 | P(≥ 4) ≈ 0.91 | about 2.0 of 4 (8 instances each) |
| Paired, I = 16, N_N = 2 | about 3 to 4 per member | P(≥ 2) ≈ 0.81 to 0.93 per member | about 3.5 of 4 |

The probabilities are binomial [K, my computation; I for the rates]: n = 16 or 32 at p = 0.2, and per member n = 4
or 8 under the draw and n = 16 paired.

**So under a draw the per-member noise lines will mostly read "held on one instance" or "not established".** This is
the size's consequence, written now.

### 5.3 Why N_P = 8, and N_N = 2 or 4

- **N_P.** Nearly every instance is expected eligible (10 of 10 in the batch [K, `BATCH2X_REPORT.json`, `k_elig`]).
  At I = 16 the primary claim will have about 4 counted instances per member, and at I = 32 about 8. N_P = 8 with 2
  per member is a floor that only an ineligible or failed member can miss [I].
- **N_N.**
  - At I = 32, N_N = 4: twice campaign 6's minimum of 2, because the claim pools four functions.
  - At I = 16, N_N = 2: campaign 6's own minimum. That is all the size supports.
  - A larger N_N needs a larger I (section 6) [I].

### 5.4 The claims under the paired design (open choice 9.13)

- Every eligible instance has a run without noise **of every member**. Every instance with room has the noisy runs
  **of every member**.
- Each member's claims are then judged on all instances, exactly as campaign 6's were. The family claims are the
  conjunction over members.
- One wrong answer on any member's run refutes that member's claim and the family claim [I].
- The minimum of 2 instances applies per member.
- It needs the superset measures on every instance (8.4).

---

## 6. Room per member, and the size

### 6.1 Room is a property of crossings, and crossings are properties of cells

- **Where room comes from.** A scan measures a cell alone ("Only the scanned cell receives pulses") [K,
  `C6/batch/scan6.py` docstring line 7]. A cell's room at K = 3 depends on where its crossing falls in its step,
  against its budgets [K, `FUPD/DESIGN_NOTE_WIDEN.md` B.1; `BATCH2X_REPORT.json`, `crossings_in_their_steps`].
  - The member decides only which crossings an instance needs [I].
  - Every member of F needs 4: F1 and F2 need 2 pair and 2 line; F3 needs 1 pair and 3 line; F4 needs 4 line. A
    unary crossing is counted as a line crossing.
- **In B2** [K, `BATCH2X_REPORT.json`, by my reading of `in_its_window` per crossing, 8301-8310]:
  - pair crossings in their window: 15 of 20 (a 8, b 7);
  - line crossings: 13 of 20 (c1 7, c2 6);
  - in all, 28 of 40, which matches the report's `"crossings": {"n": 40, "in_their_window": 28}`;
  - `k_all3` = 2 of 10 (8303, 8306), under the one-port rule.
- **A product model** [I, assuming independent crossings, which 10 instances cannot test]:
  - F1 and F2: 0.75² · 0.65² ≈ 0.24;
  - F3: 0.75 · 0.65³ ≈ 0.21;
  - F4: 0.65⁴ ≈ 0.18;
  - the family, balanced: ≈ 0.20.
- **F2's room equals F1's on the same cells** [I]. Its extra partial teaching read uses the same bound,
  `negativeMargin` at the testing error, as a partial test read F1 already has. So on B2, `r_F1 = r_F2 = 2`.
- **F3's and F4's room shares a, b or c's crossings with F1, but adds the unary crossings of a and b.** It is not
  known for any instance.

### 6.2 The development runs: top B2 up with the unary measures

- **What is missing** [K for what B2 holds; I for the rest]. B2 measured each of 8301-8310 for F1: two decks, two
  pair scans, two line scans of c, the both-lines check and two one-sided sets [K, `PREPD/README.md`]. A unary member
  needs, per cell that may be unary:
  - the deck's read of port 1 at 1.0 at every stage;
  - a unary scan;
  - the preset check.
- **The top-up, per instance** [I]:
  - a guard-on and a guard-off deck with the extra reads. A deck's dose `D_p` is needed by the scan, and a second
    deck gives a free check against B2's: with the same seed and deck, the stored-voltage doses should agree;
  - a unary scan of a and of b at 1.0, with `D_p` from the new guard-on deck;
  - the preset check of a and of b.
  - In all, 6 runs.
- **With it, every instance of B2 gives a room verdict for every member**, paired across members:
  - for each of 8301-8310 and each member, the general path (section 7) computes the member's prediction and its
    gate at K = 0 and K = 3, and reports `r_m`;
  - F1 and F2 use B2's runs as they are;
  - F3 and F4 use the top-up's deck reads at 1.0 and its unary scans, with B2's pair, line and one-sided runs.
- **B2's waveforms** are needed by campaign 5's `predicted.load`, which reads each deck's `evidence/trace.raw` and
  `result.json` [K, `C5/predicted.py:447-459`]. B2's run folders on `PREP` hold only `record.json`, `DOSEDEV.json`
  and `noise.sha256` [K, `ls`].
  - The waveforms were meant for `evidence/learned-dnf-circuit-campaign-7-prep` [K, `PREPD/README.md`], which exists
    at `85199862` [K, `git ls-remote`].
  - Its tree (fetched by branch name, without blobs) holds, for example,
    `research/learned-dnf-circuit-campaign-7-prep/evidence/batch-8303/8303-cal-on/evidence/` with `result.json` and
    `trace.raw` in two parts, `trace.raw.part-000` (90 000 000 bytes) and `part-001` [K, `git ls-tree`]. In all it
    lists 158 `trace.raw` parts [K, same].
  - I did not fetch the blobs, join the parts or check them against `RUNS_SHA256SUMS`.
- **Why not a fresh batch.** A fresh batch would measure F1's runs again, which B2 already holds at the design point.
  Topping up keeps the members paired on the same ten instances, at about half the cost of a fresh batch (8.2) [I].
- **The partial teaching read of F2** is seen only in a network run. It is the subject of the rehearsal's F2 run
  without noise (8.3). It can be run earlier, on the nominal cell, as the stopped session proposed.

### 6.3 The size

**The difficulty** [I]. F1's and F2's room on B2 is known (2 of 10); F3's and F4's is not. The owner's rule written
before B2 reads: "A campaign 7 on this design is sized on `k_all3` … `I = ceil(30 / k_all3)` … If `k_all3` is 0 or 1
of 10, no campaign follows on this design" [K, `PREPD/BATCH2X_PLAN.md` §8]. Its author read "this design" as
campaign 6's function at twice the dose [K, same section].

**Two options for the owner** (open choice 9.7):

- **(a) The rule as written, by member.** For each member m, `r_m` from 6.2.
  - A member with `r_m` ≤ 1 is removed before the draw, as the rule says for its own design. If fewer than 3 members
    remain, no campaign.
  - Then `I = ceil(30 / min_m r_m)` over the members kept, rounded up to a multiple of their number. With r_m = 2
    for all four, I = 16.
  - For F1 and F2 this is the pre-B2 rule exactly. For F3 and F4 it is that rule applied to counts not yet seen,
    written before the top-up's first run.
  - N_N = 2 pooled (campaign 6's minimum). With about 3 instances with room, a larger N_N would likely fail (P(≥ 4)
    = 0.40 at a rate of 0.2, n = 16 [K, my binomial computation]).
- **(b) A family rule written before the top-up**:
  - `I = |F'| · max(3, ceil(10 · E / R))` with `R = Σ r_m`, `E = 6`, and the cap I ≤ 32;
  - with r_m = 2 for all four, I = 32, and N_N = 4.
  - A member with `r_m` ≤ 1 is removed; if fewer than 3 members remain, no campaign.
  - Its F1 and F2 terms are known before it is written. That is to be said in the rule.

**My recommendation: (a)** [I]. It stays nearest to the one rule written before any data, and its cost fits the
draft's bound (8.4).

---

## 7. The code: one general path

### 7.1 The shape of it

- **One member table**, `FAMILY.json`: per member, its cascade (terms, lines, M) and its wiring (`WIRING`, `ROUTES`,
  port kinds). Everything that depends on the function is derived from it, by rules and not by cases.
- The **member object** (`topology.py`, new, about 250 lines [G]) gives:
  - the cells and their kinds;
  - the amplitude of each port;
  - the calendar for given needs, with `pulses`, `separation`, `settled` and `zero_error` made general;
  - the truth table and the patterns in mask order;
  - the measure run list of an instance (its pair, unary and line crossings, its one-sided sets and preset checks);
  - the list of crossings and one-sided sets.
- **The path**, stage by stage:
  1. member table;
  2. deck plans;
  3. measures;
  4. mapping anchors;
  5. prediction (needs, budgets, the observation in `TraceTables` order);
  6. generator spec;
  7. Lean gate;
  8. network plans;
  9. analysis (words, outputs, G, H, N-claims, with one report per member and the family verdicts).
- **No per-function special case.** Two tests are proposed [I]:
  - **(a) Regression.** The general path on F1, with campaign 6's 1x design point and attempt c1's evidence,
    reproduces byte for byte:
    - `dnf.calendar`'s slots;
    - `plans4.network`'s plans;
    - `C6/stages/c1/PREDICTED.json`;
    - the four `Gate6_*.lean`.
    - The generator already reproduces the gate files [K, `GEND/README.md` test (a)].
  - **(b) Coverage.** The path runs on all 15 shapes of section 1.2 with the generator's synthetic observations (`synth.py`)
    and compiles each gate. Section 1.1's two-port rule is the only refusal allowed.

### 7.2 Every frozen file that hard-codes the function

Line counts [K, `wc -l` on `IMPL` and `PREP`]. The new sizes are my guesses [G].

| File (lines) | What is hard-coded [K] | Needs | New size [G] |
|---|---|---|---|
| `DNF/dnf.py` (199) | `INPUTS`, `LINES`, `truth`, `patterns`, `calendar`, `pulses`, `zero_error`, `cost` | **Generalised replacement** (`topology.py`). Its constants are imported unchanged | ~250 |
| `C5/c4.py` (128) | `CELLS = ("a","b","c")` (line 22), the amplitudes by cell | **Thin wrapper**: the constants re-exported, the cells from the member | ~30 |
| `C5/plans4.py` (63) | sources from `dnf.INPUTS`, edges from `dnf.LINES`, amplitude by cell | **Generalised replacement** | ~90 |
| `NC/net.py` (220) | nothing about the function | **Unchanged**; plus a frozen wrapper for `vhi`, `reltol` (as `batch2x.py` does) | ~40 |
| `C5/session4.py` (104) | nothing | **Unchanged** | 0 |
| `C5/predicted.py` (634) | `LAYER1`, `LAYER2`, `TARGET` (lines 47-49), `needs`, the budget rule of c, `room`, `learning_ports`, `observation` (letters ABCD; teach row "empty", line 404) | **Generalised replacement** of those functions. The exact arithmetic is kept and imported (`solve`, `ceil_sum_sqrt`, `noise_square`, `read_budget`, `sensitivity`) | ~450 |
| `C5/gate4.py` (215) | `Cascade 2 1 4` (line 51), `lines := fun _ _ => true` (line 61), the tables | **Replaced by the generator** (`GEND/spec.py` 197, `emit.py` 278, `mirror.py` 334, to freeze), plus an adapter from prediction to spec | ~60 |
| `C5/check.sh` (116), `cases.py` (509), `mirror_mutations.py` (242), `expected/` | the fixtures are F1 cases | **Unchanged**: check.sh accepted the generic `Synth_S1` as is [K, `GEND/README.md`]. Per-member synthetic cases are added as separate tests, not into check.sh | 0 (+ tests) |
| `C5/reads4.py` (137) | the six named ports | **Generalised replacement** (ports from the member) | ~150 |
| `C5/analyze.py` (493), `C6/campaign6/analyze6.py` (230) | `word_claims`, `n_own` over six ports, the 16 patterns, M4, M8's observation | **Generalised replacement**, with per-member reports and the family verdicts of section 5 | ~550 |
| `C5/run4.py` (234), `C6/campaign6/net6.py` (82) | `c4.CELLS`, needs `a,b,c1,c2`, the seed guard | **Thin wrapper** (`netF.py`): the member's cells and needs, the new seed guard | ~110 |
| `C6/batch/scan6.py` (306) | `amp(cell)`, `kinds_of(cell)` (lines 63-68) | **Thin wrapper**: amplitude and kinds by port kind; the preset check of a unary port | ~60 |
| `C6/batch/predict6.py` (400) | `CROSSINGS`, `NEEDS`, `BOTH`, `ALONE`, `anchors` (the pair rule and c's rule), decoder clauses | **Generalised replacement**, with the mapping amendment of 2.4 | ~450 |
| `C6/batch/schedule6.py` (249), `C6/campaign6/stages6.py` (356), `inputs6.py` (108), `meas6.py` (148) | the nine measure runs per instance and their dependencies; machines `a`, `b` | **Generalised run lists**, from the member, plus thin wrappers. The three-pair layout as the draft proposes [K, draft §6] | ~200 |
| `C6/campaign6/predicted6.py` (166), `c6.py` (181) | seed lists (`c6.py:51-53`), the record per instance | **Thin wrappers**: new seeds, `DRAW.json` checked at every runner | ~150 |
| `PREPD/dev/batch2x.py` (323), `batch2x_report.py` (146) | development code for F1 | **New versions**: the smoke and the top-up's runs (8.1, 8.2), and a report of each member's prediction and gate on B2 plus the top-up | ~250 + ~200 |
| launch kit, `marker_check.py`, `publish_evidence.py`, `diskcheck.py`, `collect.py`, `noisemodel.py` | the seed lists and machine names only | **Reused**; machine names as the draft's three pairs | small |

**In total** [G]: about 2 900 lines of new campaign code, and about 1 500 lines of tests. `SECOND_FUNCTION_DESIGN.md`
estimates about 750 lines of code and 900 of tests beyond the campaign 7 code list, for one more function. The two
figures count different things: mine counts the whole general path from campaign 6's files, theirs the addition to a
campaign 7 code list I have not seen. I did not reconcile them. The single largest piece is
the prediction (`predicted.py` together with `predict6.py`). Lean: no theory, no edit of `LC/`.

---

## 8. Costs

**Figures used** [K, `PREPD/CAMPAIGN7_PROTOCOL_DRAFT.md` §6, the batch's means at the design point, `1e-5`]:

- Measure runs: guard-on deck 1 662 s, guard-off deck 1 206 s, pair scan 701 s, line scan 600 s, both-lines check
  54 s, one-sided set 476 s.
- Nominal smoke runs at 2x and `1e-5`: guard-on deck 1 128 s, guard-off deck 715 s, both-lines check 50 s, one-sided
  set 323 s [K, `record.json` `wall_s` of `PREPD/dev/batch2x/smoke/none-smoke-*`].
- Network runs, which are the draft's estimates, never measured at `1e-5` [I there]: run without noise 689 to
  1 292 s, noisy run 1 179 to 2 676 s, untrained run 185 to 277 s.

**My assumptions** [I or G as marked]:

- **A unary scan costs a line scan, and a preset check costs a both-lines check** [G].
- **A deck with the extra reads at 1.0 costs 7/6 of a deck** [G]: one more read slot per stage, 7 slots against 6.
- **A network run's cost goes with its number of slots** [G]. Needs are 2 or 3 at 2x [K, the batch]. That gives
  about 34, 26, 25 and 20 slots for F1 to F4, so factors of 1, 0.76, 0.73 and 0.59, about 0.77 on average [I].
- **The kit's expected compute E** is taken as 0.38 × the run time for measure stages and 0.65 × for network
  stages. These are the ratios of the draft's own E to its run times [I: 12 357 / 32 380 and about 21 000-44 000 →
  13 700-28 800].

### 8.1 The first step: a nominal smoke of a unary port

**Runs** (nominal cell, 2x, `1e-5`; development, counts nothing) [I]:

| Run | Run time |
|---|---|
| A guard-on deck with the extra reads (port 1 of a and of b at 1.0, every stage) | about 1 320 s (1 128 × 7/6) |
| A unary scan of a, port 1 at 1.0 | about 600 s |
| The preset check of a: port 1 at 1.0 at s = 0, which must be silent | about 50 s |
| **In all** | **about 1 970 s of runs, about 1 320 s of wall time** |

The scan and the check take `D_p` from the existing nominal guard-on deck's `DOSEDEV.json`
(`PREPD/dev/batch2x/smoke/none-smoke-cal-on/`), so they can run beside the new deck.

**What it decides** [I]:

- that the code path works: a deck with reads by port kind, a scan by port kind, the check;
- that a first-layer port at 1.0 crosses between 0 and the deck's 8 stages;
- that it fires once, inside the decision window;
- that its crossing agrees with the new deck's reads.

**What it cannot decide.** On the nominal cell a is the same circuit as c, with no mismatch (2.3). So the smoke also
tests that a's unary crossing equals c's line-1 crossing. It does not test a mismatched first-layer cell.

**An alternative, more informative and still cheap.** The same three runs on B2's instance 8303, for a and b, with
`D_p` from 8303's B2 deck. This is about 3 200 s of runs (1 939 + 2 × 600 + 2 × 50) and about 1 940 s of wall time.
It is the first measure of a mismatched unary port, and its runs are part of 6.2's top-up.

### 8.2 The top-up of B2

- **Per instance**: decks with the extra reads, 1 939 + 1 407 s; then 2 unary scans and 2 preset checks, 1 300 s.
  That is **4 646 s** [I].
- **Ten instances: 46 460 s of runs**, E about 17 700 s.
  - On one machine at four runs at a time, about 3.5 to 4 hours, in two waves: decks, then scans [I, scaled from
    B2's 64 758 s in about 5 hours [K, `BATCH2X_PLAN.md` §4]].
  - On two machines, about 2 hours.
- **Then, with no runs**: 40 predictions and 40 gate files, 10 instances × 4 members.
  - The generator's files took 8 to 21 s each to compile [K, `GEND/README.md`].
  - check.sh took 9 to 14 min per file, because it rebuilds its fixtures [K, same]. See open choice 9.10.
- **It needs B2's waveforms** (6.2): a fetch of about 6.6 GB [K, `PREPD/README.md`].

### 8.3 The rehearsal, with the owner's noise sensitivity reading

**The owner's confirmed reading** (relayed by the coordinator, confirmed on 2026-11-20 at about 20:3x UTC; I have
not seen the owner's own words):

- the verdicts are taken under decision 5's constants;
- 8 noisy rehearsal runs, 4 on each of 8303 and 8306, measure `b`, `w` and `d` by campaign 3's definition;
- the measured values are fixed before any noisy campaign stage;
- a declared comparison after M8 says, per counted instance, whether it keeps room with the larger of each pair of
  constants;
- it counts nothing.

**Carried over as it stands** [I]. In a family campaign, the comparison after M8 is made per counted instance of
every member. Room is computed with the member's own gate.

**Which function the 8 runs use** (open choice 9.14).

- I propose **F1, the function campaign 7 was about when the reading was confirmed**. Campaign 3's definitions are
  about reads of ports, and I have not checked that runs of four different calendars measure the same quantities.
- Each other member's noisy path is then rehearsed by one noisy run of its own. F2 runs on 8303. F3 and F4 run on
  the first top-up instance with room for them, in seed order.

**R-N** [I]:

| Runs | Run time |
|---|---|
| The 8 noisy F1 runs (4 on 8303, 4 on 8306) | 9 400 to 21 400 s |
| One run without noise of each member, and a second of F1 on 8306 (5 runs) | about 2 800 to 5 300 s |
| One noisy run each of F2, F3, F4 | 2 500 to 5 600 s (slot factors 0.76, 0.73, 0.59) |
| One untrained run per member | 600 to 900 s |
| **R-N, total** | **about 15 300 to 33 100 s** |

- **R-M**: the nominal cell through the kit's M stages on each of the six machines, about 2 700 s each [K, draft
  §7]: about 16 200 s of machine time. The unary runs add about 1 300 s per machine [I].
- **In all**: about 39 000 to 57 000 s of machine time, a few hours of wall time on six machines.
- **What it must show** [I]:
  - every run complete under the 0.75 rule [K, `C6/campaign6/README.md`, REHEARSAL_RULES];
  - each member's prediction record reproduced byte for byte;
  - G on F2's partial teaching reads, at 2x and `1e-5` (3.4);
  - a unary cell learning in a network run;
  - the network costs that set the campaign's limits;
  - the three measured constants, fixed before any noisy campaign stage.

### 8.4 The campaign (the draft's choice B: noisy runs only on instances with room)

**Measures per instance, by member** [I]:

| Member | Runs | Run time |
|---|---|---|
| F1, F2 | campaign 6's 9 | 6 476 s |
| F3 | 2 decks, 1 pair scan, 1 unary scan, 2 line scans, both-lines check, 1 one-sided set, 1 preset check | 5 949 s |
| F4 | 2 decks, 2 unary scans, 2 line scans, both-lines check, 2 preset checks | 5 422 s |
| Mean over a balanced draw | | 6 081 s |
| Superset, for the paired design | decks with the extra reads, 2 pair, 2 unary, 2 line, both-lines, 2 one-sided, 2 preset | 8 254 s |

**Totals** [I]:

| Design | Measures, E | Network run time | Network E | **Total E** |
|---|---|---|---|---|
| (a) Draw, I = 16 | about 37 000 s | 17 200 to 35 300 s | 11 200 to 23 000 s | **about 48 000 to 60 000 s** |
| (b) Draw, I = 32 | about 74 000 s | 33 900 to 69 800 s | 22 000 to 45 400 s | **about 96 000 to 119 000 s** |
| Paired, I = 16 (9.13) | about 50 200 s | 67 200 to 138 700 s | 43 700 to 90 200 s | **about 94 000 to 140 000 s** |

**How the network figures are made** [I]:

- (a): 16 runs without noise × 0.77, about 3 instances with room × 3 noisy runs × 0.77, and 4 untrained runs.
- (b): the same with 32 and about 6.
- Paired: every member on every instance, so the factor is 3.08, the sum of the members' factors, in place of
  0.77.

**Against the draft's compute proposal** of `E ≤ 72 000 s` [K, draft §6, OPEN 1]:

- (a) fits at every estimate.
- (b) and the paired design exceed it at every estimate (9.8).

**Wall time**, six machines as three pairs [K, the draft's layout]:

- (a) about 2.6 to 3.5 h of runs per machine, near the draft's 15 instances [K, draft §6].
- (b) and the paired design about 4.5 to 6.5 h [I].
- **The kit's stage bound** of 14 400 s, against M1 for 5 instances on a pair at 13 864 s [I, draft]:
  - (a), with 5 or 6 instances per pair, sits at that bound. M1 may need to be split [I].
  - (b) needs measure stages in sweeps of at most 5 instances.
  - The paired design multiplies the network stages, which must then be split by member or by round.

---

## 9. Open choices for the owner, each with my recommendation

**The first thing to ask the owner for: the smoke of 8.1** (about 1 970 s of runs on the nominal cell, or about
3 200 s on 8303). It is the one physical unknown of the family, and it is the cheapest step.

1. **The family.**
   - **Recommendation: F = {F1, F2, F3, F4}**, with F3 and F4 on unary cells.
   - Alternatives:
     - F1 and F2 only, if the smoke or the top-up shows no unary cell with room.
     - F1, F3, F4 without the shared input. This is the fallback if the rehearsal's G fails on F2.
     - F plus the nine D members: 13 functions, 4-cell decks, a second mapping amendment, room about 0.12 to 0.17.
2. **A ≤ 2 with every OR cell wired to every line.**
   - **Recommendation: yes.**
   - The alternative, unwired lines recorded as gain-0 arrivals, needs a check of c's latency against the dated
     decoder that I did not make.
3. **The draw.**
   - **Recommendation: balanced, by the SHA-256 sort of section 4.**
   - Alternatives: weighted by `1 / r_m`; independent uniform per seed.
4. **How a one-input term is made** (2.5).
   - **Recommendation: (ii), a unary cell, one port at 1.0.**
   - The tie route (i) is rejected: it is a sub-run of F1 and would make F3 and F4 empty as tests.
5. **The mapping amendment** (2.4: a unary cell on layer 1's dose; `K = 8` with no pair cell).
   - **Recommendation: write it, review it, and freeze it before the top-up's first run.**
6. **The room instrument.**
   - **Recommendation: the generator's mirror per cell, with the Lean K3 verdict as the last word**, both for `r_m`
     and for counting.
   - The alternative, the frozen room model, refuses instances the kernel certifies on c's both-lines read [K,
     `GEND/README.md`].
7. **The size, and the claims' minima** (6.3, 5.3).
   - **Recommendation: (a)**, the owner's pre-B2 rule by member: I = 16 if every `r_m` = 2. With it N_P = 8 (2 per
     member) and N_N = 2 pooled.
   - The alternative, (b), is a family rule written before the top-up: I = 32, N_N = 4.
8. **The compute bound.**
   - **Recommendation: keep the draft's E ≤ 72 000 s for (a)**, which fits at 48 000 to 60 000 s.
   - (b) or the paired design need about 120 000 to 140 000 s, tested once after the rehearsal.
9. **Which instances get noisy runs.**
   - **Recommendation: the draft's choice B**: noisy runs only on instances with room for every cell.
   - The cost: the noise claims on the first-layer cells lose the instances where only they have room. Stated now,
     as in the draft.
10. **How the 40 gate files of the top-up and the campaign's gate files are compiled.**
    - **Recommendation**: compile the theory once and check each file with check.sh's step 3 (forbidden tokens,
      warnings as errors, axioms). Keep one full check.sh run per member as campaign 6 did.
    - I did not check that the kit accepts such a split.
11. **The untrained control.**
    - **Recommendation: one per member** (4 runs, about 1 000 s).
12. **G on partial teaching reads.**
    - **Recommendation: keep G's rule unchanged and report the partial teaching reads as their own subset.**
13. **A draw per instance, or the paired design** (every member's networks on every instance; 5.4, 8.4).
    - **Recommendation: the draw, as the owner decided, at size (a).**
    - Paired would give each member about 0.8 to 0.9 chance of 2 counted noisy instances at I = 16, against about
      0.18 under the draw. It costs about 94 000 to 140 000 s and needs the superset measures on every instance.
14. **Which function the noise sensitivity reading's 8 runs use** (8.3).
    - **Recommendation: F1**, the function of campaign 7 when the reading was confirmed, plus one noisy rehearsal
      run of each other member.

---

## Not checked

- **The unary first-layer cell.** It has never been simulated, at any amplitude, on a or b. A single port at 0.49
  might or might not ever cross. Its costs are assumed equal to c's line runs.
- **The mapping amendment** (2.4) has not been checked against the deck reads or the one-sided bound. The B = 2
  mapping (help ≠ 0) has not been checked either.
- **Gate files.** None was generated or compiled for F2, F3 or F4 with measured numbers. The generator's synthetic
  S1 and S2 cover their shapes only with synthetic observations [K, `GEND/README.md`].
- **The tie analysis** (2.5) compares port sets per slot (`fam/subrun.py`). It does not compare dates, amplitudes or
  slot order, which I argue matter only through read-only tests. The Lean substitution argument by `TwoRails` was
  not written out.
- **Room per member** on B2 and the top-up is not computed. F2 = F1 is my reading.
- **B2's waveforms.** I listed the evidence branch's tree only. I did not fetch, join or hash its parts.
- **Whether a second deck of a B2 instance reproduces B2's doses.** It is expected of a noise-free deterministic run
  with the same seed, deck and tolerance. Not checked.
- **`SECOND_FUNCTION_DESIGN.md`** itself: I have only the coordinator's summary of it. Its code estimate was not
  reconciled with mine.
- **The owner's words** for the noise sensitivity reading: I have only the coordinator's relay. Whether campaign 3's
  definitions give the same quantities on runs of different members' calendars is not checked.
- **Network runs.** No network run exists at `1e-5`, nor on a mismatched cell at 2x. Every network cost here rests
  on the draft's estimates and on my slot-count scaling [G].
- **G at 2x and `1e-5`** (a stored voltage under gated reads) is not measured. The 0.0001 mV figure is from attempt
  c1, at 1x and `1e-4`.
- **The bench's fan-out** is ideal per-port sources. Loading and coupling of a shared driver are not modelled. Nor did
  I check whether the injected noise is independent on the two ports of a shared input.
- **The product model of room** assumes independent crossings.
- **Whether 85xx seeds are free.**
- **The launch kit.** Whether it accepts three pairs and stage sweeps of at most 5 instances, and whether its
  14 400 s bound applies per stage as the draft reads it.
- **The kernel cost** of the 40 top-up gate files and of a campaign. I compiled nothing.
- **The C5 PREDICTION.md text of G**: I read its lines 569-571 only, not the definition of "write'".
- **Files I read only in part.** `C5/predicted.py` beyond lines 1-50, 355-459; `C5/analyze.py`, `reads4.py` and
  `run4.py` other than by search; `C6/batch/predict6.py` and `schedule6.py` other than their docstrings, searches and
  `deck_w`; `stages6.py` not at all. The "hard-coded" column of 7.2 rests on searches for the names of cells, ports
  and inputs, and on the design note's A.3 inventory [K, `FUPD/DESIGN_NOTE_WIDEN.md` A.3].
- **The binomial figures** assume the room rates stated with them.
- **The layered theory** (#179) is not used here, and nothing above applies to it.

## Changes since the first version

**Second version** (SHA-256 `88dd2210…c05d`):

1. It recommended tied ports for one-input terms, with a units rule for Lean. **Withdrawn in the third version.**
2. It showed that F is exactly the valid rewirings of the first-layer ports (`fam/rewire.py`): three kinds of map
   are refused.
3. It dropped the development batch. **Revised in the third version**: B2 is topped up with the unary measures.
4. It added the paired design, the owner's noise sensitivity reading and the post-hoc caution on sizing.

**Third version**, after the coordinator's review of the first version and its reading on tying ports:

1. **The coordinator's reading on ties is confirmed** (2.5, `fam/subrun.py`).
   - Tied F3 and F4 are sub-runs of F1 port for port, and test nothing beyond it.
   - Tied F2 differs from F1 only by the partial teaching reads.
   - So the tie route is rejected although it is cheaper, and F3 and F4 use unary cells at 1.0, as in the first
     version.
2. **The units rule is dropped** as unnecessary: a unary cell fits layer 1's one dose as it is (2.4, 2.5).
3. **The first step** is a nominal smoke of a unary port (8.1), with a variant on 8303. Then a top-up of B2 with the
   unary measures (6.2, 8.2), instead of a fresh batch.
4. **The size** (6.3): (a) applies the pre-B2 rule by member, which gives I = 16 if every `r_m` = 2; (b) is a family
   rule written before the top-up. N_N follows.
5. **The paired design** stays as an option. It now needs the superset measures and is no longer recommended (9.13).
6. **Costs** are recomputed (8).
7. Findings 4 to 8, sections 1.3, 2.2 to 2.5, 6, 8 and 9 and the "not checked" list are rewritten. Sections 4, 5 and
   7 are adjusted.

**Fourth version**, after the coordinator's message on v2 (it crossed v3):

1. **Section 2.6 added: "What each member tests physically".**
   - Slot tables for F2, tied F3 and F4, and unary F3 and F4 against F1 (`fam/slots.py`). They confirm the
     coordinator's reading: tied F3 and F4 have 0 slots outside F1, F2 has 2, unary F3 and F4 have 6 each.
   - The two designs side by side, T (ties) and U (unary), with the fresh-batch cost of U beside the top-up.
2. Nothing else changes.

**Fifth version**, after the owner's decision (step 1: five two-layer functions of 3 inputs):

1. **Section 0 added.** It covers the members, X1 and X2 (c with one line: claims, measures, mapping, Lean), F1 as
   the regression anchor, room and size by the pre-B2 rule per member (I = 15), the draw, the claims, the costs, and
   the noise sensitivity reading on F2.
2. **Section 0 supersedes** 1.3, 4, 5, 6.3, 8.4 and 9 where they differ. Sections 1 to 3 are unchanged.

**Sixth version**: section 0.8 added, on what could raise the unary room rate before the top-up. It was written while
the smoke on 8303 ran, before its results were read.
