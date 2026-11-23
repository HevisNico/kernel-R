# Layered calibration: proposal (milestone 1)

**A proposal only. No code is written and nothing is run for it. Nothing here is preregistered.**

Marks: [K] read in a file named here; [I] inferred; [G] guessed (an estimate).

Sources read:
- the family method: research/function-family-campaign-impl at 920413ec (`research/function-family/TOPUP_RULES.md`
  §1–§3.5, `research/function-family/dev/family_predict.py`) and the freeze marker at df3851b2;
- `FAMILY_DESIGN.md` (§0.2, 2.4 and 7.1, as `TOPUP_RULES.md` cites them; not read line by line);
- campaign 5's `predicted.py` as P (`table`, `guarded`, `G`, `sensitivity`, `noise_square`, `read_budget`,
  `instance`) and `c4.DECISION5`, at research/learned-dnf-circuit-campaign-6-impl ecfcd1c1;
- campaign 6's `predict6.py` (`doses_V`, `deck_w`, `anchors`, `mapped`, `measure_instance`, `augmented`) and
  `scan6.py` (`scan`, `move`), at the same commit;
- the scan, one-sided and calibration records of research/learned-dnf-circuit-campaign-7-prep (b956efe4), for slot
  counts;
- on the Lean side: `LayeredMonotoneTarget.lean` (Cell, Cell.Valid, AdditiveSlot, FiringSlot, ReadCalibration,
  TrainingCalibration), `LayeredMonotoneCheckerTargets.lean` (`Checker.additiveSlot`, `firingSlot`, `oneRead`,
  `checkLayeredTrainingCalibration`, `checkLayeredReadCalibration`), `LayeredMonotoneCheckerProofs.lean`,
  `Target.lean` (`admissible`), and the composition files of proof/layered-composition (e9d228e).

## 0. What the family method does, in one paragraph [K]

The score of a read is **not a physical readout**. Campaign 6 replaced the guard-off charge peak with a **mapped
score on the stored-voltage axis**:
- w_p = (u_p(0) − u_p) / D_p is the port's stored-voltage move from the preset, in doses;
- Z = help + Σ_{p in the read's ports} (g_p + d · w_p) (`predict6.mapped`).

The anchors are set so that Z = θ (100 000) at the scanned FIRE crossing s* (`predict6.anchors`, `TOPUP_RULES.md`
3.5.2): a bisection along the training path to 1/512 stage, about 50 slots per scan [K, campaign 7-prep records:
49–55 slots]. The method then fits a guarded tuple (help, gains, dose), linear in the writes, by exact least squares
(`P.guarded`). It takes ε as the largest |Z − G| and the sensitivity as guarded dose / D_p in mV. The budgets are
`P.read_budget(ε, sens, writes, K, DECISION5)` at K = 0 and K = 3, plus H = ⌈h · d⌉ for the scan's half bracket h. A
read is "not measured" when its FIRE bit disagrees with Z ≥ θ while |Z − θ| > H, or when question 1 fails
(⌈s*⌉ ≠ the first firing stage).

The same R cell is used here, so the method **applies to the cells**. It does not apply as code: its tables are tied
to the two-layer a, b → c shape and to calibration decks run apart from the network. It needs the adaptations below.

## (a) Mapping from measured quantities to every clause

Notation: per cell x and port p, D_p is the dose in mV and u_p is the stored voltage
(mean(vmem) − mean(sum) near the end of a slot, as `scan6` measures it). s*, h are the scan crossing and half bracket
in stages; n is the need (number of silent rounds); θ = 100 000.

### Cell fields (Lean `Cell`)

| Field | both (pair cell) | copy (unary cell) | either (two lines) |
|---|---|---|---|
| `threshold` | θ | θ | θ |
| anchor K, dose `d` | K = max(8 − s*, s*), d = round(θ/2K) | K = max(8 − s*, s*), d = round(θ/2K) (`TOPUP` 3.5.2 point 6) | d = round(θ/(s*₁ + s*₂)) |
| `initialGain` | g₁ = g₂ = round(d (K − s*)) | g₁ = round(θ − d s*); g₂ = 0 (port 2 is not an input) | g_p = round(θ − d s*_p) |
| `help` | 0 | 0 | 0 |
| `dose` (fitted) | guarded tuple's dose (`P.guarded` over the cell's own reads) | idem | idem |
| `trainError`, `testError` | budgets of (c), at K = 0 or K = 3 | idem | idem |
| `maxWrites` | rounds run − 1 | idem | min over its 2 groups of rounds − 1 |
| `rail` | 10 θ (P.RAIL) | idem | idem |

The anchors give the mapping. The fitted tuple is what Lean checks against. The family method uses the anchors for
Z and the guarded tuple for G. That stays as it is.

### Per read (every lesson read, every replay read, every test read)

| Lean clause | Measured quantity |
|---|---|
| `start`, `arrival`, `emissions` | as now (router dates, launch dates) |
| `measuredScore` | Z = round(help + Σ_{a in input} (g_a + d · w_a)), with w from u measured before the read in the same slot |
| decoder: `fired = decide (θ ≤ measuredScore)` | holds by construction **only if** the FIRE bit agrees with Z ≥ θ. Check every read; a read with \|Z − θ\| > H and a disagreeing bit makes the instance "not measured" (`predict6` point 3) |
| emission timing (one emission, by the deadline, after every arrival) | as now (already checked) |
| arrival window | as now (`ThresholdRead` includes `InWindow`, already true on every read) |
| residual: `admissible budget (measuredScore − score w input)` | Z − G, where G is the fitted tuple's score at the writes Lean counts: `writesBefore` (lessons) or `settledWrites` (tests). Writes are counted as the silent rounds with an arrival, the same count the router records |
| `scoreAt y` (firing reads, for submasks and anchors) | the mapped Z of mask y at the same slot's u (no extra read). Submask dominance follows from g_a + d w_a ≥ 0 per port; this is checked, not assumed |
| anchors: `score w y − testError ≤ scoreAt y` | holds when the fitted G and the mapped Z agree within testError at the anchor mask |

### The inverter-rail ports

A both cell fed by a direct rail and a complement rail (XOR) receives its two pulses about 0.08 tu apart [K: direct
at s0 + δ, complement at the inverter emission + δ, dev runs]. The mapped Z does not depend on timing, but the
crossing s* does. So the scan reads of such a cell **inject the pulses with the cell's measured offset**: the median
over its training reads of (port arrival − first arrival). A copy fed by a complement rail (NOT1) gets one pulse; its
scan needs no offset.

The inverter itself has no score clause: `checkInverterRead`, already checked.

## (b) Reused reads and separate scans

| Quantity | Source | New slots |
|---|---|---|
| u_p before and after every read, every port | **training and test slots**: one more `meas avg` per port per slot | 0 |
| D_p | the moves of the silent lessons (n doses per port; the family uses 8 joint doses of a deck) | 0 |
| FIRE bits, latencies, decoder checks | every lesson, replay and test read | 0 |
| ε (fit residual) | lesson reads at stages 0..n, mapped over every mask | 0 |
| test-state scores, scoreAt tables | test reads | 0 |
| u(0) | the preset, same session | 0 |
| **s*, h per (cell, group)** | **a scan**: pair scan (both), unary scan (copy), one line scan per line (either) | ~30 per scan (bisection started from the training bracket [n − 1, n]; the family's ascent from s = 0 is not needed) [G], against ~50 in the family [K] |
| one-sided set (both cells) | 2 single-port reads at W + h | ~8–15 [K: 12–16 in 7-prep] |
| both-lines FIRE check (either cells) | 1 read at the preset state | 2 [K] |
| guard-off calibration deck | **not needed**: the mapping replaced its Z in campaign 6 | 0 (the family runs ~20–28 min per deck [K]) |

Scans must run **in the same session, after the tests**: a different deck draws a different mismatch sample. They
start from the trained state and move each port along the path by doses and imposed leaks (`scan6.move`). That
needs the per-port leak control of `net.deck(leak_per_port)` in the deck builder. Scans are not part of the Lean
trace.

**Parallel scans (proposed).** Cells receive ideal injected pulses during scans and are not routed, so the cells of
one instance can be scanned in the same slots. The two lines of an either cell stay sequential: they share its main
capacitor. This is new. It must be checked once against a solo scan on a development instance.

Extra slots and machine-minutes per instance, at the measured cost per slot (NOT1 ≈ 7 s, ANDOR3 ≈ 30 s,
XOR3 ≈ 47 s):

| Instance | Scans | Parallel: slots, minutes | Sequential, as the family: slots, minutes |
|---|---|---|---|
| NOT1 | copy | ~30, ~3.5 | ~50, ~6 |
| ANDOR3 | both, copy, either ×2, copy | ~70, ~35 | ~265, ~135 |
| XOR3 | both ×2, either ×2, copy | ~70, ~55 | ~280, ~220 |

With today's training and test (1.2, 16.8, 29.0 min), the totals with parallel scans are about 5, 52 and 84
machine-minutes. **This corrects my earlier estimate, which was too low**: it said 8–20 extra minutes for ANDOR3. It
did not count the scans at their real length.

## (c) Budgets per read, on `P.read_budget`

Constants: `DECISION5` (between 0.111, within 0.094, per dose 0.009 mV), allowance 0.030 mV at K = 0. Each
sensitivity is sens_p = d / D_p (guarded dose over measured dose).

| Gate | trainError | testError | H |
|---|---|---|---|
| both | max_{k=0..n} read_budget(ε, [s₁, s₂], [k, k], K) + H | read_budget(ε, [s₁, s₂], [n, n], K) + H | ⌈h · 2d⌉ |
| copy | max_{k=0..n} read_budget(ε, [s₁], [k], K) + H | read_budget(ε, [s₁], [n], K) + H | ⌈h · d⌉ |
| either | max over lines p and k = 0..n_p of the one-port budget + H | **max of** the one-port rule (max_p one-port at [n_p]) and the two-port both-lines budget at [n₁, n₂], + H | max_p ⌈h_p · d⌉ |

S = 0 for every kind: each is anchored at its own crossing.

What is new:
- Lean's `Cell` has **one** testError. The family's two testing rules for c (one-port, and two-port both-lines) are
  merged by taking their max. This is conservative.
- ε is fitted over the stages that training visits, 0..n. The family fits 0..n + 2 from a calibration deck.
- In a layered network every cell is "layer 1" of its own fit: one guarded tuple per cell, each with its own dose.
  The family shares one dose per layer.
- K = 3 uses campaign 5's noise constants. They mean something only for runs with noise on. The dev runs had none.
- Inverter-fed both cells use the offset scan of (a).

## (d) The Lean side

**Run per instance, one file per K (K0, K3):**
- `checkLayeredValid`, with the fitted cells. It now means something: it holds the room conditions of `Cell.Valid`.
- `checkLayeredTrainingCalibration`.
- The read calibration at every input pattern:
  - without a front end, `checkLayeredReadCalibration` (all line patterns are tested);
  - with a front end, `Checker.oneRead` at the rails of each input pattern only.
- The timing checkers of today, unchanged.
- The final theorem: `layered_recognition_from_intrinsic` without a front end, `layered_inverters_chained` with one.
  This gives the outputs from the premises, not by comparison with the data.

**New pieces:**
- A new Lean module, `LayeredReadCheckAt.lean`: a public soundness lemma
  `Checker.oneRead c train x r = true → ReadCalibration c train x r`. The existing `one_read_iff` is private, and
  `checkLayeredReadCalibration` needs a trace for every line pattern; with inverters, 2^(2m) − 2^m of them never
  occur. It is a new file that repeats the private lemmas' proofs; no existing file changes.
- Emitter (`lean.py`):
  - fitted `Cell` literals;
  - `measuredScore` in every read;
  - `scoreAt` tables, 4 masks per read;
  - lesson `CellTrain` with the observed rounds;
  - one file per K;
  - the final theorem.
- Python mirror (`measure.py`): the two calibration checkers, clause by clause, to diagnose a false value before
  Lean; written for this package, not imported from the generator's `lmirror`.

## (e) Development plan

| Milestone | Content | Estimate [G] |
|---|---|---|
| M1 | this proposal | done |
| M2 | instrument: per-slot u of every port; D_p from the lessons; leak control per port; scan mode (bisection from the training bracket, parallel, offsets), one-sided set, both-lines check; tested on NOT1 | 0.5 day + ~10 machine-min |
| M3 | mapping and fit: anchors per gate, mapped Z for every read and mask, guarded tuple, ε, sensitivities, budgets K0 and K3, question 1 and the decoder check. Exact Fractions. Cross-checked bit for bit against P and predict6 on one campaign 6 or 7 instance's records | 0.5 day |
| M4 | Lean: `LayeredReadCheckAt.lean` with negative controls; emitter extended; the final theorems; kernel time measured | 0.5–1 day |
| M5 | the three dev instances (9801–9803) end to end: K0 and K3 verdicts, room per cell, costs; report, then stop | 0.25 day + ~2.5 machine-h |
| | Total | about 2 to 2.5 days (my earlier "1 to 2 days" is raised) |

Each milestone ends with a report and a stop.

## (f) Risks, first the score mapping

1. **The score is a mapping, not a measure.** Z comes from the stored voltages and the scanned crossing. It is valid
   for a read only if the FIRE bit agrees with Z ≥ θ.
   - Network reads differ in timing from the scan reads: rail offset, an either cell's two arrivals up to ~0.7 tu
     apart (ANDOR3 pattern 111), upstream latency spread.
   - The crossing depends on timing. A read near the threshold can therefore break the decoder clause and make the
     instance "not measured". The offset scans reduce this for the rails, not for the either cell's arrivals.
2. **Room.** In B2, 2 of 10 instances had room at K = 3 for the two-layer cascade, `k_all3` = 2 [K, `TOPUP_RULES.md`].
   - A layered instance needs room in every cell (4 here), and the merged either testError lowers it further.
   - The yield of usable instances may be low; it would set the campaign size more than the cost does.
3. **Fewer fit points.** D_p and ε come from n ≈ 3–6 training stages, not from an 8-stage deck. The budgets may be
   larger or less stable.
4. **Parallel scans** are untested. They must be compared once with a solo scan.
5. **Question 1** (⌈s*⌉ = the first firing stage of the training word) can fail on scans that start from the
   trained state rather than the preset; then the instance is not measured.
6. **Noise.** The K = 3 constants are campaign 5's bench values. A campaign without noise has only K = 0 meaning.
7. **Lean size.** Scores and 4-mask tables per read double the file. Kernel time is expected to stay in seconds; not
   measured yet.
8. **Scans disturb the trained state.** So they come last, and a scan failure loses the instance's calibration, not
   its trace.
