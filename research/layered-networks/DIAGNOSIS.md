# Diagnosis: why 3 of 4 ANDOR3 cells fail K0, when 99 family cells never did

**No new simulation.** From existing data only:
- the family top-up verdict, `research/function-family-dev` 0c003fbf, `topup-verdict/PREDICTIONS.json`;
- campaign (a), `evidence/function-family-campaign-predicted` d7e4fcc2;
- campaign 7-prep's protocol draft and `dev/batch2x.py`, `research/learned-dnf-circuit-campaign-7-prep` b956efe4;
- campaign 5's `c4.py` and `run4.py` at ecfcd1c1;
- this package's 9801/9802 M4 records (`dev/cal4_*`).

Marks: [K] counted or read in a named file; [I] inferred; [G] guessed.

## The answer in short

Two systematic causes and one instance-specific one.

1. **The layered deck runs the cell at the frozen 1x design point; the family runs it at its 2x design point**
   (`vhi = 0.7`, about 2.71 mV per write) **and at `reltol = 1e-5`.** The layered deck is `cell.spice` unchanged:
   `vhi = 0.6`, 1.35 mV per write, `reltol = 1e-4`. At half the step, every budget term fixed in mV doubles in
   stages:
   - the K0 base goes from 0.013 to 0.022 stage;
   - the K3 base goes from 0.164 to 0.33 stage.

   The 1e-4 tolerance adds a numerical irreproducibility of the same size as the D4 term. The family measured 32 µV
   between two identical cells at 1e-4, and agreement at 1e-5 [K, `CAMPAIGN7_PROTOCOL_DRAFT.md` lines 40–42].
2. **The single Lean testError of an either cell (the max rule, kept by the owner)** puts c2_0's anchor budget at
   0.059 stage. The family's two-layer gate tested c's anchors at its one-port budget (0.013 stage at 2x).
3. **This instance's crossings sit unusually close below their stop stages.** 3 of its 6 groups have margins under
   0.05 stage (0.009, 0.039, 0.039), against 1 of 60 in the family [K, below].
   - At the layered budgets of about 0.03–0.06 stage, uniform margins would make about 0.16 K0 failures expected in
     4 cells. Three are observed. So most of the K0 failure count of **this one instance** comes from its small
     margins, with the 1x budgets (about 2–4× the family's) as an aggravating factor.
   - Whether the small margins are chance or systematic cannot be decided without new runs. One mechanism is visible
     (below, point 4); it is small.

## 1. Stop margins (need − s*), family against layered

| Cell type | Family (top-up, 8301–8310) | n | min | 10 % | median | under 0.05 |
|---|---|---|---|---|---|---|
| pair (layered both) | s* 1.47–2.44 stages at 2x | 20 | 0.029 | 0.084 | 0.436 | 1 |
| unary (layered copy) | s* 1.37–2.60 | 20 | 0.189 | 0.299 | 0.502 | 0 |
| c line 1 / line 2 (layered either) | s* 0.66–2.40 | 20 | 0.053 | 0.10 | ~0.5–0.7 | 0 |
| **all family** | | **60** | 0.029 | | | **1** |

| Layered (1x stages) | NOT1 c1_0 | c1_0 both | c1_1 copy | c2_0 line 1 | c2_0 line 2 | c3_0 copy |
|---|---|---|---|---|---|---|
| s* | 3.6025 | 3.9911 | 2.9608 | 3.9608 | 2.7187 | 3.8799 |
| margin (stage) | 0.398 | **0.009** | **0.039** | **0.039** | 0.281 | 0.120 |
| margin (µV) | 537 | **12** | **53** | **52** | 376 | 163 |

- The need is the same quantity in both, but a layered stage is half a family stage, so the needs are about twice
  as large (3–4 against 2–3) [K].
- Under a uniform margin, P(at least 3 of 6 below 0.05) ≈ 0.002. That is computed after looking, on one instance;
  it is a flag, not a test.

## 2. Budget terms, in stages of the cell's own step (score / (k d), k = 2 for a both cell)

| | D (mV/write) | K0 base | H | H_drift | H_D4 | **K0 error** | **K3 error** |
|---|---|---|---|---|---|---|---|
| family pair / unary / c (median of 10) | 2.71 | 0.011 | 0.0020 | — | — | **0.0133** | **0.164** |
| layered NOT1 c1_0 copy | 1.348 | 0.0223 | 0.0026 | 0.0004 | 0.0015 | **0.0266** | **0.331** |
| ANDOR3 c1_0 both | 1.343 | 0.0224 | 0.0044 | 0.0004 | 0.0018 | **0.0289** | 0.334 |
| c1_1 copy | 1.342 | 0.0224 | 0.0058 | 0.0003 | **0.0138** | **0.0423** | 0.347 |
| c2_0 either (train / test) | 1.338 | 0.0229 / 0.045 | 0.0059 | 0.0007 | 0.0068 | **0.036 / 0.059** | 0.343 / 0.667 |
| c3_0 copy | 1.356 | 0.0222 | 0.0040 | 0.0002 | 0.0017 | **0.0282** | 0.330 |

- **The dominant term is the base (P's), doubled by the step.** The K0 base is ε + ⌈0.030 mV · sensitivity⌉. In
  stages this is about 0.030 mV / D: 0.011 at 2.71 mV, 0.022 at 1.35 mV. K3 scales the same way: 3σ is fixed in mV
  (`DECISION5`), so 0.164 stage at 2x becomes 0.33 at 1x [K].
- **The new terms are smaller, except D4 on c1_1.** H is 1.3–3× the family's: the bracket is 20 µV, a larger share of
  a 1.35 mV step. H_drift is negligible. H_D4 is 0.0138 stage on c1_1, which alone flips it from +23 to −30.
- **Either cell.** The test budget of 0.059 stage is the max rule's two-port both-lines budget. Under the one-port rule
  it would be 0.036, and c2_0's margin of 0.039 would pass.

## 3. Training schedule and inputs from other cells

- **Dose step.** 1.35 mV per write at 1x against 2.71 at 2x [K]. This is cause 1.
- **Number of stages.** Twice as many writes to the stop, the same physics [K: the layered s* in writes, 2.7–4.0, is
  2× the family's 1.4–2.6 in 2x stages].
- **Doses are uniform.** The training states sit at w = 0, 1.0000, 2.0000, 3.0000, 4.0000 within 0.002 [K,
  `instrument.training_path` on 9802]. ε is 0–7 score units, as in the family (2–4). The fit is not the problem.
- **Lesson replays through lower layers.** The lower cells are gated read-only. Their stored voltages move by at most
  0.3 µV per slot (the measured drift) [K]. No write leaks into a replay.
- **Inputs from another cell.** A routed pulse is the same ideal current pulse as an external one, with the same
  amplitude (0.49 / 1.0) and the same shape (the router sets the same sources) [K, `run.Network.pulse`]. Only the
  arrival date differs; a port's clocks start with its pulse, so a write does not depend on it [I].
  - c2_0's line-1 crossing (0.039) is not worse than c1_1's (0.039), which has an external input [K].

  No sign that routed inputs shift the trained state.

## 4. Router, 0.4 µs grid, latch double edge

- **The grid** moves emission dates by at most 0.02 tu, and so arrival dates. It does not change a pulse's amplitude
  or shape, nor any write [K].
- **The same-edge double crossing** changed a record, not the circuit [K, M4].
- **A history effect, of the size of the solver tolerance.** On c1_1:
  - the parallel scan, approaching from below after silent reads, fired at s = 2.9666 and 2.9710;
  - the solo scan, approaching from above after a run of FIREs, was silent at 2.9702;
  - the same cell, at nearly the same state, gives opposite outcomes about 5 µV apart.

  The other cells show differences of 0.0004–0.007 stage. At 1e-4 the family saw 32 µV between identical cells [K].
  - I can't tell solver noise apart from a physical memory of the last FIRE without new runs [I].
  - Either way, it is about 0.005–0.014 stage at 1x. That is the D4 term, and it is half that in stages at 2x.

## 5. Other differences between a family deck and a layered deck

| | Family (campaign 5/6 decks, batch2x) | Layered (this package) | Effect |
|---|---|---|---|
| dose design point | `vhi = 0.7` (2x) | `vhi = 0.6` (1x, frozen cell) | cause 1 |
| solver | `reltol = 1e-5` | `reltol = 1e-4` (frozen cell) | D4 and history noise |
| junction areas | `net.deck` default `junction="areas"`, stage J's areas [K, `run4.py:150` calls `net.deck(cells, section)`] | none | junction capacitance and leakage absent; effect not measured [I] |
| cells per deck | 3 | 1–6 | none expected |
| calibration | separate decks and scans before any network run | in situ, after training and tests | the scan starts from the trained state, so the approach direction differs (point 4) |
| either cell's test budget in Lean | one-port for anchors; two-port only for the both-lines read | one testError, max rule | cause 2 |

## 6. What it implies for the yield check

YIELD_CHECK.md used the family's per-cell rates, which were measured at 2x. At 1x, the K3 budget is about 0.33
stage on each side of a crossing, so a uniform crossing has room with probability about 1 − 2 × 0.33 ≈ 0.34 per cell
[I], against the family's 0.58–0.88.
- A 4-cell instance at 1x would have room at K3 about **1 % of the time** [I], not 23–26 %.
- At K0 the 1x per-cell failure is about 3–6 % [I], against about 1.3 %.

**So the projections of YIELD_CHECK.md hold only at the family's design point.**

## Candidate fixes, ranked

| # | Fix | Kind | Expected effect | Cost | Continuity with campaign (a) |
|---|---|---|---|---|---|
| 1 | **Adopt the family's 2x design point in the layered deck**: `vhi = 0.7` and `reltol = 1e-5`, by the same two-line rewrite as `batch2x.py` (`dosedev2.window`, `dosedev_tol.rewrite`). A new deck function, nothing frozen edited | design | budgets in stages back to the family's (K0 ≈ 0.013, K3 ≈ 0.164); the 1e-4 irreproducibility and most of D4 gone (the family: 32 µV → agreement); K3 room per cell back to about 0.6–0.9 | slots ×1.4–2.1 for 1e-5 [K, `batch2x.py` SLOW_DOWN]; about half as many training rounds at twice the dose (needs 2–3 instead of 3–4) [I]; net about ×1.0–1.5 per instance [G]; dev: about 1 h plus a rerun of 9801/9802 | **full**: the same cell design point and solver as B2, the top-up and campaign (a) |
| 2 | **Junction areas** as in campaign 5's `net.deck` default (stage J's `junction/netlist.py`) | design | removes an unmeasured deck difference | more devices and nodes per cell, slower [G]; dev: about 1–2 h | needed for full continuity |
| 3 | **Measure D4 and the history effect again at fix 1**: solo against parallel, and each bracket end read from both directions (the family's repeats of disputed states); then fix `d4_stage` | measurement | a D4 bound for the campaign at the new design point; tells solver noise from physics | about 8–12 more slots per scan [G], in dev only | neutral |
| 4 | **Ascent-from-preset scan on one dev instance** (the family's order: a fresh session, the scan before any training) against the in-situ scan | measurement | tests whether in-situ scanning after training shifts s* (cause 3) | one extra session per cell [G], dev only | moves towards the family's order |
| 5 | **Either cell's testError: the one-port rule** | rule | c2_0 eligible at K0 | none | the family's two-layer gate used one-port for c's anchors [K]. **The owner has decided to keep the max rule**, so this is listed and not proposed |

**Not candidates.**
- The lesson replays, the routed inputs, the 0.4 µs grid and the latch double edge: no evidence that any shifts the
  trained state (points 3 and 4).
- Changing the stop rule or the slot: no evidence either.

**Recommendation.** Fix 1 first: it is the family's own design point, so it restores continuity. Then fix 3 on the
same reruns. Fix 2 only if full deck continuity with campaign (a) is required. **The yield check should be redone at
the chosen design point before any campaign sizing.**
