# Plan: a larger dose on the nominal cell (lever 2)

**Status.** A plan only, for review by the coordinator. **No simulation is run until it is reviewed.** Nothing was
installed, pushed or created. It concerns the nominal cell alone: no campaign instance, no campaign seed, nothing
preregistered. Date: 2026-11-20.

**Marks.** **[K] known**: read in a file of `research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1`.
**[I] inferred**: my reasoning or arithmetic. **[G] guess**.

---

## 1. In plain words

- The question: if the dose is made two or three times larger, do the cell's laws still hold, and does the noise
  stay the same in mV? If both, the noise shrinks in proportion against a step, and the windows of the design note
  open.
- **The dose is easy to change in the deck**: one voltage level for twice the dose. [K for the formula]
- **The measurement code is not ready for it.** Its decks, its mapping and its scans all count on 8 stages of
  about 1.35 mV. At twice the dose, 8 stages go twice as far, where single ports of a and b may start to fire. So
  the experiment needs development variants of the decks, and it cannot use the frozen gate as it is. [I]
- **A cost outside the simulation**: at twice the dose, the dose in log-gain is about 0.084, above the 1/20 that the
  read-window theorems of the native model take. [K for the bound, I for the consequence]
- **This container cannot run it**: it has no ngspice, no PDK and no pinned environment. [K, checked here]
- I propose to start with **one run**: a guard-on calibration deck at twice the dose. It answers four of the
  questions in about ten minutes of compute and decides whether the rest is worth running.

---

## 2. What sets the dose, and three ways to raise it

**The formula** [K, `research/circuit/DESIGN.md`, `35b9d80e`, "Sensor and window"]: the step of the stored voltage is
`(C_s / C_f) x (V_entry − V_exit)`. "400 fF, 30 pF and a window of 100 mV. The step is 1.33 mV by design and
1.3465 mV in the nominal cell." In `cell.spice` (`0c682cbd`): `vhi=0.6`, `vlo=0.5`, `cs0=400f`, `cf0=30p`,
`idis=8.2n`.

**The timing of a write** [K, same file]: the sensor crosses the entry level at 1.78 units, and the ERROR phase
lasts until 2.04. A FIRE is decided before 1 unit. The write happens only "if the latch is clear" at the ERROR
phase.

| Way | What changes | What moves with it |
|---|---|---|
| **A. The window**: raise `vhi` | one supply level | The entry comes earlier. By the discharge rate `idis / cs0` (20.5 mV per us), I compute the entry at about 1.5 units for `vhi = 0.7` and about 1.3 units for `vhi = 0.8` [I: the same arithmetic gives 1.71 for today's 1.78, so I add 0.07] |
| **B. The sensor capacitor**, with the discharge current scaled alike: `cs0 x k`, `idis x k` | two parameters | The timing stays, since the rate `idis / cs0` is unchanged [I]. But `idis` is also the testbench's write gate: `c4.IDIS` is used by `plans4.gates`, by `scan6.Driver` and by `gate.py` [K] |
| **C. The feedback capacitor**: `cf0 / k` | the memory's own capacitor | The integrator itself, the preset, and how the amplifier noise reaches the stored voltage. Not proposed |

**Why the window is not enough for three times.** The latest FIRE of a single read in the 17 runs of attempt c1 is
at 1.0003 units [K, from the audit's reads], and the bench's own bound is 1.06 (`dnf.LATENCY`). With `vhi = 0.8` the
entry would come about 0.2 to 0.3 unit after that, against 0.7 unit today. A FIRE that comes after the entry would
give a read that fires and writes. [I]

**What I propose.**

| Dose | Parameters | Expected step | Entry of the ERROR phase [I] |
|---|---|---|---|
| 1x | unchanged: `vhi = 0.6`, `cs0 = 400f`, `idis = 8.2n` | 1.35 mV | 1.78 units [K] |
| 2x | **`vhi = 0.7`** | about 2.7 mV | about 1.5 units |
| 3x | `vhi = 0.7`, **`cs0 = 600f`, `idis = 12.3n`** | about 4.0 mV | about 1.5 units, as at 2x |

The 3x row could instead be `vhi = 0.8` alone. I would choose between them after seeing the timing at 2x.

**About the noise model** [K for the code, I for the remark]. The injected sources take their levels from
`research/circuit/noise.json`, which `noise.py` computes from each block analysed alone (the amplifier with 30 pF
and 400 fF). Way A changes no block. Way B changes the sensor capacitor, so the injected levels would no longer be
exactly those of the block; the effect should be small, and I did not compute it.

---

## 3. What must change in the code before any run

Nothing frozen is edited: this is development code beside it, as the batch's code was.

1. **The deck has no handle for these parameters** [K]. `net.deck` copies the `.param` lines of `cell.spice` as
   they are and takes no argument for `vhi`, `cs0` or `idis`. A small wrapper must rewrite those lines in the deck's
   text. Its first test is that with unchanged parameters it gives the same deck, byte for byte.
2. **`c4.IDIS`** (for 3x by way B) is a constant of three frozen modules [K]. The wrapper must give the scaled
   value wherever a port is allowed to write.
3. **The number of stages** [K for the constants, I for the consequence]. `c4.STAGES = 8`; `MAPPING_U.md` anchors
   layer 1 on "every deck alone read (w <= 7) is predicted silent" and sets the one-sided bound at 8 stages or
   more; the scans look for "crossings below 8"; the reach of the scan deck was tried at 10 stages of 1.35 mV only.
   At k times the dose, the same stage counts go k times further. Where a single port of a or b starts to fire is
   not known beyond 8 doses [G]. So the decks should cover about `8 / k` stages plus one, and the mapping's "8"
   should become a parameter.
4. **Noise seeds for the nominal cell** [K]. `c4.noise_seed` gives the nominal cell exactly one, 90 961, which
   campaign 5 used. Eight new ones are needed. They must be numbers never used to fix the noise of a run
   (`C6/PREDICTION.md` section 4 lists the ranges used), declared before the runs.
5. **The slope** for `b` and `w`: FIRE latency against stored voltage at the trained state (NOISE_AUDIT, second
   version, section 5.1). The guard-on deck reads each kind at several stages above its need, with latency and
   stored voltage; a short reader must take the secant there. Phase 1 took it from isolated scan reads.

**The Lean gate is not used.** The laws to check are physical; the gate certifies a prediction for a campaign. [I]

---

## 4. The runs

Estimated wall times are the batch's means [K, `BATCH_REPORT.md` section 1], which were measured on mismatched
cells. The nominal cell is faster (its guard-on deck took 485 to 514 s, `CAMPAIGNS_4_AND_5.md`), so these are on
the high side. A noisy network run on the nominal cell took about 925 s (`STOPPING_RULE.md`).

| Step | Runs | Kind | Each, s | At 1x | At 2x | At 3x |
|---|---|---|---|---|---|---|
| 0. Smoke | 1 | guard-on calibration deck | 804 | yes, as a test of the wrapper | **yes, first of all** | yes |
| 1. Measures | 8 | guard-off deck (645); 2 pair scans (495); 2 line scans (465); both-lines check (37); 2 one-sided sets (219) | 3 040 in all | no: they exist | yes | yes |
| 2. Quiet network | 1 | run without noise, with skew | 718 | yes | yes | yes |
| 3. Noisy network | 8 | one noise seed each | 925 to 1 400 | yes | yes | yes |
| **Runs** | | | | **10** | **18** | **18** |
| **Compute** | | | | 8 900 to 12 700 s | 12 000 to 15 800 s | 12 000 to 15 800 s |

- **At 1x the measures exist** [K]: the rehearsal r3 measured the nominal cell on both machines (stages RM1 to RM3,
  `none-a` and `none-b`, `REPORT.md` section 4). The 1x smoke is there to test the wrapper: it must reproduce r3's
  doses string for string.
- **Why 8 noisy runs** [I]. `b` is a quantity between runs. Each run gives 4 offsets (a, b, line 1, line 2), so 32
  in all, and the root mean square of 32 values is known to about 12 %. Campaign 3 had 38, phase 1 had 55.
- **In all**: 46 runs, about 33 000 to 44 000 s of compute. Four at a time on one machine of 4 processors, that is
  roughly 2.5 to 3.5 hours; half on two machines. [I]
- **In stages**: the 2x smoke alone first (about 10 minutes). Then 1x and 2x (28 runs, about 21 000 to 28 500 s).
  Then 3x only if 2x says go.

Lower needs make the network calendars shorter, so the 2x and 3x network runs should cost less than at 1x. I did
not estimate by how much.

---

## 5. Go or stop

Per dose, in this order. The first "stop" ends that dose.

| # | Law | Measured on | Go | Stop |
|---|---|---|---|---|
| G0 | The wrapper changes nothing by itself (1x only) | the 1x smoke | the doses equal r3's, string for string | any difference |
| G1 | **The dose** | the smoke: the 8 joint doses of each port | the mean is k times 1.3465 mV within 2 %; on each port, successive doses within 1 % of each other | outside either |
| G2 | **A write stays clean** | the smoke | no read that fires and writes; no gated read moves a stored voltage by more than 0.01 mV; on every firing read the ERROR entry comes at least 0.2 unit after the FIRE | any of them fails |
| G3 | **The need exists and falls** | the smoke | each of the four kinds has a first firing stage in the deck; reported against `s* / k` | a kind that never fires, or fires at stage 0 |
| G4 | **The scans are clean** | the 4 scans, the both-lines check, the one-sided sets | four consistent brackets of 1/256 stage, none contradictory after the majority; `ceil(s*)` equals the deck's first firing stage, four of four; each scan's `u(0)` within 20 uV of the deck's; single ports silent at their bound; both lines fire at the preset | any of them fails |
| G5 | **The network does what the measures say** | the quiet run | the six words and the 16 outputs are those the needs give | any difference |
| G6 | **The noise in mV, per constant** | the 8 noisy runs, with the slope of the smoke | `d`, `w` and `b` as section 5.1 of the audit defines them, each within 25 % of its 1x value | `w` or `b` grows with the dose: more than 60 % at 2x, more than 100 % at 3x |

- **G6's numbers are a proposal** [I]. With 32 offsets, 25 % is two standard errors. Between "go" and "stop" the
  answer is "unclear": the dose helps, less than in proportion.
- At 1x, G6 gives the first measure of `b` and `w` by campaign 3's definition on this deck. That is worth having
  whatever the larger doses say.
- A need of 1 is not a stop, but it leaves one silent stage only, the preset. I would report it as a warning: the
  prediction then says little.
- The audit's own instrument (score and FIRE level, in steps) would be computed on the same runs, beside
  campaign 3's.

**What a "go" would not show.**

- Nothing about mismatch: the three cells of the nominal deck are the same nominal cell.
- Nothing about any noise but the injected model.
- **Nothing about the theorems of the native model at that dose** [K, `DESIGN.md` line 120]: "The read-window
  theorems take doses of at most 1/20." The dose is 0.042 in log-gain at 27 C today; twice that is 0.084. The
  network theorem of the guarded model counts doses and is not concerned [I], but the bridge from the analog cell
  would no longer cover the cell.
- Nothing about the layout track, whose dose criterion was set for 1.35 mV (`sky130-layout/CONCLUSION.md`).

---

## 6. The toolchain, and where it would run

**Pinned** [K, `C6/INVENTORY_a.json`]: Python 3.12.3, numpy 2.3.5, ngspice 42, the PDK at commit `1232782c`, each
with its SHA-256; Ubuntu 24.04, 4 processors.

**This container** [K, checked here]:

| Needed | Here |
|---|---|
| Python 3.12.3 | present, **without numpy** (the default Python is 3.13.18 with numpy 2.5.3) |
| numpy 2.3.5 in the pinned venv | absent: no `/home/user/owner-prep` |
| ngspice 42 | **absent** |
| the PDK at `1232782c` | **absent** |
| 4 processors, `avx512f` | present (Xeon at 2.30 GHz) |

So it cannot run a single deck today, and I installed nothing.

**Where it could run.**

1. **The campaign's machines a and b**, which have the environment and its checks. The runs would go outside the
   launch kit, as the batch's smokes did: the kit's manifests and seed guards describe campaign decks, not decks
   with changed parameters [I, from `c6.py`'s docstring].
2. **This container, after an install** that the owner would have to allow, and that needs network access to the
   package and PDK sources. I have not checked that access.

Either way: every long run detached, four at a time, a time limit of twice the estimate, and the session kept
active, since a container that sits idle restarts (`REPORT.md` section 7).

---

## 7. Not checked

- **Nothing was simulated.** Every timing figure of section 2 is arithmetic on the deck's parameters, not a
  reading of a trace.
- That rewriting the `.param` line is enough: I did not check whether another file or a subcircuit default holds a
  second copy of `vhi`, `cs0` or `idis`, beyond the three uses of `c4.IDIS` cited.
- That scaling `cs0` and `idis` together really leaves the timing unchanged: the precharge of a larger capacitor,
  and the current mirror at a larger current, are not examined.
- Where single ports start to fire beyond 8 doses.
- The contents of `noise.json`, and how way B would change the block's noise.
- The cost of the 2x and 3x runs: the figures are 1x means on mismatched cells.
- I read `DESIGN.md` around the dose only, and neither `launch.py` nor `schedule6.py` in full.
- Whether an install is possible in this container.
