# Noise audit of campaign 6, attempt c1

**Status.** An exploratory measurement, for review by the coordinator. The owner allowed the pushed runs of attempt
c1 to serve as development data for it (the owner's message in the coordinator's chat, 2026-11-20 05:27 UTC, which
I read in that session's transcript). No simulation was run, nothing was pushed, no session was created. Date:
2026-11-20.

**Fourth version**, for publication: it differs from the third (SHA-256 `e2343d0f…384c`) only in section 8, where
two sentences named a local folder (see the changes at the end). No figure and no other sentence changed.

**Third version.** The first is SHA-256 `9ee7e9d9…3808`, the second `f4ccbcc5…40d0`. The second rewrote section 5
(how campaign 3 defined the three noise constants) and corrected a wrong pairing. The third adds, in section 5.4,
`b` and `w` measured in mV by campaign 3's own definition, with the slope taken on the calibration decks of stage
M1 (fetched with the owner's go of 05:54 UTC, "Oui, par étapes"). Sections 1, 5.5, 7 and 8 follow. The changes are
listed at the end. No measurement of the earlier versions changed.

**What it is not.** It measures noise. It recounts no claim of campaign 6 under any rule, and does not say what
campaign 6 would have counted. Section 6 works out what the measured figure would give on the development batch's
records only.

**Marks.** **[K] known**: read in a pushed file, or computed from pushed files by the repository's own readers.
**[I] inferred**: my reasoning or arithmetic. **[G] guess**.

---

## 1. The result, in plain words

- The budget of campaign 6 allows each read an error of **0.33 step** (three sigma), where a step is one stage of
  the read's own training path. [K]
- In the 12 noisy runs, the noise actually seen is about **0.19 to 0.25 step at three sigma**: about 0.20 for the
  pair reads of a and b, about 0.22 to 0.25 for the single-line reads of c. [I, from K measurements]
- So the budget is wider than the noise seen, **by a factor of about 1.3 to 1.7. Not by 3.**
- Against the three constants (section 5) [I]:
  - the dose noise is right: 0.008 mV per dose seen, 0.009 in the constants;
  - **the other two depend on the instrument.** With the audit's own (score and FIRE level), a run adds about
    0.077 mV to its reads and the scatter within a run is about 0.064 mV, on the lines of c: each about 0.7 of its
    constant (0.111 and 0.094). With campaign 3's own (FIRE latency over a slope), the same runs give 0.118 and
    0.106 mV on the lines and 0.080 and 0.074 mV on the pairs: the constants, more or less.
  - The two instruments disagree by a factor of about 1.5. **The FIRE bits side with the smaller figure**: with
    campaign 3's figures, 8 of the 497 firing reads should have differed from the quiet runs, and none did
    (section 5.4).

  The first version said that the margin was mostly in the difference between runs; that came from a wrong pairing
  and is withdrawn.
- The noise is real and does flip reads. In one noisy run, cell a of 7802 fired one stage early, at a read that sat
  0.06 step below its threshold. [K]
- One check goes the other way: from the measured sigma I expected 3.6 FIRE bits to differ from the quiet runs,
  and 1 did. So the figure above may be somewhat high for firing reads. [I]

In the terms of the design note (second version, B.2): the measured r is neither "near 0.1" nor "near 0.33". It
is in between.

---

## 2. What was read, and how it was checked

**The runs** [K]. The 4 quiet runs (stage Q) and the 12 noisy runs (stages N1 to N3) of instances 7802 to 7805.
The untrained control run of 7802 was verified with the others and not used.

**The branches**, fetched by name, one commit each:

| Branch `evidence/learned-dnf-circuit-campaign-6-c1-…` | Commit |
|---|---|
| `Q-a`, `Q-b` | `7361a444`, `9dc06b78` |
| `N1-a`, `N1-b` | `38ee6bbb`, `56cc33c8` |
| `N2-a`, `N2-b` | `6c401e7f`, `eec037c8` |
| `N3-a`, `N3-b` | `788d9934`, `3b68a15a` |

These are the commits of `REPORT.md` section 13.

**Integrity** [K, `out/VERIFY.json`].

- The 12 noisy traces were reassembled from their 24 parts as `PARTS.json` says. Every part and every reassembled
  file has the size and the SHA-256 recorded there: 24 of 24, 12 of 12.
- All 201 files listed in the eight `COLLECTED.json` have their recorded size and SHA-256.
- The 68 hashes that the 17 runs' own `record.json` hold for their evidence files agree too.
- In all: 269 checks, 0 bad. No file of a run is outside `COLLECTED.json`.

**The readers** [K]. The reads are extracted by the repository's own code, at `ecfcd1c1` (the head of
`research/learned-dnf-circuit-campaign-6-impl`), unchanged: campaign 5's `plans4.network` and
`reads4.network_reads`, and `measure.Trace`. This is the path of `analyze.rows_of`.

**The interpreter is not the pinned one** [K]. I ran Python 3.13.18 with numpy 2.5.3; the campaign pins Python
3.12.3 and numpy 2.3.5. To see whether that matters, the script compares its reads with two sets of numbers of the
pushed analysis (`RESULTS.json`, SHA-256 `1b6e21f2…98e8e2`): the 72 stored voltages of comparison M7 and the 680
FIRE latencies of comparison M3. **All 752 are reproduced with a difference of exactly 0.**

**The words** [K]. In 11 of the 12 noisy runs, every port's word equals the quiet run's. In `7802-n2` the word of
a's two ports is `sssFsFF` where the quiet run has `ssssFFF` (section 4).

---

## 3. What was measured

For each noisy run, each slot and each cell that receives a pulse, the read is compared with the read of the same
slot in the quiet run of the same instance: **874 pairs of reads** with the same FIRE bit, and 2 with a different
one. [K]

Three things are in the pushed traces, and I measured each on the reads where it can be seen:

| Quantity | Where it can be seen | Why not elsewhere |
|---|---|---|
| **The stored voltage** of each port before a read | every read | |
| **The score** of a read: the peak of the main charge `q` | reads that stay **silent** | In a firing read the guard stops the charge at the FIRE (`REPORT.md` section 3), so the peak is cut |
| **The FIRE level**: `q` at the moment the cell fires (`q_peak_before_fire`) | reads that **fire** | A silent read never reaches it |

**The unit.** A "step" is what one stage of training adds to the score of that read, taken from the quiet run of
the same instance: the difference of `q` between two successive silent training reads. For a pair read a step is one
dose on each of the two ports; for a line of c it is one dose on one port. Steps are 0.032 to 0.038 of the FIRE
level [K, `out/AUDIT.json`, `quiet_ladders`]. The budget, in the same unit, is 0.328 to 0.336 on the four instances
[K: `budgets.K3.<cell>.training` over the cell's step, from `PREDICTED.json` at `b6e319f6`].

**Where the injected noise enters** [K, `research/circuit/cell.spice`]: on the reference of the FIRE comparator
(`nzm`), on the reference of each port's sensor comparator (`nzc`), and on the common-mode reference of each port's
integrator (`nzo`).

---

## 4. The measurements

All noisy minus quiet. Source: `out/AUDIT.json` unless said.

### 4.1 The stored voltage [K]

Over the 72 port-runs (6 ports, 4 instances, 3 rounds):

| | Standard deviation | Largest |
|---|---|---|
| Before the port's first read of the run | 0.045 mV | 0.120 mV |
| After its last write | 0.045 mV | 0.124 mV |
| Gained between the two, during training | 0.014 mV | 0.032 mV |
| Within a run, after the last write | below 0.0001 mV | |

- The offset of a noisy run is there **before any training**, and training adds little to it.
- Once a port has stopped writing, its stored voltage does not move during the rest of the run.
- This offset is only one of the two parts of the constant `b` (section 5.1): the other acts on the read and is
  not in the voltage across the capacitor. So 0.045 mV is not to be set against `b = 0.111` mV.

### 4.2 The doses [K]

On the 253 reads where both runs write the port once: the dose differs by 0.0080 mV (standard deviation), 0.026 mV
at most. The constant is `d = 0.009` mV. The quiet doses are 1.349 mV on average.

### 4.3 The score of silent training reads [K]

| Read | Reads | Standard deviation | Largest | Of which not explained by the stored voltage |
|---|---|---|---|---|
| pair (a, b) | 80 | 0.061 step | 0.142 step | 0.055 step |
| line (c) | 93 | 0.072 step | 0.173 step | 0.060 step |

The last column removes what the stored-voltage difference of 4.1 predicts (for a pair, the mean of its two ports,
which is the mapping's own assumption of equal ports [K: `MAPPING_U.md` section 1]). Most of the score noise is
therefore noise of the read itself, not of the memory. [I]

### 4.4 The FIRE level [K]

| Read | Reads | Standard deviation | Largest |
|---|---|---|---|
| pair (a, b) | 344 | 0.019 step | 0.076 step |
| line (c), one line arrived | 153 | 0.019 step | 0.058 step |

- A run's mean FIRE level differs from the quiet run's by 0.002 of the FIRE level at most (about 0.05 step): there is
  little offset between runs on the FIRE level.
- The both-lines reads of c (12 reads) move by 0.0002 to 0.0011 of the FIRE level. I give no figure in steps for
  them: the network runs hold no ladder of both-lines reads to define a step.

### 4.5 Put together [I]

The decision of a read is "score above the FIRE level". Its noise is the noise of the score minus the noise of the
level. Taking the two as independent:

| Read | Sigma | Three sigma | Budget |
|---|---|---|---|
| pair (a, b) | 0.064 step | **0.19 step** | 0.33 step |
| line (c) | 0.074 step | **0.22 step** | 0.33 step |

In mV of one port, 0.064 to 0.074 step is 0.086 to 0.100 mV, against the model's 0.147 mV.

### 4.6 The same without the quiet runs [K]

A quiet deck has no noise source, so its time steps could differ from a noisy deck's, and part of 4.3 to 4.5 could
be that and not noise. To check, the script compares the three noisy runs of an instance among themselves, slot by
slot, with no quiet run:

| | pair | line |
|---|---|---|
| Score of silent training reads | 0.065 step | 0.079 step |
| FIRE level | 0.018 step | 0.019 step |
| Three sigma, put together | **0.20 step** | **0.25 step** |

These agree with 4.3 to 4.5. The quiet run is a fair reference.

### 4.7 The read that flipped [K]

`7802-n2`, cell a, layer 1:

| Slot | Quiet run | Noisy run |
|---|---|---|
| 3 (after 3 doses) | silent, peak 0.9736 | **FIRE**, at 0.9750 |
| 4 | FIRE, at 0.9759 (after 4 doses) | **silent**, peak 0.9753 (still 3 doses) |
| 5 and after | FIRE | FIRE (after its 4th dose) |

- The scan had placed this crossing 0.059 step above stage 3 (`PREDICTED.json`, `question_2.a.below_stages` =
  15/256). The quiet run agrees: its stage-3 peak is 0.0023 under its FIRE level, 0.06 step.
- In the noisy run the same state fired once (slot 3) and then did not (slot 4, with a higher peak). So the FIRE
  level itself moved between two reads.
- The cell then wrote its fourth dose and ended in the predicted state.
- By the prediction record this port had no room of its own at budget K3 (`learning_ports.a1.own_room` is false),
  so it was not a counted port. I state the fact; I draw nothing from it about any claim.

### 4.8 A consistency check that does not quite close [I]

If each read's margin moved by an independent Gaussian of the sigma of 4.5, how many FIRE bits should differ from
the quiet runs? The margins are each crossing's place in its step, from the pushed record (`question_2`). Over 672
reads: **3.6 expected, 1 seen** (the flip above; its second slot is a consequence of the first).

- Most of the expectation is one place: a of 7804 sits 0.105 step above its threshold and fires 54 times in the
  three noisy runs; 2.2 flips were expected and none occurred. The chance of none is about 0.11.
- Overall, the chance of seeing 1 or fewer when 3.6 are expected is about 0.13. It is not a contradiction. It
  suggests that the noise of a firing read is smaller than what silent reads show, or that the two noises are not
  independent, or that the noise is not Gaussian. I cannot tell which.
- So 0.19 to 0.25 is better read as **an upper estimate for firing reads**, and a fair one for silent reads.

---

## 5. The three constants: how they were defined, and whether the audit measures the same things

### 5.1 How campaign 3 defined and measured them [K]

**One instrument for `b` and `w`: the FIRE latency.** A cell that is further above its threshold fires sooner. The
definitions are in phase 1's `research/network-circuit/phase1/constants.py` (`6644fb58`, its docstring and the
function `port`) and its note `NOISE.md` (`39cfbd14`, section 1):

- **The slope**: FIRE latency per mV of stored voltage at the trained state, a secant over the isolated reads of
  the port's scan.
- **`w`, within a run**: "scatter of the FIRE latency about the mean of its run, divided by the slope".
- **`b`, between runs**, the *run offset*: "for each run, (FIRE latency without noise − mean FIRE latency of the
  run) / slope". It is "what one run adds to every read of a port, the same for the whole run".
- Both are taken only on a noisy run that gave the word of the run without noise, with at least 3 FIREs. Both are in
  mV across the storage capacitor **of one port**, on **reads that fire**, at the trained state.
- **`d`, per dose**: "root mean square of (dose in a noisy train − dose of the port without noise)".

**Where the run offset comes from** (`NOISE.md` section 3): two effects of the port's integrator amplifier, each
with a coefficient of one. The preset samples the amplifier's noise, and that value stays in the stored voltage
for the whole run (0.065 mV). And the slow part of the amplifier noise has a mean over a run that is not zero
(0.074 mV): "the stored node follows it, so every read of the run sees the port shifted by it". The stored voltage
before the first pulse "explains little of the run offset". The two ports of a cell correlate at 0.23.

**The values.**

| Constant | Value | Where it was measured | Estimator |
|---|---|---|---|
| `b` | 0.090, then **0.111** mV | 0.090: phase 1, 55 run offsets on 12 ports of 3 development instances (`NOISE.md` section 2). 0.111: campaign 3's declared comparison M5, 38 port-runs of its noisy network runs, one noisy run per instance (`REPORT.md` line 198, `3fe6505a`; `PREDICTION.md` line 236, `6aa0f405`) | the root mean square of the run offsets, not centred. In M5: `(median of the quiet run's latencies − mean of the noisy run's) / slope` per port-run (`analyze.py` lines 253 to 257, `d2c3a2e0`) |
| `w` | 0.064, then **0.094** mV | the same two places | the root mean square over port-runs of `stdev(latencies of the run) / slope` |
| `d` | **0.009** mV | phase 1: 0.0081, 0.0082 and 0.0088 mV on its three development instances (`phase1/CONSTANTS.json`, `dose_noise_sd_mV`) | as defined above. That 0.009 rounds the largest of the three is my reading [I]; I found no line that says so |

M5's slope is the port's `train_18_quiet.slope_per_mV`, from the measures of campaign 3.

**How decision 5 carried them over** [K]. Campaigns 2 and 3 fixed 0.090, 0.064 and 0.009 beforehand
(`network-circuit-ring/README.md` section 5, `26a12e53`; campaign 3's `predicted.py`, `FIXED_NOISE_MV`). Phase 0 of
the learned circuit proposed "those observed in campaign 3 (M5: 0.111 mV between runs, 0.094 mV within a run),
larger than the fixed constants of campaigns 2 and 3 (0.090, 0.064), with 0.009 mV per dose; for a joint read, the
offsets of its two ports added linearly (a common cause cannot be excluded)"
(`research/learned-dnf-circuit/README.md` lines 165 to 167, `a8068deb`). Decision 5 fixed them (`DECISIONS.md`,
`49684afc`), and campaign 5's `PREDICTION.md` (lines 264 to 268) applies them.

So `b` and `w` come from a **descriptive comparison** of campaign 3, on **single-port reads of ring cells**, by
**latency**. They were carried to pair reads and routed lines without being measured on them.

### 5.2 Is the audit's counterpart the same quantity?

| Constant | The first version's counterpart | The same quantity? |
|---|---|---|
| `d` | the dose of a noisy run minus the dose of the same slot in the quiet run (4.2) | **Yes, in substance** [I]. Phase 1 compares with the port's mean noise-free dose, the audit with the same slot's. Seen 0.008 mV; constant 0.009 |
| `w` | all the noise of a read that the stored voltage does not explain (4.3), with the FIRE level (4.4) | **No.** That figure mixes two things: the scatter within a run, and what a run adds to all its reads through the slow part of the amplifier, which campaign 3 counts in `b`. It is also read on silent and firing reads with another instrument |
| `b` | the stored-voltage offset of a run (4.1) | **No.** It is only the first of the two effects of `NOISE.md` (the preset's sample). The second acts on the read and is not in the voltage across the capacitor, which is what 4.1 measures |

The total of section 4.5 does not depend on this pairing: it is all the noise of a read, however it is split.

### 5.3 The audit's reads, cut as campaign 3 cut them [K for the figures, I for the comparison]

Added in this version, from the reads already extracted (`noise_audit.py constants`, output
`out/CONSTANTS_AS_CAMPAIGN_3.json`). For each noisy run and each kind of read: an offset (the run's mean difference
from the quiet run) and a scatter about it. The offset's root mean square has the part due to the scatter removed.

With the audit's own instrument (score of silent training reads, FIRE level of firing reads):

| Read | What a run adds to its reads | Scatter within a run | Both |
|---|---|---|---|
| line of c (one port) | 0.057 step, **0.077 mV** | 0.048 step, **0.064 mV** | 0.074 step, 0.100 mV |
| pair of a, b (two ports) | 0.043 step | 0.047 step | 0.064 step |
| the constants, one port | `b` = 0.111 mV | `w` = 0.094 mV | 0.147 mV |

- For a line, a step is one dose of one port (1.349 mV on average), so the mV are direct. For a pair I give steps
  only: a step is a dose on both ports, and the constants are per port.
- On the lines, each of the two is **about 0.69 of its constant**.
- 24 run-and-kind groups per read type, of 3 to 5 silent reads each: the split between the two columns is rough.
  Their combination is the 0.19 and 0.22 step of 4.5.

With campaign 3's own estimator on the FIRE latency, which needs no step, but with no slope to turn it into mV:

| Read | Port-runs | Run offsets, rms | Scatter within a run, rms | Ratio | Scatter of the quiet run |
|---|---|---|---|---|---|
| pair of a, b | 23 | 0.0075 unit | 0.0071 unit | 1.05 | 0.001 unit |
| line of c | 24 | 0.0117 unit | 0.0107 unit | 1.09 | 0.002 unit |
| campaign 3, M5 | 38 | 0.111 mV | 0.094 mV | 1.18 | |

The ratio needs no slope and can be compared: 1.05 and 1.09 here, 1.18 in campaign 3. The noise has the same shape
as campaign 3 found. (23 and not 24 for the pairs: a of `7802-n2` did not give the quiet word.)

### 5.4 `b` and `w` in mV by campaign 3's definition [K for the figures, I for the reading]

Added in the third version. Source: `noise_audit.py m5`, output `out/M5_AS_CAMPAIGN_3.json`.

**What was fetched and checked** [K]. The branches `evidence/learned-dnf-circuit-campaign-6-c1-M1-a` (`90ce4b9b`)
and `…-M1-b` (`f0b3b4ea`): the ten calibration decks of 7801 to 7805. All 102 files of their two `COLLECTED.json`
have the recorded size and SHA-256, and so do the 40 hashes of the runs' own `record.json`: 142 checks, 0 bad
(`out/VERIFY_M1.json`). No trace of stage M1 is split.

**The slope** [K]. Phase 1's `secant`, copied verbatim, on the firing reads of each kind in the instance's guard-on
deck (isolated reads, one per stage, read by the repository's `reads4.calibration_reads`), at the trained state:
the stored voltage of the deck's first firing stage, which equals the need on all 16 kinds. For a pair the stored
voltage is the mean of its two ports. With one point per stage, the secant runs from the trained stage to the
next one. The 16 slopes are 0.076 to 0.117 time unit per mV.

**The estimator** [K]: campaign 3's M5, on the 47 port-runs of 5.3.

| Read | Port-runs | `b`: run offsets, rms | `w`: scatter within a run, rms | Three sigma, in steps |
|---|---|---|---|---|
| pair of a, b | 23 | **0.080 mV** | **0.074 mV** | 0.24 |
| line of c | 24 | **0.118 mV** | **0.106 mV** | 0.35 |
| all | 47 | 0.101 mV | 0.092 mV | |
| the constants | | 0.111 mV | 0.094 mV | 0.33 |

By this definition the constants are about right on the lines of c, and about a quarter too large on the pairs.

**Why I do not take these figures at face value** [I].

1. **The slope is too small where it is used.** Latency falls fast just above the threshold and then flattens: one
   stage further, the slope is 0.65 to 0.67 of itself [K]. The secant spans a whole dose on the strong side of the
   trained state, so it understates the slope at the trained state, and the mV come out too large. A parabola
   through the first three firing stages gives the slope at the trained state itself; with it, `b` and `w` become
   0.069 and 0.064 mV on the pairs, 0.100 and 0.090 mV on the lines. That is a sensitivity, not the definition.
   Phase 1 and campaign 3 took their slope from scan reads around the state, which the calibration decks do not
   have.
2. **The FIRE bits contradict them.** If the margin of a firing read moved by a Gaussian of
   `sigma = sqrt(b^2 + w^2)`, then, from each crossing's place in its step, **8.2 of the 497 firing reads** at the
   trained state should have differed from the quiet run. **None did.** The chance of none is about 0.0003. With
   the three-point slope: 5.2 expected, none seen, chance about 0.006. The audit's own figure fares better and is
   still on the high side (section 4.8).

So campaign 3's instrument, with the only slope the pushed records give, overstates the noise that actually moves
a read across its threshold. By how much I cannot say from these runs.

**What would settle it** [I]: latencies at stored voltages close around the trained state, on both sides. The
scans of stage M2 read each kind at states half a stage apart and closer near the threshold; whether they record
the latency I have not checked, and I did not fetch them.

### 5.5 What this means for a budget [I]

- **This is the main open question, and it is now sharper.** The two instruments give different mV on the same
  runs: on the lines, 0.077 and 0.064 (score and level) against 0.118 and 0.106 (latency over the deck's slope).
  A budget must say which it uses.
- The dose constant is right under both.
- The observed FIRE bits are the only evidence that does not pass through an instrument, and they favour the
  smaller figures.
- Read strictly by campaign 3's definition, these runs give no ground to lower `b` and `w` for the lines of c.
  Read by what flipped, they do.
- A measured figure is not a budget. Setting one is the owner's decision.

---

## 6. What the measured figure would give, on the development batch only [I]

On the seven instances of the batch that have budgets (`rehearsal/PREDICTIONS_BATCH.json`, `b825d6aa`, SHA-256
`e2e9e572…cc89`), from each crossing's place in its step. "Lever 1" is the one-port testing budget for c of the
design note. Source: `out/WINDOWS_BATCH.json`.

First a check of the formula: with each record's own K3 budgets it gives back the record's `room_at_K3` for a, b
and c on all seven instances.

| r (three sigma, in steps) | a has room | b has room | c, today's rule | c, lever 1 | a, b and c, today's rule | a, b and c, lever 1 |
|---|---|---|---|---|---|---|
| 0.33 (today) | 3 of 7 | 2 | 0 | 1 | 0 | 0 |
| 0.25 | 4 | 2 | 0 | 3 | 0 | 1 |
| 0.22 | 4 | 3 | 0 | 4 | 0 | 2 |
| 0.20 | 4 | 4 | 0 | 4 | 0 | 2 |
| 0.15 | 6 | 4 | 2 | 4 | 0 | 2 |

- With today's rule for c, no instance has a, b and c together at any of these values.
- With lever 1 and r between 0.20 and 0.25, 1 or 2 of the 7 do.
- Seven instances is very few, and a measured three sigma is not a budget: a budget would be set above it.

**What this means for the choice of the design note** [I]. The measured noise alone does not open the noise claims
for c. With lever 1 and constants measured on this deck, a, b and c would all count on roughly one instance in
eight (r = 0.20) to one in sixteen (r = 0.25) by the windows of the design note's B.2, which assume that a crossing
lands anywhere in its step with equal chance; the batch gives 1 or 2 of 7. With a larger dose on top, more.
Whether to measure the constants again, and at what value to set them, is the owner's decision.

---

## 7. Not checked, and limits

- **The interpreter was not the pinned one** (section 2). The 752 reproduced values are the only evidence that it
  does not matter.
- **Four instances, all eligible**, three noisy runs each, one noise model (the injected one), one simulator. The
  figures describe these runs.
- **The score noise is seen only on silent reads, the level noise only on firing reads.** Putting them together
  (4.5) assumes that they are independent and that a firing read has the score noise of a silent one. Section 4.8
  suggests this overstates the noise of firing reads.
- **Three sigma is an extrapolation** from 173 silent reads and 497 firing reads, as if the noise were Gaussian. I
  did not test its shape.
- **The step** is the quiet run's own, between successive silent reads. Steps grow by about 4 % from one stage to
  the next, so a figure in steps carries an error of that order. For the FIRE level I used the last silent step,
  which is slightly smaller than the true one: the level's figure is slightly high.
- **Not measured, for lack of a step in the pushed network runs**: the silent test reads (one port of a or b
  alone, the empty read of c) and the both-lines reads of c. Their raw differences are in `out/PER_READ.json`. A
  step for them would need the calibration decks of stage M1, which I did not fetch. I stopped there and
  reconstructed nothing.
- **The FIRE level** is `q` when the protection latch rises, which is a little after the comparator trips. For the
  same slot in two runs the delay is nearly the same, so the difference is a fair measure; I did not quantify the
  remainder.
- Section 5.1 rests on phase 1's `constants.py` and `NOISE.md`, campaign 3's `analyze.py` (lines 215 to 262),
  `predicted.py` (its constants) and the two lines cited of its `PREDICTION.md` and `REPORT.md`. I did not read
  campaign 3's `RESULTS.json`, nor recompute its 0.111 and 0.094. I did not read `research/circuit/noise.py`
  beyond its first 45 lines.
- **`b` and `w` in campaign 3's definition (5.4) rest on a slope taken over a whole dose on one side of the
  trained state.** The three-point slope is my own construction. I did not fetch the scans of stage M2, nor check
  whether they record latencies.
- Of stage M1 only the guard-on decks of 7802 to 7805 were read; 7801's and the guard-off decks were verified and
  not used.
- The untrained run, and the stages M2 and M3, were not used.
- Section 4.8 uses each crossing's place in its step from the prediction record of attempt c1. It is used only to
  test the noise figure; no room and no count is computed for the campaign's instances.
- The script was written and run by me in this session. No one has reviewed it.

---

## 8. Files

The audit was computed in a local folder, outside any git tree. On this branch the script is
[`dev/noise_audit.py`](dev/noise_audit.py); in the table below it appears under its local name `code/noise_audit.py`.
The outputs under `out/` are named here by their SHA-256.

| File | SHA-256 |
|---|---|
| `code/noise_audit.py` (781 lines; the first version's was `d9bc930d…9e85`, the second's `2fa8886c…1213`) | `abebb63633323e823bc7bdaf28542cd5f08e2eaae2ae84671b8006da3733bb87` |
| `out/VERIFY.json` (the integrity checks) | `b29bc6c0ea610f7bd77a809939c7ddf74d12a63fdf8c1384188df1a1637bc864` |
| `out/RUNS.json` (the 17 runs and their words) | `7ff35005c69df910ebeb6bb2099f7c7a8c3ce5cdfc576fc467320a6b3ca73b3f` |
| `out/AUDIT.json` (every table of this note) | `a1d0609c25c59a76497b1b246ef89242a36a8272c45d5d8fc286fe6b418ec160` |
| `out/PER_READ.json` (the 876 compared reads) | `f42d97f5b96d507a69230cd565bf16d70b45694bf6d36d805abf18e8c4af43ec` |
| `out/WINDOWS_BATCH.json` (section 6) | `49a315456a09f61e000cca30f579a8db373c3774a88a68f780707300eadee69e` |
| `out/CONSTANTS_AS_CAMPAIGN_3.json` (section 5.3) | `f5c9d12fced213501cf63ae59ec4be8cb94c86a76caf1ecb700bda05580381d3` |
| `out/VERIFY_M1.json` (the integrity checks of stage M1, new) | `b82d16050fae2c0c56178569ed648e2551c8cd8a5d040e4c81056b2b2c415b4a` |
| `out/M5_AS_CAMPAIGN_3.json` (section 5.4, new) | `04399aca6d251e01dc1119613906f78b5f1cfdbb122aa6ffe88fc6dab1c05409` |
| `out/reads/<run>.json` (17 files) and the four stdout files | in `out/SHA256SUMS` (`f98536ef…64ee`) |

The commands, from that folder, with `R` the checkout at `ecfcd1c1`:

```
python3 -I code/noise_audit.py verify  ev out
python3 -I code/noise_audit.py reads   R ev out
python3 -I code/noise_audit.py analyze R ev out R/research/learned-dnf-circuit-campaign-6/stages/c1/PREDICTED.json RESULTS.json
python3 -I code/noise_audit.py windows R/research/learned-dnf-circuit-campaign-6/rehearsal/PREDICTIONS_BATCH.json out
python3 -I code/noise_audit.py constants out
python3 -I code/noise_audit.py verify-m1 ev out
python3 -I code/noise_audit.py m5 R ev out R/research/learned-dnf-circuit-campaign-6/stages/c1/PREDICTED.json
```

Since the first version the script gained the commands `constants`, `verify-m1` and `m5`. `AUDIT.json`,
`PER_READ.json` and `VERIFY.json` are byte-identical to the first version's.

**One defect of mine, found and fixed in this version.** The first run of `verify-m1` wrote its report under the
name `result.json`: a loop variable had the same name as the parameter that holds the report's name. The checks
themselves were right (142, 0 bad). I renamed the parameter, removed the misnamed file and ran it again; `VERIFY.json`
of the first version was never touched.

`ev` holds the eight evidence folders as on their branches. `RESULTS.json` is the file of the analysis branch
`feb0927f`.

The local folder is temporary. The script is on this branch; where the outputs are kept is said in this folder's
`README.md`.

---

## 9. Changes since the first version

1. **Section 5 rewritten**, at the coordinator's request after the owner's "on continue": how campaign 3 defined
   `b`, `w` and `d` (5.1), whether the audit's counterparts are the same quantities (5.2), the audit's reads cut
   as campaign 3 cut them (5.3, a new computation on reads already extracted), what would be the same quantity
   (5.4), and the consequence for a budget (5.5).
2. **A wrong statement withdrawn.** The first version paired `w` with all the noise of a read beyond the stored
   voltage, and `b` with the stored-voltage offset alone. It concluded that the margin was mostly in `b` (0.045
   against 0.111). By campaign 3's definition, part of what I had put in `w` belongs to `b`. Cut correctly, each is
   about 0.7 of its constant. The bullet of section 1 that carried the wrong conclusion is replaced.
3. **Nothing measured in sections 2 to 4 and 6 changed.** The headline (0.19 to 0.25 step against 0.33) stands.
4. `noise_audit.py` gained one command; one output file was added; "Not checked" and the file table follow.

**Third version.**

5. **Section 5.4 replaced**: it was "what would be the same quantity"; it is now that quantity, measured, with the
   slope from stage M1, and two reasons not to take it at face value.
6. **Section 1's bullet on the constants rewritten again.** The second version said that `b` and `w` were each about
   0.7 of their constants. That holds for the audit's own instrument. By campaign 3's definition they are about at
   the constants on the lines. Both are now given, with what the FIRE bits say.
7. Section 5.5, "Not checked" and the file table follow. The defect in `verify-m1` is declared in section 8.

**Fourth version.**

8. Section 8 only: the path of the local folder is replaced by where the script is on the branch, and the sentence
   that asked where to keep the files is replaced by a pointer to the folder's `README.md`.
