# Combined campaign: inverter cells and layered networks — preregistration

**Status: candidate for the freeze, not pushed.** It is pushed alone, after the freeze commit and before the seed draw. Every number marked [K] is measured, [I] inferred, [G] an estimate. Code: research/layered-campaign-int at the freeze commit (on main 3f27bb36; candidate 54689b62, not yet pushed); frozen file list FREEZE_PINS.json (113 files by sha256) and FREEZE.txt. Sources: CAMPAIGN_PLAN_DRAFT.md (8af2cba), PLAN_NOTES_3.md, DECISIONS_3.md, YIELD_LOT_RULE_2.md (da23523) and the yield lot (evidence/yield-lot-K01…K12; aggregate at a398d1f2), the pre-freeze dry runs of 2026-11-25 (evidence/prefreeze-dryruns, evidence/prefreeze-g2), NOISE4_REPORT.md (458bc7a6).

## 1. What is tested

Three drawn groups, one function each, every instance an independent SKY130 mismatch draw (setseed S on the whole deck), at 27 °C, typical corner, at the family design point (vhi 0.7, reltol 1e-5, junction areas):

| Group | Function | Circuit |
|---|---|---|
| G1. NOT in one layer | y = ¬x | 1 C5 inverter + 1 copy cell |
| G2. Layers without NOT | (x0∧x1)∨x2 | both + copy → either → copy (3 layers) |
| G3. Layers with NOT | y = x0 ⊕ x1 | 2 C5 inverters + both, both → either → copy (3 layers) |

## 2. The primary claim: a direct test

For each instance, before any network run (stage D, same deck and seed, so the same devices):
- every R cell is measured alone (scans from the preset, the family's order, repeat rule v2), fitted, and gated at K0 and K3 (`fit3`, one-port rule for the either cell; DECISIONS_3.md);
- every inverter is gated in the network deck itself (`invinst.indeck`, CircuitInverterGate.lean, K0, K3, StateBound);
- the prediction is written and sealed (sha256 manifest, ENV.json hash included): every training word, every output on all 2^m patterns, every cell bit, the skew slots' silence, eligibility at K0 and room at K3.

**Sealing (fixed now).** (a) Each instance's prediction is sealed BEFORE its own stage N starts. (b) The sealed prediction leaves the machine before that stage N starts: in one append-only commit on its own log branch `evidence/combined-seals-K<nn>`, the machine appends a line (instance, seal sha256, UTC time) to SEALS.txt and adds the full sealed folder `seals/<inst>/` (every file its SHA256SUMS lists, a few kB), then pushes it plainly (`sealpush2`); stage N starts only after the push succeeds. A second seal of the same instance is refused. The push time is the one GitHub records, not the commit date. The coordinator verifies every log after the campaign against the stage-N start times recorded on the machine. Stage N refuses to start without the seal-log commit, and records that commit in every stage-N record. A stage N with no seal pushed before it counts as not sealed and has no prediction. A duplicate machine fetches the log branch by name and checks that the commit is on the branch, that the SEALS.txt line equals the sha256 of the folder's SHA256SUMS, and that the seal verifies, before it writes its own comparison. (c) The one analysis regenerates every prediction from the stage-D records alone, on a machine other than the one that ran the instance, and checks it byte-identical to its seal. A mismatch is reported as a defect and that instance has no counted prediction.

Then stage N, the network trained by its own pulses and tested on every pattern, is compared **directly** with the sealed prediction.

- **K0 (no noise)**: on every eligible instance, one run. **One differing letter, cell bit or output refutes.**
- **K3 (noise)**: on every instance with room, 3 noisy runs (rounds 1–3, noise seed 10·S + n), each predicted to train and answer as sealed. **One difference refutes.**
- **No prediction, no claim.** A run on an instance without eligibility (K0) or without room (K3) is reported plainly as observed. It is never "predicted to fail", and it counts for no claim and no refutation.
- **Secondary control (not a claim):** the kernel's recognition theorem applied to the stage-N traces (`layered_recognition_at`; `layered_inverters_chained` for G1 and G3), reported per instance beside the direct verdict.

## 3. Sizes, fixed by the yield lot (YIELD_LOT_RULE_2, before any campaign data)

Yield lot on 56 dev seeds 6102–6225 (stage D only; these seeds count for nothing) [K, research/layered-stage-d a398d1f2, dev/yield_lot/aggregate]: eligible at K0 / with room at K3, with the lower 90 % Wilson bound:

| Group | K0 | K3 | N (rule: max(⌈20/L0⌉, ⌈5/L3⌉) ≤ 80; NOT1 fixed) | expected K0 / K3 counted |
|---|---|---|---|---|
| G1 NOT | 8/8 (L0 0.747) | 5/8 (L3 0.348) | **60** | 60.0 / 37.5 |
| G2 (x0∧x1)∨x2 | 19/24 (L0 0.630) | 3/24 (L3 0.051) | **32** (N3 = 98 > 80) | 25.3 / 4.0 |
| G3 XOR | 21/24 (L0 0.725) | 6/24 (L3 0.135) | **37** | 32.4 / 9.2 |

**Declared before the campaign, by the rule: "G2: K3 not expected to be established (N3 = 98 > 80)."** The sizes were accepted by the owner as the rule gives them, with no change after the rates were seen. The lot ran before noise4, so its inverter K3 verdicts used the noise.json allowance; a read-only recount under noise4 (recount_noise4_lot.py) gives no change: NOT1 5/8 and XOR3 6/24 with room, every inverter keeping its room, the smallest margins moving by under 0.001 x. The most frequent K3 failing clauses in the lot: G2 c1_0 (anchor (1,2) and stop margin) and c1_1 (early silence); G3 c1_1 (anchor (1,2) and stop margin).

## 4. "Established" (fixed before any data)

A counted instance: eligible (K0) or with room (K3), fixed by stage D (§8 failure rule). The thresholds below count HELD instances: counted, completed, every comparison agreeing, no premise flagged. Per group and level:

| Level | established | held on k instances, not established | held on one instance | not established |
|---|---|---|---|---|
| K0, G1 | ≥ 30 | 2 ≤ k < 30 | 1 | 0 |
| K0, G2 and G3 | **≥ 20** | 2 ≤ k < 20 | 1 | 0 |
| K3, every group | ≥ 5 | 2 ≤ k < 5 | 1 | 0 |

- A refutation on any counted instance is reported whatever the count.
- **All three groups together** ("NOT, layers without NOT, and layers with NOT"): established at a level only if each group is.
- P(not established | every prediction right) [I, binomial, at the lot rate / at its lower 90 % bound]:

| | G1 K0 | G1 K3 | G2 K0 | G2 K3 | G3 K0 | G3 K3 |
|---|---|---|---|---|---|---|
| P(not established) | ≈ 0 / ≈ 0 | ≈ 0 / ≈ 0 | ≈ 1 % / ≈ 40 % | ≈ 63 % / ≈ 98 % | ≈ 0 / ≈ 0.5 % | ≈ 3 % / ≈ 43 % |

Stated plainly: at the lower bounds, G2 at K0 and G3 at K3 may well end "held, not established"; G2 at K3 is expected not established.

## 5. Machines, budget, fallback

- Measured cost per instance, CPU-min [K, yield lot and the pre-freeze dry runs of 2026-11-25]: stage D with the inverter gates G1 ≈ 6, G2 ≈ 48, G3 ≈ 66 (+ ≈ 2 for G1 on an audited instance); N0 G1 1.6, G2 27, G3 48; each noisy round G1 2.1, G2 ≈ 38.5 (three in parallel), G3 62; one XOR3 instance in all ≈ 5.15 core-h (plan 4.94). Noisy rounds run in parallel after N0.
- 12 machines × 4 cores × 6.5 h = 312 core-h; **window 6.5 h, ceiling 280** (the owner's choice). The rehearsal measures the real per-instance cost on all 12 machines; if it exceeds the plan, the sizes are reduced by the cut order below, and fixed before the draw. Planned ≈ 168 core-h for 60 / 32 / 37 (G1 11.6, G2 55.4, G3 101.2), plus controls and D4 audits.
- **The rehearsal starts all 12** (12 set up and passed envcheck on 2026-11-24 [K]). A machine that fails envcheck or its rehearsal share is dropped before the draw.
- **Fewer machines: same sizes, longer campaign** (the owner's choice). With m working machines (8 ≤ m < 12), the window is lengthened so that m machines give the same 280 core-h ceiling: 280 / (4 m) h at most, about 8.75 h on 8 machines . Fixed at the end of the rehearsal, before the draw. Below 8 machines, the campaign is postponed.
- **Cut order if the ceiling binds anyway:** the yield-lot rule's order only (YIELD_LOT_RULE_2.md, da23523): XOR3 from N down to N0, then ANDOR3, then alternately below N0, each cut declared; NOT1 never. A job not started is "not run", listed with its seed, never replaced.

## 5a. Noise, in one place

- **What is injected.** Campaign (a)'s injected model on every R cell (noise.json: b 0.111, w 0.094, d 0.009 mV, FAKEPID 10·S + n). On every C5 inverter, noise3's two sources: the FIRE comparator's input noise (vnzm, white and flicker) and the help mirror's shot charge into vq.
- **What is budgeted at K3.** For the R cells, noise.json's allowance (campaign (a)'s rule). For the inverters, the injected level as measured in a trace (noise4_budget.json: σ_δ 417.6 µV, ×1.25 over noise.json, and σ_η 8.653e-4 x, ×1.10). This is an estimate from two noise-seed draws (98011 and 98014), the larger of each taken.
- **Rounds.** Rounds 1–3 with noise seeds 10·S + n. Noise is off in stage D and N0.

## 6. Controls (as in campaign (a))

- **U**, untrained, one run per group on its first eligible instance: no R-cell output fires on any pattern.
- **S**, shift: one skew slot per both cell in every stage-N run: the cell stays silent.
- **Duplicate**, one instance per group on a second machine, which writes its own comparison against the original's pushed seal (§2 b): `input.spice` byte-identical; records and verdicts identical except the listed cost and wall fields; `trace.raw` byte-identical except its `Date:` line (digests when the raw file is deleted); `session.log` identical except the listed wall-clock progress lines. Judged by `check_duplicate.py` (sha256 frozen). A failure is a defect of the environment, reported; no instance is dropped.

## 7. Seeds, freeze, blinding

- **Seeds** drawn after the freeze by `draw_seeds.py` (sha256 d793da47f402d296018d62cebeb7ee01cce34c76047d80287c84b30092d20e32), with the sizes of §3 given explicitly: `draw BEACON ROUND EXCLUDED.json DRAW.json NOT1=60 ANDOR3=32 XOR3=37`. A candidate S = 10000 + (SHA-256("beacon|round|group|k") mod 90000); rejected if S or any noise seed 10 S + n (n = 0..3) is excluded or already drawn.
- **Beacon:** the drand League of Entropy "quicknet" chain (chain hash 52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971, a round every 3 s), the randomness of the first round whose time is at least 600 s after the GitHub-recorded push time of the first commit adding DRAW_ANNOUNCE.txt on branch `evidence/combined-draw` (pushed once, alone, by the coordinator after the rehearsal; only the first such commit counts). The round is therefore in the future when it is fixed: round = ⌈(t_push + 600 − genesis) / 3⌉ + 1, with quicknet's genesis 1692803367 s and period 3 s. The chain is pinned in FREEZE.txt (public key, genesis, period, scheme bls-unchained-g1-rfc9380, groupHash); the chain hash recomputes offline from them (`beacon_chain.py`), and the verifier passed three published rounds (1000000, 20000000, 34278954) and refused one-byte changes before the freeze. If both api.drand.sh and api2.drand.sh are down at draw time, the owner fetches the round from any drand relay and the frozen verifier checks it; DRAW.json carries the round's signature beside its randomness, for an offline recheck. The value is fetched by the coordinator, with api.drand.sh allowed in its environment, verified by the frozen `beacon_verify.py` (BLS signature against the chain public key, randomness = sha256(signature)), and can be rechecked by anyone from drand's public API or relays. The coordinator fetches it, verifies it against the chain's public key and publishes DRAW.json with the beacon value, the round and the announce push time.
- **Excluded seeds:** `EXCLUDED.json` made by `draw_seeds.py scan` at the freeze over every branch of the repository fetched by name (rule in the script: every 4–7-digit integer and range on any line that names a seed, FAKEPID, rehearsal or dry run), with its sha256 recorded in FREEZE.txt (first scan: seeds_sha256 78389a193da0fdcac2a97b37068de463276320188559cfed1779df495a23f2e7) and its refs and tips recorded; printed in full, ranges collapsed, in the freeze commit. It contains at least 1000–1199, 2000–2399, 5001–5020, 6001–6100, 6102–6225 (yield lot), 7101–7103, 7301–7306, 7401–7412, 7701–7710, 7801–7805, 8301–8310, 8501–8515, 9711–9770, 9801–9806, 9901–9903, 9911–9970 and their noise seeds, and explicitly 98010, 98020, 98030, 98040, 98050–98053 and 98060–98063 (unused, excluded for prudence). The scan is authoritative; ranges listed here that no branch names yet enter it once this file is pushed. The draw range is 10000–99999. The rehearsal seeds and every pre-freeze dry-run seed and noise seed (their evidence pushed first) are added by a second scan after the rehearsal, before the draw; FREEZE.txt records the first scan (seeds_sha256 78389a19…, 15,323 integers, 216 branches).
- **Frozen by sha256 (FREEZE_PINS, 113 files):** the drivers (campaign_run12 and the chain it imports), the analysis, the checks, the inverter kit (d599300d), the controls and noise (controls4/5, noise4 budget), the configs and specs, CircuitInverterGate.lean and the Lean gate files; Lean 4.35.0 by its real binary (sha256 bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38, `envcheck_layered4`, which resolves the real binary and refuses anything else, and refuses any Python but 3.13.18), ngspice 42 (sha256 820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45), SKY130 1232782c, Python 3.13.18 and numpy 2.3.5 (refused otherwise; its fingerprint hashes the package files only, cd6ab151…, the same on every machine), the configs (design point, d4_stage 0.005, scan cap 64, C5 overlay, noise constants b 0.111 / w 0.094 / d 0.009 mV).
- **Blinding:** per-instance predictions, comparisons and verdicts sealed during the campaign; progress counts only. **One analysis**, the frozen analysis script (`analyze8.py`, sha256 df2ae67c… in full in FREEZE.txt, with `d4_regate.py` 3827d1a5…; analyze7 plus the D4 rule of §8, with the seal regeneration and the duplicate judged by `check_duplicate.py`), run once and checked byte-identical on a second run. It outputs RESULTS.json with: per group and level, the counted instances, the verdict word (§4), every refuting difference with its cell and pattern and the §8 diagnostic; the observed-only list with reasons; failed and not-run steps; controls U, S and duplicate; the secondary Lean control per instance; the declared max-rule counts; the seal regeneration check of §2(c); ENV per machine; costs.
- **Prediction record reproduced** per instance, as in §2 (a)–(c): sealed before its own stage N, the seal hash pushed to the machine's log branch first, and every prediction regenerated byte-identical on another machine by the analysis.
- **Fixes after the freeze:** any fix after the freeze means a new freeze commit, an amendment pushed alone, and a new rehearsal.
- **Machine discipline:** jobs detached; the session waits in the foreground in ≤ 590 s chunks; `uptime -s` at the start and end of each stage; no counted run is ever relaunched (missing, never replaced); every instruction acknowledged before acting.

## 8. Premises, decisions and expectations, stated in advance

- **Open premises, assumed, not proved** (the claim reads "computes f under these premises"): the leak along the trajectory (one of two fitted side rates at each time); the simulator's measured real hypotheses, supplied as outward-rounded numbers; the latch delay (measured, not bounded); the routed walk (checked per trace, no soundness proof); D4 (`d4_stage` 0.005, audited on every 6th instance).
- **Rule decision recorded:** the either cell uses the one-port test budget (campaign (a)'s family rule), adopted on 2026-11-24 after dev failures were seen (DECISIONS_3.md, 70fad23), before the freeze. **Declared comparison, counting for nothing:** room and eligibility under the superseded max rule, reported beside the claims.
- **Expectations:** the either cells and the inverter-fed outputs are the noisy ones. If a noisy run refutes, the either cell's two-port read is checked first (PLAN_NOTES_3.md). The injected noise model is pessimistic: 262 µV injected against 66 µV for the device model on a read of the stored voltage, and 1.7 to 1.8 times the drift of a read (research/circuit/DESIGN.md; research/network-noise-study/phase0/FEASIBILITY.md). The yields are measured (§3): at K3, G2 is expected not established, so "all three groups together" at K3 is expected not established either.
- **Failure rule (the owner's decisions, before the freeze).**
  - **Not completed.** A step that crashes, hits its time limit or is cut, from stage D to stage N, ends that instance's run at that level as "not completed". It is neither a refutation nor a hold. It is listed with its seed, its step and its reason, never re-run and never replaced, and it counts for nothing, for or against. The drivers' per-run time limits (campaign_run.py DEFAULT_TIMEOUT, in s): deck 120, inverters 3600, stage D 7200, seal 120, each stage-N round 7200, comparison 300, U 3600, duplicate 7200; at the limit the step's process group is killed and the step recorded "timeout" with its wall and CPU time; a step found running at a resume is recorded "interrupted". None was hit in the pre-freeze dry runs (the longest stage-N round measured: 63 CPU-min).
  - **The counted set is fixed by stage D, before stage N:** eligibility at K0, room at K3, the inverter gates. Nothing observed during or after stage N removes an instance from it.
  - **Refutation.** On a counted instance, one differing letter, cell bit or output in a completed, sealed comparison refutes, whatever premises are observed in stage N. A false premise found beside it is reported as the diagnostic, never as an excuse.
  - **Premise flagged.** If every letter, cell bit and output agrees but a premise observed in stage N (§8: the leak along the trajectory, the latch delay, the routed walk, D4) is false, the instance does not count towards "established" at that level; it is reported apart, flagged, with the clause. It is not a refutation.
  - **Counts reported side by side:** per group and level, counted, held, refuted, premise flagged and not completed, so that a group cannot look clean because its hard instances did not finish.
- **Zero-noise identity (a check of the environment, criterion fixed by the owner before the freeze, `check_noise_identity2`):** noise sources at amplitude 0 must give the same words, lessons, tests, skews and emissions as noise off, with u equal to ±1 in the record's last digit; latch dates (−4 to +17 ns seen) and inverter x readings are listed, not judged.
- **D4 (the stage-D/network scan difference), audited, rule fixed by the owner before the freeze (`analyze8.py`, `d4_regate.py`).** Every 6th instance of each group in draw order runs its stage D with solo scans; on it, the measured value replaces the constant 0.005 in its own budgets (fit.py). The constant 0.005 is the maximum of six 2x measurements rounded up; twelve 2x measurements exist before the campaign, all below it (max 0.00405), the twelfth from the end-to-end audit check of 2026-11-25 (NOT1 6220, 0.00397) [K]. The analysis reports every audited cell line against 0.005. Per group, D4* is the largest audited value; if D4* > 0.005, every unaudited instance of that group is regated from its sealed stage-D record with D4* in place of 0.005, at K0 and K3, without simulation; one whose gate then fails at a level is "premise flagged" there (not counted towards established, reported). The sealed predictions are never modified and nothing removes a refutation. This still assumes the unaudited instances are no worse than the worst audited one of their group.
- **Known limits carried:** G2's shared first-layer stimulus (the Lean witness uses separate stimuli); the either cell's two inputs are driven together in stage D (offset 0) but arrive up to about 0.7 tu apart in the network (covered by the routed-walk premise); one ngspice convergence line per run; the router's 0.02 tu grid; the inverter x_D reading written by the network runs is a linear interpolation at T+D−2 ns and can be wrong next to a reset edge (one artifact in 468 dev readings, on a fired slot); no gate, margin, prediction or comparison reads it;  the 200 ns maximum step in the network against 5/20 ns in the inverter characterisation (no effect observed on 9803); numpy 2.5.3 used for some dev in-deck gates (verdict-identical to 2.3.5, not byte-identical); the yield lot's ENV.json on 11 of 12 machines hashes the elan proxy, not the Lean binary (version 4.35.0 checked; the lot fixes sizes only); simulation only (one simulator, one corner, injected noise, no parasitics, no silicon).

## 9. Order of steps

Pre-freeze dry runs (done 2026-11-25: XOR3 9803 one clone; NOT1 9804 two clones, after fixes; ANDOR3 6104 two clones; a NOT1 D4 audit end to end) → integration branch → freeze commit (with the beacon rule of §7) → CI at the freeze → this file pushed alone → rehearsal on 12 machines (exercises the seal pushes of §2, costs them, fixes the machine count and the window; sizes only cut by §5's order) → draw announcement pushed alone, then the seed draw at the round of §7, published → campaign, blinded, with each seal pushed before its stage N → one analysis, with the seal regeneration on another machine → report → PR.
