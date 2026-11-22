# Family campaign (a): amendment 2, the network limits from the rehearsal

This amendment sets three points left open by `PREDICTION.md` section 4 and amendment 2a (`AMENDMENT_2a.md`,
SHA-256 `1508f531…`). **Nothing else changes**, in `PREDICTION.md` or in amendments 1 and 2a. It is pushed alone on
`research/function-family-campaign`, before stage D. Decided by the owner, 2026-11-22.

## 1. The campaign's network limits

**What section 4 says.** "The limits are set from the rehearsal's measured costs, by the rule
`10 × ceil(2 × expected / 10)`, in an amendment pushed before the first network stage."

**The measured costs** [K, the six rehearsal branches, every file checked against its `SHA256SUMS`]:
- `evidence/function-family-campaign-rehearsal-M1` to `-M6`, at `6071b93b`, `8ab9a063`, `d800c720`, `dbe8928f`,
  `ac6b2542` and `0bdff841`;
- all 22 network runs and all 6 R-M runs completed and reached their last date;
- the largest share of a judging limit of amendment 2a is 0.66 (8306-F4-quiet), so no run triggers the 0.75 rule.

**Why the expected cost depends on the run** [K, `family_net.network`, no simulation]. A run's cost grows with its
number of slots, and its slots grow with its needs. The rehearsal's needs are 2 or 3. A campaign run may have needs
up to 5, since Q1 and Q2 are at most 7. At needs 5 a run has up to 1.50 times the slots of the rehearsal run of the
same member and kind (X1). The untrained runs do not change. Run times also varied by up to 23 % between machines
for the same kind (F2 noisy: 1 400 to 1 724 s).

**The rule** [new]. The limit of each campaign network run is `10 × ceil(2 × r × n / 10)` s, where:
- `n` is the number of slots of that run's own calendar (`family_net.network` on the needs and unary ports of the
  prediction record), so the limit is computed from `PREDICTED.json` before stage Q;
- `r` is the largest measured seconds per slot of that member and kind in the rehearsal:

| Member | without noise (s per slot) | noisy | untrained |
|---|---|---|---|
| X1 | 37.50 | 49.00 | 19.00 |
| X2 | 44.27 | 50.00 | 19.00 |
| F4 | 45.91 | 55.45 | 16.50 |
| F2 | 42.56 | 74.96 | 13.25 |
| F3 | 37.56 | 55.08 | 11.25 |

  For F2 noisy, `r` is the largest over its 8 runs. For every other member and kind it comes from one run.

At the rehearsal's own calendars this rule gives exactly `10 × ceil(2 × measured / 10)`. At needs 5 it gives, for
example, F2 noisy 4 800 s and X1 without noise 1 350 s.

**For reference only, not the rule.** The plain rule `10 × ceil(2 × largest measured wall time / 10)` would give:

| Member | without noise | noisy | untrained |
|---|---|---|---|
| X1 | 900 s | 1 180 s | 80 s |
| X2 | 1 330 s | 1 400 s | 160 s |
| F4 | 2 020 s | 2 440 s | 140 s |
| F2 | 2 130 s | 3 450 s | 220 s |
| F3 | 2 030 s | 2 870 s | 180 s |

The per-slot rule was chosen because a campaign run with more slots than its rehearsal run would have less than
twice its expected cost under the plain rule.

**The 0.75 rule** applies to the rehearsal only (section 7). In the campaign, a run cut at its limit does not
complete, and is a missing run, never replaced.

## 2. One more rehearsal run: 8306-F2-quiet

**Why.** The noise sensitivity values of section 7 need, for each of the two instances with noisy F2 runs, a run of
F2 without noise. The run offsets and the dose without noise are measured against it. The rehearsal has one on 8303,
and none on 8306.

**The run** [new]:
- id `8306-F2-quiet`, on M5, through `family_net.py run … 8306 F2 rehearsal quiet 0 …` against the rehearsal record
  (`PREDICTED.json`, SHA-256 `c02057d3…`). `family_net.py check` admits it;
- hard timeout 2 950 s and judging limit 1 970 s, amendment 2a's F2 row;
- it runs in parallel with the campaign's measure stages and delays nothing;
- its evidence goes on M5's rehearsal branch, in a commit of its own.

**What it is used for.** Only the noise sensitivity values. It is outside the rehearsal's 22 runs and is never
counted for any check or claim.

## 3. The noise sensitivity values go in amendment 2b

`b`, `w` and `d` are fixed in **amendment 2b**, pushed alone **before any noisy campaign stage**, so that their code
does not delay the measure stages. Their code (`research/function-family-campaign/noise/noise_constants.py`, by
campaign 3's definitions) is reviewed, frozen and rerun by M3 as amendment 1 sets out, before it reads the 8 noisy F2
runs and the two runs of F2 without noise.

## Not checked

- Whether a campaign run's cost is proportional to its number of slots: assumed. The rehearsal gives one point per
  member and kind, except F2 noisy.
- The machine-to-machine spread for kinds measured once.
