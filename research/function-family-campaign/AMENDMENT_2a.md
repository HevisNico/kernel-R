# Family campaign (a): amendment 2a, the rehearsal as it can run

This amendment changes three points of `PREDICTION.md` section 7 (`385c33bf`, SHA-256 `5f9cdfe6…`), and records one
point as pending. **Nothing else changes**, in `PREDICTION.md` or in amendment 1 (`AMENDMENT_1.md`, SHA-256
`eb19e291…`). It is pushed alone on `research/function-family-campaign`, before any rehearsal run. Decided by the
owner, 2026-11-22.

## A. R-M is replaced by a reproduction on each machine

**What section 7 says.** "**R-M**: the nominal cell through the campaign's measure stages, on each machine. That
includes the unary decks, scans and preset checks."

**Why it cannot run** [K, read in the frozen code]:
- the campaign's measure wrapper (`impl/campaign_measure.py`) accepts the seeds 8501 to 8515 only;
- its stage manifests (`impl/manifests.py`) build their jobs from the campaign's seeds only;
- `topup.py` accepts 8301 to 8310, and `batch2x.py` and `family_net.py` refuse the nominal cell;
- only campaign 6's `batch6.py` accepts the nominal cell, and only for its two plain decks.

**What replaces it** [new]. On each of M1 to M6, one run:
- `topup.py cal REPO OUT 8303 on NGSPICE PDK`, the top-up's guard-on unary deck of 8303, through the frozen `topup.py`
  and `batch2x.py`;
- its limit is the campaign's rule for that kind, `10 × ceil(2 × 2 076 / 10)` = 4 160 s.

**The comparison.** Each machine's run is compared with the top-up's run of 8303 (`8303-cal-on-unary` on
`evidence/function-family-topup-M1`, at `525bb26a`, its parts joined and checked against its `SHA256SUMS`).
- The criterion is section 6's, as fixed there: `trace.raw` without its `Date:` header line, plus the input deck,
  the record, the result and the noise fingerprint (`impl/dupcheck.py`).
- **A mismatch on a machine means that machine runs nothing** until it is explained in writing.

**What this does not show.** The campaign's measure wrapper and its guard path are exercised only by their tests
(`test_campaign.py`), never by a simulation before the campaign. The campaign's own measure stages first run in
stage D.

## B. The round of a rehearsal run

The rehearsal's noise seeds are section 7's table, unchanged. For a noisy rehearsal job [new, a convention]:
- the ROUND passed to `family_net.py run` is family_net's `n`, that is noise seed − 10 × S:
  - F2 1 to 4;
  - X1 and F4 5;
  - X2 and F3 6;
- the run id keeps campaign_common's form, `S-MEMBER-rN`: `8303-X1-r1`, `8303-X2-r1`, `8306-F4-r1` and `8306-F3-r1`
  for the four single noisy runs.

## C. The limits of the rehearsal's network runs

**Fixed here, before any rehearsal run** [new]. Each network run of the rehearsal is judged against
`10 × ceil(2 × upper / 10)`:
- `upper` is section 4's upper F1 estimate times the member's slot factor:
  - without noise: 1 292 s;
  - noisy: 2 676 s;
- for an untrained run, `upper` is 180 s.

| Member | without noise | noisy | untrained |
|---|---|---|---|
| X1 | 960 s | 1 980 s | 360 s |
| X2 | 1 220 s | 2 520 s | 360 s |
| F4 | 1 530 s | 3 160 s | 360 s |
| F2 | 1 970 s | 4 070 s | 360 s |
| F3 | 1 890 s | 3 910 s | 360 s |

**The 0.75 rule** of section 7 is judged against these limits. A rehearsal run above 0.75 of its limit here, or one
that does not complete, means nothing is launched until an amendment.

**The hard timeouts** of the rehearsal jobs are `10 × ceil(3 × upper / 10)`, so that a slow run still ends and is
measured:
- X1 1 440 and 2 970 s;
- X2 1 830 and 3 780 s;
- F4 2 290 and 4 740 s;
- F2 2 950 and 6 110 s;
- F3 2 830 and 5 860 s;
- untrained 540 s.

A run cut there has not completed.

**Amendment 2**, after the rehearsal, sets the campaign's network limits from the measured costs, as section 4 says.

## Pending

**C1, the noise sensitivity values.** No code yet computes `b`, `w` and `d` from the 8 noisy F2 runs by campaign 3's
definition. That code is:
- written, reviewed and frozen;
- rerun by M3 as amendment 1 sets out;
- run before any noisy campaign stage.

Its values are fixed in amendment 2.

## Not checked

- Whether each machine's reproduction of `8303-cal-on-unary` is identical: that is what A checks.
- The estimates behind the limits of C: no network run at `1e-5` has been measured yet.
