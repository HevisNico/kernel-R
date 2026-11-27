# Rehearsal 1: the replay of the third symbol (TASK 3)

Run on 2026-11-27 by the stage-D worker, after the criteria were pushed (REPLAY_CRITERIA_2026-11-27.md, ca239157, and its
addendum, 13af8381). This is a reconstruction made after the fact. It is exploratory and changes no verdict. It
touched nothing on the freeze path, and ran in a separate folder.

## How it was run

- **Code.** The stage-D code of the freeze 5d02acce, from a clean clone: `stage_d.StageDNetwork`, the instance's seed,
  and overlay `config_inverter_c5.json`. ngspice and the PDK at 1232782c, as pinned. Python 3.13.18. See replay.py.
- **The deck.** The deck the replay builds is byte-identical to each instance's published `D/input.spice`
  (`deck_identical: true` in every run): 28b8df45… for XOR3_27735 and 28b8df45… for XOR3_88529.
- **The history.** Stage D's training loop runs lesson slots 0, 1 and 2 only. Slots 0 and 1, and the preset before
  them, are stage D's exactly.
- **What changes.** In slot 2 (the third read), only the two input dates of the two cells under study change,
  measured from the slot's T. The two other cells of the network deck keep stage D's 2.4/2.4 µs. All the dates lie on
  the noise grid (asserted).
- **The window.** The run continues to the end of slot 2's watch window, T to T+240 µs, whether the cell fired or not.
- **Saved vectors.** Besides stage D's own vectors, each of the two cells saves x1 and x2 vs and vrefsn, and vq and
  vrefmn. The full output is in runs/*/replay.json; the raws are listed by sha256 in runs/RAW_SHA256SUMS.txt.
- **The comparators.** In the deck's comp subcircuit the output is high when inp > inn, with xm1's gate as inn and
  xm2's gate as inp.
  - Each port comparator (xcmps of x1 and x2) has inn = vrefsn and inp = vs. Its margin is **vs − vrefsn**.
  - The common comparator (xcmpm) has inn = vq and inp = vrefmn. Its margin is **vrefmn − vq**.
  - For each margin the table gives its signed maximum over [T, T+240 µs], in mV, with its time from T.
- **The sampling step.** ngspice's variable step: a median of 0.004 to 0.005 ns, and a maximum of 200 ns (the run's
  maximum step).

## Validity, case 1, checked first for each cell

| Instance | Cell | Replay | Stage D record | Latch difference | u difference |
|---|---|---|---|---|---|
| XOR3_27735 | c1_0 | F, latch T+22.005 µs | F, T+22.005 µs | 0.000 µs | 0.000 µV |
| XOR3_27735 | c1_1 | F, latch T+19.645 µs | F, T+19.645 µs | 0.000 µs | 0.000 µV |
| XOR3_88529 | c1_1 | F, latch T+21.762 µs | F, T+21.762 µs | 0.000 µs | 0.000 µV |
| XOR3_88529 | c1_0 | F, latch T+18.383 µs | F, T+18.383 µs | 0.000 µs | 0.000 µV |

All four cells pass: F, the latch within 0.1 µs, and u within 1 µV. The replay reproduces stage D's third read.

## Results per cell and case

Arrivals and latch times are in µs from slot 2's T. "Common max" is the maximum of vrefmn − vq. The port margins
peak at the arrival of each input pulse, at +603 mV, in every case, so they are listed only in REPLAY_TABLE.txt.

| Instance | Cell | Role | Case | Arrivals | Symbol | Latch | u before the read (mV) | Common max (mV) @ µs |
|---|---|---|---|---|---|---|---|---|
| XOR3_27735 | c1_0 | refuted | 1 | 2.4 / 2.4 | F | 22.005 | −15.2227 / −15.4168 | +392.181 @ 22.01 |
| XOR3_27735 | c1_0 | refuted | 2 | 12.0 / 12.0 | F | 31.606 | −15.2227 / −15.4168 | +392.180 @ 31.62 |
| XOR3_27735 | c1_0 | refuted | 3 | 11.2 / 12.8 | **s** | — | −15.2227 / −15.4168 | **−6.663 @ 31.20** |
| XOR3_27735 | c1_1 | witness | 1 | 2.4 / 2.4 | F | 19.645 | −13.673 / −24.138 | +391.687 @ 19.65 |
| XOR3_27735 | c1_1 | witness | 2 | 12.0 / 12.0 | F | 29.245 | −13.673 / −24.138 | +391.687 @ 29.25 |
| XOR3_27735 | c1_1 | witness | 3 | 12.8 / 11.2 | F | 29.340 | −13.673 / −24.138 | +391.686 @ 29.35 |
| XOR3_88529 | c1_1 | refuted | 1 | 2.4 / 2.4 | F | 21.762 | −14.3883 / −16.6999 | +405.992 @ 21.77 |
| XOR3_88529 | c1_1 | refuted | 2 | 12.0 / 12.0 | F | 31.363 | −14.3883 / −16.6999 | +405.991 @ 31.37 |
| XOR3_88529 | c1_1 | refuted | 3 | 12.8 / 11.2 | **s** | — | −14.3883 / −16.6999 | **+7.937 @ 31.20** |
| XOR3_88529 | c1_0 | witness | 1 | 2.4 / 2.4 | F | 18.383 | −14.8891 / −13.3062 | +392.118 @ 18.39 |
| XOR3_88529 | c1_0 | witness | 2 | 12.0 / 12.0 | F | 27.984 | −14.8891 / −13.3062 | +392.118 @ 27.99 |
| XOR3_88529 | c1_0 | witness | 3 | 11.2 / 12.8 | F | 28.051 | −14.8891 / −13.3062 | +392.116 @ 28.06 |

Observed as such: in XOR3_88529 c1_1, case 3, the common comparator's differential rises to +7.937 mV at T+31.20 µs,
and the latch does not rise. In the fired cases, the differential jumps to about +390 to +406 mV at the latch.
Without a further measurement this report reads nothing into that.

## Reading against the criteria table, one cell at a time (addendum)

- **XOR3_27735, refuted cell c1_0.**
  - Case 1 is valid. Case 2 gives F and case 3 gives s.
  - Its witness c1_1 gives F in all three cases.
  - This is the first row of the table. In this isolated cell, the separation of the two inputs alone, at a constant
    mean delay, suffices to reproduce the divergence.
- **XOR3_88529, refuted cell c1_1.**
  - Case 1 is valid. Case 2 gives F and case 3 gives s.
  - Its witness c1_0 gives F in all three cases.
  - This is the first row of the table, for this cell, read on its own.
- **No range claim.** These are three tested arrival times per cell. No bound between them was established, so each
  result is stated as **stable at the tested times**, and nothing is claimed over a continuous range of arrival times.

## What this replay cannot establish

It is the criteria's own section, which this replay does not change.
- It explains two past cases. It does not give a rule that predicts a new network.
- Under the preregistration, `ssFF` against `sssFF` stays a full refutation.

## Files

- replay.py: the replay.
- analyze_replay.py: the reading.
- REPLAY_TABLE.json and REPLAY_TABLE.txt: every number above, plus the port margins and the sampling steps.
- fig_replay_XOR3_27735_c1_0.png and fig_replay_XOR3_88529_c1_1.png: cases 1–3 overlaid for each refuted cell. They
  show v(p) and the three comparator differentials over T to T+60 µs.
- runs/<instance>_case<k>/replay.json: the slots of each run and stage D's slots for comparison.
- runs/RAW_SHA256SUMS.txt: the sha256 of the six raws, which are not published.
