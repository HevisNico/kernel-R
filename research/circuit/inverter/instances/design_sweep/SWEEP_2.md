# Widening the inverter's margins: design sweep 2 (development seeds only)

**Development work, not preregistered.** Each candidate is a fresh simulation of the 6 stress seeds (9928, 9944,
9963, 9903, 9901, 9902; tt_mm) and the nominal cell (tt). They were gated with the package at bb4b8cc. One lever was
changed at a time, then combinations. The candidates' configs are `C*.json`; every number is in
`SWEEP_2_OUTPUT.txt`, produced by `analyze.py`. `config.json` is **not** changed. The design change waits for the
owner's go.

## Summary (6 stress seeds)

| Candidate | Change from J0 = 4.0 | Eligible | Room | min SM3 | min FM3 | max X absent (≤ 1.35) | min headroom | Added W·L | Nominal emission |
|---|---|---|---|---|---|---|---|---|---|
| C0 | none | 5/6 | 4/6 | −0.0000 | 0.131 | 1.364 | 0.109 V | 0 | 0.5145 |
| C1 | J0 4.4 | 5/6 | 5/6 | 0.054 | 0.134 | 1.364 | 0.072 V | 0 | 0.5145 |
| C2 | τ 0.30 | 5/6 | 5/6 | 0.080 | 0.119 | 1.364 | 0.047 V | 0 | 0.5145 |
| C3 | level 0.95 | 5/6 | 5/6 | 0.053 | 0.085 | 1.364 | 0.109 V | 0 | 0.5270 |
| C4 | help mirror w4 l8 | 6/6 | 6/6 | 0.066 | 0.197 | 1.296 | 0.109 V | +48 µm² | 0.5135 |
| **C5** | **help mirror w2 l16** | **6/6** | **6/6** | **0.112** | **0.244** | **1.258** | **0.109 V** | **+48 µm²** | **0.5148** |
| C6 | C5 + J0 4.4 | 6/6 | 6/6 | 0.169 | 0.252 | 1.258 | 0.072 V | +48 µm² | 0.5148 |
| C7 | help mirror w2 l32 | 6/6 | 6/6 | 0.110 | 0.251 | 1.255 | 0.109 V | +112 µm² | 0.5104 |
| C8 | help mirror w4 l16 | 6/6 | 6/6 | 0.095 | 0.228 | 1.272 | 0.109 V | +112 µm² | 0.5115 |

- **Charge (C1, C2) and the threshold (C3)** raise the silence margin, but they do not touch the cause of the tail:
  - 9944 still fails StateBound (1.364), because X absent is the help error, not Q;
  - C2 costs headroom (47 mV);
  - C3 costs firing margin (min 0.085) and 0.0125 tu (0.25 µs) of latency.
- **The help mirror's matching (C4, C5) removes the cause.**
  - ηH falls from 0.20 to 0.067 at most (C5), and 9944 passes StateBound with X 1.258.
  - C5 (longer channel, same width) is better than C4 (same W/L, larger area): its higher overdrive lowers the
    current's sensitivity to the threshold mismatch.
- **Larger still (C7, C8) does not help.** The remaining help error (about 0.04-0.05, also at nominal) is
  systematic, not mismatch. It is consistent with the switch's transient on the larger gate capacitance [I]. C7's
  nominal silence margin is lower than C5's.
- **The leak asymmetry was not swept.** Its whole weight in the margins is α·L ≈ 0.004-0.006, against the
  0.11 gained here.

## Costs

- **C5:**
  - area +48 µm² (two NMOS from 2×4 to 2×16 µm);
  - no added power: the same 0.5625 µA help reference, and the same 2.5 pC (4.5 pJ) per slot when the input is present;
  - no latency change: nominal emission 0.5148 tu against 0.5145; comparator delay 0.00101 tu.
- **C6 adds** +0.25 pC (+0.45 pJ) per slot and 10 % more inhibitory current. It costs 37 mV of headroom (72 mV left).

## Recommendation

**C5: help mirror w = 2, l = 16 (µm), J0 kept at 4.0.**
- On the stress set, every instance has room.
- Silence margin with noise: min 0.112 (it was −0.00003).
- Firing margin with noise: min 0.244.
- The state bound has 0.09 to spare.
- Headroom is unchanged, at 0.109 V or more.
- C6 would add 0.057 of silence margin at the cost of headroom. Keep it as a fallback if the new lot falls short of
  its target.
