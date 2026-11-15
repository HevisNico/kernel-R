# Amendment 3 to PREDICTION.md of campaign 3: the time limit of the robust scan

Pushed alone, before the implementation of campaign 3 is frozen and before any attempt marker; no seed of campaign 3
has been simulated. It changes no frozen file and one rule of [`PREDICTION.md`](PREDICTION.md) (`6aa0f40`): the
time limit of a robust scan, **640 s becomes 860 s**. It rests only on the rehearsal of the robust scan on the
nominal cell ([`ROBUST_SCAN_REHEARSAL.json`](ROBUST_SCAN_REHEARSAL.json), commit `d2c3a2e`) and on the measures of
campaign 2. Everything else stays as committed: twelve instances, one launch per machine per stage.

## The rehearsal

Four robust scans of the nominal cell (model section `tt`, no mismatch, no seed: not an instance), four at a time
on machine `a`, then the same four with the round of repeats forced (rehearsal only):

| | Pulses | Simulated, ms | Wall, s |
|---|---|---|---|
| ordinary scan of the nominal cell (campaign 2) | 15 | 10.54 | 274 to 284 |
| robust scan | 19 | 14.06 | 400 to 420 |
| robust scan with one round of repeats | 23 | 17.58 to 18.46 | 498 to 516 |

The robust scan adds **4 pulses and 3.52 ms** (two doses, two reads, the return by the imposed leak); one round of
repeats adds **4 pulses and up to 4.40 ms**.

## The limit

- **Raw worst case: 787 s.** The longest scan of campaign 2 (`b-7306-scan-a1`: 20 pulses, 13.18 ms) plus both
  extras is 28 pulses and 21.10 ms; at the slowest rates seen in campaign 2 (24.3 s per pulse, 37.3 s per simulated
  ms) that is 680 s by the pulses and **787 s** by the simulated time.
- **The slow machine's fitted model for that scan, x 1.3: 833 s.** Machine `a` of campaign 2: wall = 52 s + 27.9 s
  per simulated ms, so 641 s for 21.10 ms, and 833 s with the margin of 1.3.
- **860 s is the largest limit the frozen launch kit accepts for one measures manifest of twelve instances.** Its
  bound per machine is the sum of (limit + 10 s) over the 24 scans and 6 trains divided by four, plus the largest
  (limit + 10 s): 7 200 s per machine at 860 s, **14 400 s for the two machines**, the most one manifest may hold.

**What 860 s does not cover: 1.3 x the raw worst case, 1 030 s**, that is, a scan as long as the longest seen, with
a round of repeats on contradictory states, at the slowest per-ms rate seen, plus the full margin of 1.3. Such a
scan would reach its limit and be a **missing run, never rerun**, and its instance would not be measured, as
`PREDICTION.md` says of every measure run that does not count.

## The new kit budget

| Stage | Per machine | Two machines |
|---|---|---|
| measures (scans 860 s, trains 730 s) | 7 200 s | 14 400 s |
| network runs, at five doses per port (unchanged) | 7 280 s and 6 885 s | 14 165 s |
| **in all** | | **28 565 s (7.9 h)** |

The kit's worst case rises from 25 665 s to 28 565 s. The expected machine time of amendment 1 of the commitment
does not change: the limit binds only a scan that runs long.
