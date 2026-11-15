# Amendment 1 to the commitment of campaign 3

Pushed alone on the branch `research/network-circuit-ring-campaign-3-commitment`, after
[`COMMITMENT.md`](COMMITMENT.md) (commit `d758fdb`, SHA-256
`593b65ff5b7624d420fd17bd3881dc99d0a31637a050a3bf9aa0e8e2e5a3b8fe`), which it does not edit, and before the
attempt marker of the network runs of campaign 2. It replaces **only point 4 of the commitment, the budget**.
Everything else in the commitment is unchanged: twelve instances, seeds 7401 to 7412; the protocol of campaign 2
with its four corrections and nothing else; the reporting rule; campaign 3 the last campaign of this series for
this claim.

## 4. Budget (replaces point 4)

- **Expected machine time**, two machines, two stages, counted as in campaign 2: **about 269 minutes if all twelve
  instances are measured** (260 minutes, plus about 9 minutes for the two extra reads of the robust scan), and
  **229 minutes if nine are measured** (before the extra reads, which the scans of all twelve instances make:
  about 238 minutes with them).
- **The kit's worst case**, every run taking its whole limit, at five doses per port: **25 665 s, 7.1 h**: 5 750 s
  per machine for the measures, 7 280 s and 6 885 s for the network runs.
- **The owner accepts both figures**, above the 4 h first fixed.
- **Order**, as in campaign 2: on every machine the runs without noise and the control come first and the noisy
  runs last, so that an overrun can only cost noisy runs. A noisy run that reaches its limit is a missing run,
  never replaced.
