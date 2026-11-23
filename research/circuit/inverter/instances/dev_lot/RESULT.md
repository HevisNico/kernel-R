# Development lot of inverter instances: result

**Development work, not preregistered.** Run under the rule of 4bcf98a (70 %), with the code at cd8823e.
Run started 2026-11-23T06:54:42Z and ended 07:09:33Z. Every verdict is conditional on the open premises listed in
`SUMMARY.json`: one constant leak [I], the ℝ bridge, and the latch.

## Counts

| | k / n | Wilson 95 % |
|---|---|---|
| finished | 60 / 60 | |
| eligible (K0) | **60 / 60** | [0.940, 1.000] |
| with room (K3) | **59 / 60** | [0.911, 0.997] |

The rule did not stop the lot (20 of the first 20 eligible). The final verdict is **"continue"**: 60 of 60, against
a threshold of 42 of 60. The kernel agreed with the mirror on all 60, and the sample was the same across the 5 runs
on all 60.

## Distributions (min, median, max over 60)

| Quantity | min | median | max |
|---|---|---|---|
| silence margin, K3 | -0.0000 | 0.1386 | 0.2006 |
| firing margin, K3 | 0.1307 | 0.2646 | 0.3224 |
| δ (units; 1 unit = 500 mV) | 0.0002 | 0.0080 | 0.0350 (17.5 mV) |
| α | 0.0027 | 0.0039 | 0.0048 |
| emission (tu) | 0.4865 | 0.5112 | 0.5354 |
| ηH | 0.0175 | 0.0586 | 0.1970 |
| Q | 0.8996 | 0.9522 | 1.0031 |
| machine seconds per instance | 52.8 | 57.2 | 59.8 |

## The one failure, and the tail

- **9928, room fails.** SilenceAfter at K3 has margin -0.00003; at K0 the margin is +0.0058. The cause is a large
  help error (ηH 0.176, from help-mirror mismatch) together with the largest δ of the lot (0.035, 17.5 mV).
- **9944 passes with 0.0032** (ηH 0.197).
- The next margins are 0.026, 0.045 and 0.054.
- The silence margin's tail is set by the help mirror's mismatch (ηH up to 0.20). It is not set by the leak or Q.

## Cost

- 58.3 machine-minutes of job time in all (under the 90 ceiling).
- 14.7 minutes of wall time on one 4-core machine, 4 jobs at a time.
- Traces kept locally (267 MB), not committed. `RESULT_SHA256SUMS` lists every MEASURE.json, GATE json and Lean file.
