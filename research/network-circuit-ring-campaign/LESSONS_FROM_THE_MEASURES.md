# Campaign 2: what the measure stage showed

Written after the measures of campaign 2 and before its network stage, and pushed alone on the branch
`research/network-circuit-ring-lessons`, before the attempt marker of the network runs. **It rests only on the
measures** (`evidence/measures-a`, `evidence/measures-b`, `MEASURES.json`, `PREDICTED.json` at `7aa9411`) and on
the cost model of phase 0. No network run had started when it was written; nothing in it uses a network result.
It changes no rule of `PREDICTION.md` and no frozen file: campaign 2 runs its network stage as preregistered. It
is input for a corrected campaign 3, whose rules are the owner's to set. No diagnostic simulation of 7302 or 7305
is made before campaign 2 has ended.

## 1. The scan of 7302, port `a1`, reached its limit

`a-7302-scan-a1` was stopped at its limit of 410 s (`time-limit-never-rerun`), so 7302 is not measured. The limit
came from the rehearsal of phase 0: one scan on the nominal cell, 15 pulses, 10.54 ms simulated, 274 to 284 s
wall with four runs at a time on machine `a`, times 1.3.

The 23 scans that ended (four at a time on each machine):

| | Machine `a` (11 scans) | Machine `b` (12 scans) | Rehearsal, nominal |
|---|---|---|---|
| wall, s | 278 to 389, mean 349 | 233 to 347, mean 280 | 273 to 284 |
| pulses | 13 to 18 | 13 to 20 | 15 |
| simulated, ms | 8.34 to 11.86 | 8.78 to 13.18 | 10.54 |
| s per pulse | 21.2 to 24.3 | 17.3 to 19.8 | 18.3 to 18.9 |
| s per simulated ms | 28.3 to 37.3 | 24.1 to 29.6 | 26 to 27 |
| fit | 52 s + 27.9 s/ms | 44 s + 22.8 s/ms | |

Trains without noise: 514 to 537 s on `a`, 449 to 477 s on `b` (limit 730; rehearsal 451 s).

What this says:

- **The length of a scan is not fixed.** It is set by the port: its training reads, the coarse descent and the
  bisection (`cellscan.py`: up to 30 training reads, 40 descent steps, 16 bisection steps, a simulated span capped
  at 60 ms). On the instances it ranged from 13 to 20 pulses and 8.3 to 13.2 ms; the nominal cell sat in the
  middle. A limit taken from one nominal scan does not cover the instances.
- **The two machines differed by about 20 %.** Machine `a` took 21 to 24 s per pulse, against 17 to 20 on `b` and
  18 to 19 on the same container in the rehearsal. Same processor model, four processors each. The 1.3 margin was
  spent by the machine alone on the longest scans of `a` (389 s).
- `a-7302-scan-a1` had run 410 s: at the rate of `a` that is at least 17 to 19 pulses, or about 11 to 14 ms. Its
  session log (133 975 bytes) is longer than that of every scan that ended on `a` (at most 132 220 bytes). How long
  it would have run is not known.

**Data for a limit set from the real spread.** The longest scan seen has 20 pulses and 13.18 ms; the slowest rate
seen is 24.3 s per pulse and 37.3 s per ms. Covered on the slowest machine: 20 x 24.3 = 486 s, 13.18 x 37.3 =
492 s; with a margin of 1.3, about 640 s. At that limit the measures of six instances cost 3 245 s per machine by
the kit budget instead of 2 555 s (1 380 s more for the two machines); the expected machine time does not change.
A limit tied to the scan itself (its pulse count) would need a change of `cellscan.py` and is not proposed here.

## 2. The scan of 7305, port `a1`: no slope at the trained state

7305 is not measured: `constants.port` fails on `a1` at `assert len(points) >= 2` (`secant`, line 45). Its
isolated reads:

- silent at -4.721, -6.077, -7.433, -8.789 mV, then FIRE at -10.145 mV with a latency of 0.999 unit;
- the reference, the read 16 units after a FIRE and one more read: FIRE, all at -10.145 mV (latency 0.998 to
  0.999);
- the bisection back down: silent at -9.898, -10.021, -10.083, -10.114, -10.129 mV.

**The threshold exists** (bracket -10.145 to -10.129 mV, half bracket 0.008 mV). What is missing is a second
stored state that fires: every FIRE is at one state, just past the threshold, with a latency at the edge of the
read window (1 unit). The slope of latency against the stored voltage, which turns every help into mV, cannot be
computed. It is a different failure from 7206 of campaign 1, where a state that fired was not stronger than a
state that stayed silent (`assert lo < hi`); both are a scan whose isolated reads do not have the structure that
`constants.port` needs, and both leave an instance not measured.

The margin is thin elsewhere too: the number of distinct stored states that fired among the isolated reads of
`a1` is 2 on 7301 and on 7303, against 3 to 9 on the other ports of the measured instances.

**Robust rules, for the owner to choose before campaign 3:**

- **More fired states by construction.** After the first FIRE, the scan reads the port at one and at two further
  doses, so that every port has at least three distinct fired states. About two pulses per scan (40 to 50 s at
  the rates above). A change of `cellscan.py`, rehearsed before freezing.
- **A declared fallback for the slope.** When fewer than two fired states exist, the slope is a value fixed
  beforehand (the nominal cell's, or the smallest seen on the measured ports), stated as a departure that widens
  the budget. No new simulation.
- **For the 7206 case** (`lo >= hi`): repeat the isolated reads at the two disputed states and take the threshold
  from the majority, or count such a port as having no room. Either is decided before the runs.
- Whatever the rule, count the instances that it cannot measure in the planned size (section 3).

## 3. Eligibility: 2 of 4 measured instances

| Instance | Measured | Needs a1, b1, c1, a2 | Eligible | Least room under the noise-free budget |
|---|---|---|---|---|
| 7301 | yes | 5, 4, 4, 5 | no | `a1` -0.013 mV |
| 7302 | no: scan reached its limit | | | |
| 7303 | yes | 4, 4, 3, 4 | no | `c1` -0.043 mV |
| 7304 | yes | 2, 4, 5, 4 | yes | `a2` +0.003 mV |
| 7305 | no: no slope on `a1` | | | |
| 7306 | yes | 6, 4, 4, 4 | yes | `c1` +0.003 mV |

14 of the 16 measured ports have own room under the noise-free budget (campaign 1: 19 of 20). With four ports
per instance, one port without room is enough to lose the instance, and the two eligible instances pass by 3 uV
each. Per drawn instance: campaign 2 gives 2 eligible of 6; campaign 1 gave 4 of 6; together **6 eligible of 12
drawn, 0.5 per drawn instance** (9 of 12 measured, 6 of 9 measured eligible).

**How many instances fit in 4 h**, counted as the owner counts it (expected machine time, two machines, two
stages; each stage on each machine is the sum of its expected times divided by four plus three quarters of its
largest). Measures from campaign 2: a scan 313 s, a train 495 s on average. Network runs from the cost model of
phase 0 (needs of 4.3 on average): 1 263 s without noise, 1 151 s for the control, 1 206 s for a shortened noisy
run. Per drawn instance with three quarters measured:

| Plan per measured instance | Per drawn instance | Instances in 4 h | Expected eligible at 0.5 per drawn (at 1/3) |
|---|---|---|---|
| quiet + 3 shortened noisy (as campaign 2) | about 1 350 s | 8 | 4.0 (2.7) |
| quiet + 1 shortened noisy | about 900 s | 12 | 6.0 (4.0) |
| quiet only | about 670 s | 17 | 8.5 (5.7) |

with about 2 900 s for the control and the tails of the four stage-machines. To expect at least 4 eligible
instances at the pooled rate needs 8 drawn instances; at the rate of campaign 2, 12. With three noisy runs per
instance, 4 h holds about 8: just enough at the pooled rate, not at the rate of campaign 2. Either fewer noisy
runs, or more than 4 h, or a corrected scan that measures more of the instances drawn.

## 4. The size of N-word: 6 port-runs

From `PREDICTED.json`, under the noisy budget at K = 3 with the fixed constants:

| Instance | Own room | Room up to it |
|---|---|---|
| 7301 | `c1`, `a2` | none |
| 7303 | none | none |
| 7304 | `a1`, `b1` | `a1`, `b1` |
| 7306 | `b1`, `a2` | none |

So the plan holds **18 port-runs for N-own** (6 ports, three noisy runs each) and **6 for N-word** (`a1` and
`b1` of 7304), against about 30 and 14 expected in phase 0. Own room at K = 3 holds on 6 of 16 measured ports
(37.5 %; phase 0 assumed 50 % from campaign 1).

N-word is small by construction: room up to port `k` needs every port before it, and the launch port `a1` has own
room at K = 3 on one instance of four. Every N-word port-run of campaign 2 comes from one instance; its three runs
share the mismatch and differ by the noise only. With no failure, 6 port-runs bound the failure rate per
port-run below 39 % at 95 % (1 - 0.05^(1/6)); 18 port-runs below 15 %; about 30 are needed for 10 %.

For campaign 3, the size of N-word grows with the number of instances whose `a1` has room at K = 3 (1 in 4 here),
not with the number of runs per instance: more instances with fewer noisy runs each add more to it than more runs
on the same instances.
