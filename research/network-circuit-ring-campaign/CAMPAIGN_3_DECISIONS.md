# Campaign 3: decisions of the owner

Fixed by the owner on 2026-11-15, after the measure stage of campaign 2 and **before any network result of
campaign 2**, and pushed alone on the branch `research/network-circuit-ring-lessons`, before the attempt marker of
the network runs of campaign 2. They rest on
[`LESSONS_FROM_THE_MEASURES.md`](LESSONS_FROM_THE_MEASURES.md) (commit `453966e`), which uses the measures only.
Nothing here changes campaign 2, which runs its network stage as preregistered and is analyzed and reported as it
is. **Campaign 3 starts only after campaign 2 has ended and been analyzed and reported.**

1. **Scan time limit: 640 s**, from the spread measured in campaign 2: the longest scan seen (20 pulses, 13.18 ms)
   at the slowest rate seen (24.3 s per pulse, 37.3 s per ms), with a margin of 1.3.
2. **Robust scan.** After the first FIRE, two more isolated reads at one and at two further doses, so that every
   port has at least three fired states and the slope of its latency is always defined (the case of 7305 in
   campaign 2). A change to `../network-circuit/phase1/cellscan.py`, rehearsed on the nominal cell before the
   implementation is frozen.
3. **Contradictory states** (the case of 7206 in campaign 1: a state that fired is not stronger than a state that
   stayed silent). The isolated reads at the two disputed states are repeated and the majority is taken, by a rule
   written in the `PREDICTION.md` of campaign 3.
4. **Size: 12 new instances**, each with one run without noise and one shortened noisy run (three laps after the
   predicted freeze); one control run; within 4 h of expected machine time, counted as in campaign 2. New seeds,
   none reused: none of 7101 to 7103, 7201 to 7206, 7301 to 7306.
5. **Everything else as in campaign 2**: N = 3; the same ring and calendars; the same two budgets; the noise
   constants fixed at 0.090, 0.064 and 0.009 mV for the noisy budget only; the claim under noise per port, N-own
   and N-word, with the same exclusions reported; the same rule for the control instance; the launch kit
   unchanged, one launch per machine per stage.
