# Milestone 2 — routed FIRE can suppress an ERROR write

[GuardedFeedback.lean](GuardedFeedback.lean) is a three-probe abstraction on two cells with reciprocal, time-gated routing. Each separated slot begins at a ready cell. The probe score is $1 + k + f + e$, where $k$ is that cell's stored dose count, $f$ is 1 when a routed FIRE overlaps the probe and 0 otherwise, and $e$ is the read error. At score 2 or higher the cell fires and its memory is protected. Below 2 the pulse is silent and writes one fixed dose. The order and routing policy are fixed. The slots are A, B, then A again. The first two FIRE decisions drive the forward and return edges respectively. The forward gate is closed during the third slot.

| Read errors at A, B, A | Terminal writes at A, B |
| --- | --- |
| $0,0,0$ | $1,1$ |
| $1,0,0$ | $0,0$ |

Both error sequences satisfy the same per-read radius 1. The second run actually uses both routed edges. Lean checks that a routed FIRE can change an otherwise silent write into a protected firing decision, and that the terminal write vectors differ.

This counterexample covers a guard abstraction with explicit pulses, fixed doses and a FIRE/ERROR exclusion. Its integer score, reset between probes, additive routed contribution and finite calendar are model premises. The native hybrid proof would need to realize these premises with actual pulse timing, charge, guard crossings and ERROR exposure. In this counterexample the initial decision has exactly enough error to cross the threshold. The companion theorem, `episode_eq_of_margins`, proves equality with the clean terminal vector when each nominal slot has enough one-sided room. Earlier FIRE decisions then agree and pass the same routed input to the next slot. In this fixture, errors in $[-1,0]$ at each of the first two probes and in $[0,1]$ at the return probe preserve $(1,1)$.
