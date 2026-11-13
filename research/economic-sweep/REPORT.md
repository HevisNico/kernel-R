# Exploratory economic sweep

**Not v5/v6 confirmatory evidence.** The finite grid and two scenarios were written
before this calculation. No v5 scenario or seed was used.

H=150, dose220, service100, horizon264, initial=min(440,capacity).
The seven capacities are 300,440,660,1000,1500,3000,6600. Probe/write price
ratios are .01,.1,1,10. The policies are price-blind; price reweights a fixed
physical trace and does not cause a policy revision.

| Scenario | Capacity | Different optimistic/fixed periods | Optimistic probes/writes | Fixed probes/writes |
|---|---:|---:|---:|---:|
| jump | 300 | 0 | 265/264 | 265/264 |
| jump | 440 | 0 | 265/114 | 265/114 |
| jump | 660 | 0 | 246/90 | 246/90 |
| jump | 1000 | 0 | 246/90 | 246/90 |
| jump | 1500 | 0 | 246/90 | 246/90 |
| jump | 3000 | 0 | 246/90 | 246/90 |
| jump | 6600 | 0 | 246/90 | 246/90 |
| high | 300 | 0 | 265/264 | 265/264 |
| high | 440 | 0 | 265/176 | 265/176 |
| high | 660 | 8 | 265/168 | 265/168 |
| high | 1000 | 8 | 265/168 | 265/168 |
| high | 1500 | 8 | 265/168 | 265/168 |
| high | 3000 | 8 | 265/168 | 265/168 |
| high | 6600 | 8 | 265/168 | 265/168 |

Across 56 scenario/capacity/price cells, action-changing optimistic benefits: **0**; higher-cost optimistic cells: **0**.

Complete cells, oracle gaps and policy terminal inventories are retained in RESULTS.json
and cells.csv; no unsuccessful or inconvenient cell is removed.

## Economic opportunity not captured by this optimistic law

For jump, capacity6600 (capacity/H=44) and probe/write price10, the fixed
and optimistic policies cost255000 integer units, versus oracle105000:
a 142.86% oracle gap. Early refill costs119400, a 13.71% gap. These costs
use write price100 and probe price1000. Thus the present optimistic law
finds no economic benefit, but substantial policy-optimization room exists.
It would be incorrect to infer that all possible learning is useless.

Early refill ends that case at reserve3520 versus440 for fixed/optimistic;
unused terminal stock has no value in this objective. Future comparisons
must keep that endpoint convention explicit and must not credit this
fixed heuristic improvement to learning.

## Interpretation

The jump scenario tests low leakage followed by a refutation. The high scenario
starts at constant140 so the variation candidate need not be refuted: its extra
12-unit planning margin can alter waits/writes. A benefit there is an economic
effect of a fixed margin/threshold, not evidence that a learned rule improved.
No policy here learns a new law, and no universal conclusion follows from this grid.

The oracle knows every future loss and sensor error and may deliberately trade
saturation for probes. It explores only one-write / hard-ready-at-next-probe actions,
with maximum wait40 and no terminal inventory value. It is neither a deployable
controller nor a global physical optimum. Reported policy gaps are relative to
that comparator and can reflect different final inventories.

Safety checks retain all unsafe pre/post periods and refusals. This sweep contains
no new Lean proof or transistor evidence. It is repeatable exploratory computation.
