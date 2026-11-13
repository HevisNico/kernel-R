# Milestone 7 — memory stabilization under perpetual traffic

[PerpetualFeedback.lean](PerpetualFeedback.lean) uses the actual FIFO transition of milestone 5. A local reserve assigns natural credits $r_i(p)$ to probe $p$ for each cell $i$. A FIRE transfers credit to its descendants, and a silence spends one credit at the receiving cell. The sum of the initial credits per cell is at most $Q$.

- **Safety at every step.** The reserve argument alone bounds writes by $Q$ per cell and $QN$ over the network. For fixed dose $d$, initial memory at most $B$ and $B+dQ<U$, memory stays strictly below rail $U$. The constants precede $N$.
- **Stabilization.** For any read-error sequence there is a finite cut after which all write counters and stored memories are constant. The total write count is a bounded natural number, hence attains a maximum on the run. The counters are individually nondecreasing, so attaining that maximum freezes every counter. The statement gives existence of a cut for each run. Arbitrarily many FIREs may precede a late write, so the write bound supplies no deadline.
- **Role of the milestone 5 rank.** If a positive scalar decrease certificate exists, each declared descendant has strictly smaller probe weight than its parent. Thus milestone 5 relies on an acyclic, strictly ranked graph of probe types, even for cyclic wiring on cells. The local reserve theorem has no strict scalar rank assumption.

[PerpetualExamples.lean](PerpetualExamples.lean) checks the milestone 5 self-loop and a ring of every positive size. The self-loop has a valid local reserve, always has a pending probe and preserves its birth memory while its log grows. The ring seeds one training probe and one traffic probe. Training writes at cell zero. Each subsequent FIRE forwards the traffic probe to the next cell, with wraparound, indefinitely. The ring retains one pending traffic probe and records one event per step. For every size, the count vector freezes after the first write and the memory stays below 4 with dose 1, initial memory 1, reserve bound 2 and errors in $[-1,1]$.

## Processing order can affect terminal memory

[ScheduleCounterexample.lean](ScheduleCounterexample.lean) uses the same guarded update with an order relation that selects an existing pending occurrence, preserves the order of the rest, and appends its FIRE routes. The same seed FIRE generates two probes on a second cell. Both orders below exhaust the queue at zero read error.

| Order after the seed FIRE | Decisions | Final memory of cell 1 |
| --- | --- | ---: |
| Warm, routed read | Silence, silence | 5 |
| Routed read, warm | Silence, FIRE | 3 |

The initial memory is 1 and a dose is 2. After one dose the warm probe fires, while the routed read still writes. The router satisfies the strict scalar certificate and the local reserves with $Q=W=2$ and $\eta=1$. Each schedule's own nominal trajectory has directional read margins valid for $[-1,0]$. These margins protect decisions along a fixed order. Additional hypotheses would be needed to compare orders. The witness uses two pending probes on the same cell, and the result concerns the discrete model.
