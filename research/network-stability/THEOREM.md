# Stability of learning in dated guarded networks

[The Lean theorem](DatedNetwork.lean) is `NetworkStability.PhaseAdmission.dated_network_memory`. Fix the reserve bound $Q$, normalized write dose $d$, birth bound $B$, rail $U$, and optional rank constants $W$ and $\eta_0>0$ independently of the number of cells $N$.

Each cell stores two port counters and one recovery counter. An occurrence has a date and an input address. Its date and input select the admission phase and therefore the bias, learning and MARK rules. The guarded read uses the port and recovery counters and an additive read error. FIRE can issue dated child occurrences and write recovery. A silent occurrence can write its port and recovery, depending on its phase. An earliest-date scheduler selects a least-dated pending occurrence. The cell wiring can contain cycles.

## Hypotheses

Each occurrence carries a nonnegative reserve for each coordinate. On either branch its reserve pays for its write footprint and all emitted child reserves. The seed reserve is at most $Q$ per coordinate. Birth memories are at most $B$, with $B+dQ<U$. Children have dates at least as late as their parent. A certified read has an error interval containing zero and lying entirely on one side of the FIRE threshold at the nominal score.

At every reachable clean dated configuration, two distinct occurrences eligible at the same minimum date either target different cells or satisfy the MARK interleaving condition. For such a pair, the clean read of each occurrence must survive the other's write footprint. This condition covers the signed effect of recovery writes on both ports of the cell. Dates force the order of occurrences with different admission dates. Causal routing keeps the second occurrence eligible after the first is processed.

## Conclusions

- Every coordinate receives at most $Q$ writes, each cell at most $3Q$, and the network at most $3QN$. Each stored value stays between its birth value and $B+dQ<U$. A separate safety result, `dated_noisy_safe`, allows arbitrary read errors.
- Every certified trace replays at zero error with the same decisions, routes and counters. Counters eventually freeze even when FIRE traffic continues. The bound controls the number of writes. The step of the last write may depend on the execution.
- The tied moves form a local diamond up to pending queue permutation. Any two certified runs that exhaust their queues have equal terminal counters. The horizon corollary `dated_horizon_unique` gives the same comparison for prefixes that have cleared a common date horizon. It retains the future queue in each original execution and checks the tie hypothesis on the clipped calendar.
- For perpetual traffic, earliest-date schedules that clear each date meet dated continuation fairness and have a common limiting memory. A finite budget for service at or below each date suffices for clearance. Without clearance, an endlessly reissued early probe can starve a later writer. See [DatedFairness.lean](DatedFairness.lean).
- If an optional probe rank pays at least $\eta_0$ per step after reserving the weights of all children, and its seed mass is at most $WN$, certified traces have length at most $WN$. Any trace of that length has an empty queue. The positive rank excludes cycles in the declared probe types, even where the physical wiring has feedback.

## Global diamond corollary

A global MARK diamond implies the tie hypothesis by `TieAdmissible.of_global`, so every dated conclusion above also holds under the global assumption. The original undated statement `MarkFeedback.network_memory` remains in [MarkFeedback.lean](MarkFeedback.lean). The [date-24 control](DatedTrainingControl.lean) certifies the dated training prefix and refutes the global premise for the same protocol.

## Reciprocal witness

[ReciprocalReplay.lean](ReciprocalReplay.lean) certifies the sixteen pre-birth transactions of A through time 128. The certificate matches the actual admission and FIRE words, preserves the later sources in the queue, and identifies the two gain coordinates and recovery with the native memory at the cut. The same file gives the assembly proof through 459.9 conditional on an aligned full transaction table and its checked coordinate counts. The post-birth row table and its fold of gain and recovery writes are still required for the unconditional full-history result.
