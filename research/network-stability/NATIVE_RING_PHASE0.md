# Phase 0 · A native ring with a return acknowledgement

This is a proposed refinement class and theorem. The existing two-cell refinement is proved. The construction and refinement for this class are still to be proved in Lean.

## Class and membership test

Use the nominal-threshold hybrid model `KernelR.Hybrid.Execution`. For each $N\ge2$, number the native cells $0,\ldots,N-1$. Use native ports 0 and 2 as the two guarded gain coordinates. Port 1 stays idle.

| Input | Native delivery | What its FIRE can send |
| --- | --- | --- |
| Launch | One external delivery to cell 0, port 0, at time 1 | Cell 1, port 0 |
| Relay | A delivery to cell $i$, port 0, for $1\le i<N-1$ | Cell $i+1$, port 0 |
| Last relay | A delivery to cell $N-1$, port 0 | Cell 0, port 2 |
| Return | A delivery to cell 0, port 2 | The launch contact is closed by this date |

Each physical edge issues one delivery at the actual FIRE time plus its own fixed rational delay $\delta_i\in[8,9]$. Use a single outgoing contact per cell. Cell 0's contact is open on $[1,2)$, so the native router, which sees the firing cell and time, needs no port tag from the FIRE. All other contacts can be ungated. The initial pending list consists exactly of the launch. There is at most one delivery in flight, and the physical graph contains a directed cycle.

Construct the initial snapshot directly from parameters. Every cell starts in READY with all auxiliary modes READY, inactive RAW, charge $1/10$, auxiliary charge $1/40$, recovery $9/50$, and energy 50. Use `KernelR.FutureControls.parameters 0` at each cell. Specify each initial gain as the logarithm of a rational amplitude. Require:

- Cell 0's launch port is strong. Each relay port is either weak, with amplitude in $[9/10,1]$, or strong, with amplitude in $[9/5,2]$.
- The return port is weak. Unused gains have amplitude 1.
- Check the delay and amplitude intervals by rational comparisons. Construct the prepared snapshot, nominal physical box, and initial rail headroom from these data. The checker takes no native execution, event log, or list of successful transactions.

The first weak relay stops the pulse and writes one gain dose there. If every relay is strong, the pulse traverses the whole ring and the return writes one gain dose on cell 0's port 2. This port records the AND of the relay classifications. With delays 8 and strong amplitudes $37/20$, the all-strong branch passes the proposed inequalities for every $N\ge2$. Replacing any one relay amplitude by 1 gives the stopping branch. This checks parameter feasibility. It does not construct a native execution.

### Separation and margins from the parameters

- A strong pulse entering at $t$ should FIRE in $(t+3/10,t+9/10)$. FAST lasts one time unit. At the prepared recovery rate, `preparedSlowDuration_bounds` bounds SLOW by $28/5$. These bounds put the READY return before $t+15/2$. RAW and auxiliary completion, and zero gain and recovery doses on this branch, must hold at the same cut $t+15/2$. The next admission is after $t+8$, even if it is to a different cell. The weak branch also settles by $t+15/2$. Thus same-cell separation follows from the stronger serialized protocol. The return is strictly after the root's reopening and after its contact closes.
- Use the native pulse comparison in the range of `ReadyCoordinates`. For a weak port, the sensor-cycle bound permits an upper effective amplitude $4/3$, including the possible gain change during RAW. The scalar upper bound is $7/50+(4/3)(16/25)=149/150$. For a strong port, the frozen-gain READY comparison at $9/10$ gives at least $1/10-1/100000+(9/5)(5001/10000)=1+17/100000$ if it has stayed READY that long. Both leave a strict physical charge margin of $1/10000$. The strong inequality supplies a deadline and the root theorem supplies the FIRE time. Neither bounds the charge away from threshold at the actual crossing.
- Compile the two classes to guarded READY biases $-2$ and $2$, respectively, with normalized dose $d=4$, recovery weight 0, learning enabled on silence, and MARK disabled. Every reachable admission targets an unused gain coordinate, including the return to cell 0. The clean score is the bias, and `HasRoom` holds on $[-1,1]$. This interval certifies additive **guarded score errors**. There is no proposed identification of a score unit with an arbitrary perturbation of the native ODE or its FIRE clock.
- Derive the calendar without native logs. The occurrence key identifies cell and port. The phase is READY. For strong first visits use the first root of `readyPulse` from charge $1/10$ and the prepared amplitude. Those cells were idle before delivery. Use its exact clock plus the fixed delay for the child. For dormant or hypothetical FIRE branches, use any explicit positive latency consistent with the same abstract successor graph. A return has no abstract child. Prove equality with native routing at every actual FIRE.

## Target theorem · sketch

For every $N\ge2$ and every checked parameter tuple above, compile the router, prepared snapshot, seed, and dated calendar. From that snapshot there exist a nominal native execution complete through $T_N=10(N+1)$ and a dated `TransactionReplay` of it from `MarkFeedback.initial N seed`. The last cut is before $T_N$ because at most $N$ edges each take less than $9+9/10$ from intake to intake, and the last transaction settles within $15/2$. The replay satisfies:

- The rows are the native admissions in order, with the calendar phase equal to the native mode at each admission. Each FIRE row has the exact native FIRE clock and exact emitted delivery. The native pending list and abstract pending multiset agree at each settled cut and are both empty at $T_N$.
- At every settled cut, each native coordinate equals its prepared value plus its unit dose times the corresponding guarded count. The units are $3/5$ for log-gains and $1/10$ for recovery. The guarded count on recovery and the native recovery dose are zero in this class. The unused native gain stays fixed. Memory stays strictly below its native rail at all intervening times as well.
- The generated calendar satisfies the premises of `PhaseAdmission.dated_network_memory`. All certified earliest-date executions with guarded read errors in $[-1,1]$ follow the same decisions, drain within $N+1$ transactions, and have the same terminal memory. The endpoint native acknowledgement is one full gain dose exactly in the all-strong branch. An earlier weak relay retains that dose instead.

The proof should construct the native execution to avoid a vacuous statement about complete runs. Then `Execution.observational_unique` gives the same native endpoint and FIRE observations for every complete execution at the same horizon and fixed parameters. An event-by-event replay for each alternative native execution would additionally require transport of its admission and settlement cuts.

### Uniform certificates

Use $Q=1$, $d=4$, $B=0$, normalized rail $U=5$, $W=2$, and $\eta_0=1$. The normalized base encodes increments above the prepared state. Check the physical rails separately. Weak gains after a dose remain below $\log 4$, strong gains are unchanged, and recovery stays at $9/50<11/10$.

The declared successor graph on occurrences advances from launch through the relay indices to return. Unused keys can be omitted from the input type. Rank an occurrence at stage $k\in\{0,\dots,N\}$ by $N+1-k$; seed mass is $N+1\le2N$. The rank decreases even on hypothetical FIRE branches, although the cell graph cycles. For a particular coordinate, credit an occurrence by 1 exactly if that coordinate is a gain on its remaining suffix, including the current occurrence. A silent write spends its own credit. A FIRE transfers the suffix credit without adding a write. Recovery credit is zero. This pays for both branches, as required by `MarkFeedback.Reserve.pays`. The single-token invariant makes `TieAdmissible` immediate and strictly positive delay gives `Causal`. The exact initial rank gives the $N+1$ bound. The dated network theorem supplies the general per-coordinate and total write bounds ($Q$ and $3QN$); the protocol itself writes exactly once. The bounded rank also gives date clearance. The horizon grows with $N$, while the delay window, transaction duration, margins, doses, and certificate constants do not.

## Reuse and new proof obligations

| Existing Lean result | What carries over and what remains |
| --- | --- |
| `quiet_source_arrival_exists` and `quiet_complete_exists` in [HybridQuietSourceArrival.lean](../../proof/lean/KernelR/HybridQuietSourceArrival.lean) and [HybridQuietFlowExistence.lean](../../proof/lean/KernelR/HybridQuietFlowExistence.lean) | Construct globally quiet waits, the exact next head intake, and the final complete cut. Establish their quiet-state premises by induction. |
| `weak_input_cycle_exists` in [HybridWeakInputCycleExistence.lean](../../proof/lean/KernelR/HybridWeakInputCycleExistence.lean) | Constructs a settled weak pulse for general $n$ and router, with one ERROR dose and no FIRE or MARK. Prove that the inactive cells retain their prepared coordinates along the segment. |
| `first_learned_fire_exists` in [HybridFirstLearnedFireExistence.lean](../../proof/lean/KernelR/HybridFirstLearnedFireExistence.lean) | Constructs the actual FIRE and appends the real route for general $n$. Also supplies the scalar first crossing and transversality. Extend the subsequent FAST and SLOW construction to a selected cell in an $N$-cell product with quiet spectators and one future delivery. The current constructors `FirstLearnedFire.learned_fast_end_exists` and `prepared_slow_return_exists` are one-cell results. Transport of a one-cell trace must preserve the actual router, the pending list, and the physical ledger, or the general-`n` return must be constructed directly. This is the main new existence obligation. |
| `Execution.learned_mid_pulse_of_valid`, `prepared_transactions`, `prepared_wire_transactions`, and `predicted_phase_after_fire` in [HybridMidGainInput.lean](../../proof/lean/KernelR/HybridMidGainInput.lean), [NativeTransactions.lean](NativeTransactions.lean), [NativeWireTransactions.lean](NativeWireTransactions.lean), and [NativeTiming.lean](NativeTiming.lean) | Check the settled response and phase on a supplied physical span. The train lemmas take the actual calendar as a premise. In this class the calendar, lack of intervening same-cell input, and time available to finish must come from the one-token induction. |
| `Execution.token_balance`, `native_queue_replay`, `TransactionReplay.append`, `dated_network_memory`, and `Execution.observational_unique` in [HybridInputBalance.lean](../../proof/lean/KernelR/HybridInputBalance.lean), [NativeRefinement.lean](NativeRefinement.lean), [DatedReplay.lean](DatedReplay.lean), [DatedNetwork.lean](DatedNetwork.lean), and [HybridUniversalExecution.lean](../../proof/lean/KernelR/HybridUniversalExecution.lean) | Reuse native queue conservation, append the per-transaction certificates, obtain guarded consequences, and compare native observations. The bridge must still prove that no other flow writes or emits before settlement, compile the finite reserve and rank, and identify the native and guarded coordinates. |
| `nominal_reciprocal_refinement` in [ReciprocalPostBirth.lean](ReciprocalPostBirth.lean) | The two-cell proof supplies a comparison for the conclusion. Its fixed 77-row table, staged birth, and witness-specific dose counts are not premises of the proposed class. |

First implementation milestone: prove the generic settled strong step with one outgoing contact and arbitrary quiet spectators. Compose it with the already general weak step and prove the two branches of the ring. SLOW admissions, positive MARK writes, concurrent deliveries, staggered birth, and native error or delay jitter are outside this first class.

## Counterexample to dropping the minimum delay

Take $N=2$, nominal prepared parameters, strong amplitudes $37/20$, and a weak return amplitude 1. Replace both edge delays by $1/20$, leaving the router and other parameters as above. Write $f$ for the launch FIRE clock. A certified run of the proposed compiler would have to FIRE at cell 1 with latency $\ell\in(3/10,9/10)$ from its admission. Exact routing would then deliver the return at $f+1/20+\ell+1/20$, strictly between $f+2/5$ and $f+1$. The native root cell remains FAST until $f+1$ by the nominal FAST law. Its return cannot match the compiler's READY admission. This timing contradiction rules out the stated refinement for these relaxed parameters. It does not require a construction of the short-delay native run. The lower bound 8 used in the class is sufficient for the whole transaction to settle.

## Relation to the reciprocal witness

The full #148 reciprocal witness is outside the class. It starts with staggered births and source trains, and its third forward delivery to B (cell 1, port 1, between 176 and 178) occurs while B is still in SLOW after its prior FIRE. Its same-cell gap from the preceding admission is at least $79/10$. The gap by itself therefore fails to establish READY. [NativeTiming.lean](NativeTiming.lean) derives this SLOW window from the actual recovery band, latency bounds, and wire timing in `third_forward_predicted_slow`.

This receipt is a second control against inferring READY from the arrival gap alone. In [NativeRefinement.lean](NativeRefinement.lean), `ProtectedReceipt.recovery_dose` gives zero gain dose and recovery dose $1/10$, and `ProtectedReceipt.not_settled_exclusive` shows that the arrival precedes reopening. A READY-only guarded step with MARK disabled writes zero recovery on either branch, so it cannot reproduce this native transaction.
