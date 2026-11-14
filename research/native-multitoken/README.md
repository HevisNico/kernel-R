# Phase 0 · A trained native ring with simultaneous tokens and SLOW receipts

This note freezes a class and a refinement target for review. Existence,
refinement, and the counterexamples below are design obligations for a later
Lean implementation. The baseline is [the dated guarded theorem][dated],
[the single-token ring design in #152][ring], and [the merged #148 reciprocal
refinement][reciprocal].

## Native class

Fix any $N\ge2$. Use the nominal `KernelR.Hybrid.Execution` model and
`FutureControls.parameters 0` at every cell. The prepared snapshot has
time zero, READY main and auxiliary modes, inactive RAW, main charge
$1/10$, auxiliary charges $1/40$, recovery $9/50$, and energy 50.
Native ports 0 and 2 represent the two guarded gain coordinates. Put gain
$\log A_i$ on port 0 and log-gain zero on ports 1 and 2. The data are the
positive rational amplitudes $A_i$, two rational gaps $g_1,g_2$, a
successor map $s$, and rational physical edge delays $\delta_i$.

For every cell, seed one port-0 delivery at each of the three common dates
$t_1=1$, $t_2=1+g_1$, $t_3=t_2+g_2$. The only outgoing contact
on cell $i$ is open on $[t_3+3/10,t_3+9/10]$. During that window a
FIRE at clock $f$ emits exactly one delivery to port 2 of $s(i)$ at
$f+\delta_i$. The native router uses only the firing cell and clock. The
first two external waves are intended to give one ERROR write each, the
third to FIRE with no write, and each routed receipt to give one MARK write
during SLOW. Distinct cells may accept deliveries simultaneously. FIRE on the third wave at every cell gives $N$ issued children
pending together before any of them is admitted.

## Membership from parameters

The checker takes the tuple above and uses the following tests. All
inequalities refer to supplied parameters or independently certified scalar
constant bounds. The checker receives no event table, successful trace,
realized write count, FIRE clock, or reachability premise.

| Test | Parameter condition |
| --- | --- |
| **G. Trained gain window** | For each $i$, $9/5\le A_i\exp(6/5)\le2$. |
| **T1. Training separation** | $g_1,g_2\ge8$. |
| **R1. One incoming receipt** | $s$ is a permutation with one cycle. The proof needs indegree one. The single-cycle part specifies the topology. |
| **T2. After FAST and original auxiliary completion** | For every edge $i\to s(i)$, $3/10+\delta_i>9/10+1$. |
| **T3. Protected until the receipt settles locally** | With $h=419/300$, require $\frac9{50}(\delta_i+\frac35-1)+\frac7{25}h<\frac9{10}$ on every edge. |

Use the following fixed outward rational intervals.
$1.822<\exp(3/5)<1.823$ and $3.320<\exp(6/5)<3.321$ suffice. For G compare $3.320 A_i$ with $9/5$ from below and
$3.321 A_i$ with $2$ from above. This also bounds the first
two amplitudes by $2/3.320$ and $2(1.823)/3.320$, respectively.
Both are below $7/6$, so the weak requirement is derived rather than
included as a separate membership test. There is no
search over rounding precision. Use the inequalities in the table for
the soundness argument, and those rational comparisons for deciding
membership. $\log(5/2)>9/10$ is the strict lower bound used in T3.

The [first-cycle schedule][aux] supplies $h$ as a strict upper bound on
auxiliary completion from RAW intake. RAW itself lasts one time unit. The third-wave latency bounds give
$f_i\in(t_3+3/10,t_3+9/10)$. For a routed receipt $r_i=f_i+\delta_i$,
T2 puts its date strictly after the target's FAST end $f_{s(i)}+1$ and
after the upper deadline $t_3+h$ for third-wave RAW and auxiliary
completion. On the launch, the READY MARK phase ends before the
earliest FIRE. The strong local continuation must establish that ERROR
starts after FIRE and ends before READY reopens. Up to receipt the
target has fixed recovery $9/50$. During the receipt, use a provisional
one-input bound $b\le9/50+1/10=7/25$ on recovery, before proving the
full MARK write. The integrated SLOW rate from FAST end through
$r_i+h$ is then bounded by the left side of T3, strictly below the
logarithmic charge drop needed to reach $1/10$ from $1/4$. An
implementation must establish the provisional bound from the MARK drain
and the unique incoming RAW, prior to using the extended SLOW window.
This avoids assuming a completed dose to prove that it completes. The
gain and recovery rails have fixed headroom, since the planned amplitudes
stay at most 2 and recovery stays at most $7/25<11/10$. Positive energy,
the provenance of the auxiliary deadline, and preservation of the
prepared READY-coordinate bounds are proof obligations for these fixed
native parameters.

For a nonempty family, choose $A_i=3/5$, $g_1=g_2=8$,
$s(i)=i+1\bmod N$, and $\delta_i=5/2$. T3 has left side less than
$0.770$. The tests allow nonuniform delays and amplitudes. All $3N$
source deliveries start pending. T2 also implies that the last
third-wave FIRE precedes the first routed admission, so at least $N$
issued wire tokens are in flight together even after the initial source
queue has drained.

## Calendar compiled from the tuple

Use four keys per cell: first training, second training, launch, and
receipt. The destination and port are fixed by the key. The phase is fixed
by the key at every date, READY for the first three keys and SLOW for
the receipt. Hypothetical FIRE
branches of training and receipt keys issue no successors. A launch occurrence
at date $t$ issues one receipt at $t+\lambda_i+\delta_i$, where
$\lambda_i$ is the compiled launch latency below. Define this relative
route for all dates, so causality holds even for occurrences outside the
reachable set. On the seeded launch date $t_3$ this is the exact due date.

Compute the nominal launch clock independently of the native trace.
The first two rounds stay READY. For nominal parameters, the earliest ERROR
entry on each of those rounds is strictly after the end of the unit RAW
pulse: the SILENT drain alone takes $53/50>1$. The main charge at
$t+1$ is consequently the frozen-gain `readyPulse` evaluated with
the scalar pre-read charge and amplitude. Between the end of RAW and
the next seed date, propagate the main charge by
$q(t+u)=1/10+(q(t)-1/10)\exp(-u/2)$. Update the amplitude by
$\exp(3/5)$ per predicted completed ERROR cycle. Starting from
$1/10$, this gives the launch pre-charge. Define the launch clock as
$t_3$ plus the least root of the threshold equation for that charge and
the amplitude $A_i\exp(6/5)$ in $(3/10,9/10)$. The compiled receipt
date is that exact real clock plus $\delta_i$. Root existence,
transversality, and equality with the native FIRE clock are part of the
target. The rational membership test never compares two such roots.
The exact calendar can be noncomputable in Lean. Same-date distinct-cell
arrivals are permitted, so no comparison algorithm for exact ties is needed.

Compile the guarded score with $d=4$, bias $-6$ on port-0 keys, bias
$-2$ on receipt keys, and recovery weight zero. Enable silent learning
on READY and enable MARK only on a silent SLOW receipt. Port-0 scores in
the planned waves are $-6,-2,2$ and receipt scores are $-2$.
Use guarded score-error interval $[-1,1]$ throughout. MARK affects
native SLOW timing through the recovery rate. Its effect here is handled
by T3 and the calendar proof, while the guarded integer scores use fixed
phase-specific biases. The integer interval concerns errors in guarded
decisions.

For the reserve, credit each key with its maximum branch demand per
coordinate, including credit of its descendants. Only the launch has a
child. With a possible silent gain write on the launch, $Q=3$ per
coordinate is sufficient over the seed list on both branches. Use
normalized $B=0$, rail $U=13$, $W=4$, and $\eta_0=1$.
Each launch has rank 2 and each other key rank 1, giving seed rank $4N$.
Causality follows from T2 and the positive FIRE latency. Distinct
same-cell keys have strictly distinct dates (T1 and T2). Indegree one
keeps just one receipt key per target, so at a tied minimum all eligible
occurrences target distinct cells. Dated tie admissibility follows from
that property. Physical headroom uses the actual two gain writes and one
MARK write per cell. The reserve's hypothetical third gain write is
used for the guarded bound only.

## Frozen target statement · unproved

For every accepted tuple, let $S,\theta,R,C,\mathrm{seed}$ be the
snapshot, parameters, native router, calendar and guarded seed compiled
as above. Let $T=t_3+10$. There exist a native execution $E$ from
$S$ complete through $T$, a list of $4N$ transactions, and a guarded
endpoint $u$ such that:

1. `TransactionReplay C 4 (· ≤ ·) (MarkFeedback.initial N seed) rows u`
   holds with the stated score interval on every row. Its admission list
   is the exact native delivery word, including due dates and input
   coordinates. Each row has the native main mode at its admission; its
   FIRE date and emitted children agree exactly with the native FIRE
   and routing ledger, including multiplicities. In particular the FIRE
   multiset has one exact clock per cell. The children ledger includes
   every issued receipt. At each matched admission prefix, compare the
   native queue using the in-flight accounting below. Both final queues are empty.
2. The first two port-0 admissions at every cell give exactly one
   $3/5$ log-gain write each and zero recovery writes. Launch gives
   FIRE with zero writes, and each port-2 SLOW receipt gives exactly
   one $1/10$ recovery write, zero gain writes and no FIRE. Native
   gains and recovery stay below their physical rails at every time.
   At common settled cuts after each training wave and at $T$, native
   memory equals prepared memory plus coordinatewise unit dose times
   the guarded count of the associated prefix. Port 1 remains unchanged.
   Since $b\ge9/50$ throughout SLOW and $\log(5/2)<1$,
   reopening is before $f+1+50/9<t_3+10$. T3 keeps each receipt
   protected through its local completion before reopening. A final
   quiet suffix gives completeness through $T$. At $T$ the counts
   on native ports 0 and 2 and on recovery are $2,0,1$ respectively.
3. The compiled guarded calendar satisfies
   `PhaseAdmission.dated_network_memory` with the constants above.
   Maximal certified earliest-date schedules with error in $[-1,1]$ have the
   same decisions per key, with ties allowing different serialization.
   They drain in $4N$ transactions and have the same terminal counters.
   Every complete native run on the fixed input has the same endpoint
   and FIRE multiset by observational uniqueness. The existential replay
   is for the constructed execution.

The guarded launch transaction enqueues its children at admission in the
abstract transition. Native enqueuing occurs at FIRE, later in the same
launch wave. At native cuts through that wave, compare the guarded
pending multiset with native pending plus exactly the not-yet-issued
children of consumed launch keys. Discharge a child from that extra
multiset at its FIRE. No receipt can be due while this set is nonempty
by T2. No individual admission cut is required to settle all the other
cells, or to complete that admission's own write. Justify prefix
correspondence with native delivery/FIRE cuts and settled wave cuts
separately. The target contains no claim about native jitter,
staggered births, or unbounded traffic.

## Reuse and new obligations

The single-token proof is being developed in #152. The entries below
name existing lemmas and proposed interfaces from that design so the
reuse does not depend on unfinished branch symbols.

| Source | Reuse | New obligation |
| --- | --- | --- |
| [`quiet_source_arrival_exists` and `quiet_complete_exists`][quiet] | Quiet scalar waits and complete cuts. | Admit the full minimal-date batch and assemble overlapping local flow/jump segments at the union of their event dates. The former lemma's updated snapshot has a single intake and cannot construct the active batch. Show preservation of pending multiplicities. |
| [`weak_input_cycle_exists`][weak] | Local ERROR cycle, $3/5$ dose and restoration of `ReadyCoordinates`. The parameter inequalities fit both visits. | Construct each one-cell leg with a local queue and an empty router, then synchronize the product. Reuse [the existing autonomous projection][project] for local observations when its premises hold. It does not supply the converse product. Prove exact transport of the per-cell ledger and decay of residual charge before the next wave. |
| [`first_learned_fire_exists` and `readyPulse_first_learned_crossing_transversal`][fire] | Exact root and local FIRE segment. Reuse the single-token construction's planned FAST/SLOW legs where their assumptions hold. | Cut active product traces at distinct or tied FIRE clocks. Evaluate the real router at each global FIRE jump and amend the pending queue there. Build the protected receiver path with its early incoming receipt instead of requiring a complete, quiet SLOW return before it. |
| [`predicted_phase_after_fire`][timing], [`Execution.cadence_mark_only_pulse`][mark], and [`ProtectedReceipt.recovery_dose`][native] | The phase-window comparison, one-input recovery budget, and nominal MARK/ERROR ledger accounts. The cadence lemma inspects a supplied sufficiently long run. | Use [the one-cell cadence constructor][mark-exists] as a local reference. Generalize its charge-window premises to T3 and construct and synchronize the protected intake, MARK, auxiliary return and main reopening. Establish the budget before invoking T3. A synchronized constructor for these parameters and dates remains open. |
| [`Execution.token_balance`][balance], [`native_queue_replay`][native], [`TransactionReplay.append`][replay], and [`dated_network_memory`][dated] | Token conservation, replay algebra, and guarded convergence. #148's [`nominal_reciprocal_refinement`][reciprocal] is the reference for aligning admission/FIRE words, retaining pending occurrences, and comparing memory coordinatewise. | Compile exact clocks and phases and construct replay rows; prove the in-flight accounting, per-wave dose fold, uniform reserve and rank, and the distinct-cell tie condition. #148's fixed transaction table and counts depend on its witness. |
| [`Execution.observational_unique`][unique] | Transport endpoint and FIRE multiset to any complete execution from the same snapshot. | Match the completeness horizon and verify the nominal physical invariant for the compiled snapshot. |

## Negative controls for the new membership tests

Use the accepted family above with $N=2$ unless a change is stated.
Each row gives a parameter change and the target obligation it breaks.
These are scoped counterexamples to dropping checks from this compiler.

| Test removed | Counterexample |
| --- | --- |
| **G** | Set both amplitudes to $1/4$. Both training rounds can stay weak, and after two doses the amplitude is below $0.831<7/6$. The third wave remains silent by the weak bound, so it cannot generate a receipt. |
| **T1** | Set $g_1=0$. Two source deliveries at the same cell, port and date require the same RAW slot. The first fills it. The second cannot meet the exact-date and free-slot requirements together. The same failure occurs for $g_2=0$ at the second training and launch date. |
| **R1** | Use $N=3$ with the same amplitude and delay at each cell and set $s(0)=1,\ s(1)=0,\ s(2)=1$. The launches have the same exact FIRE clock by symmetry of their pre-launch states. Cell 1 receives two port-2 children at the same instant, so the second cannot be admitted into the occupied RAW slot. Cell 2 receives none and cannot have the specified recovery count. This control tests indegree. Separately, two disjoint two-cycles preserve indegree one but fail the single-ring topology. |
| **T2** | Keep the synchronized two-cell family and set both delays to $1/2$. Each receipt arrives at its target's FIRE clock plus $1/2$, strictly inside FAST. It cannot be assigned SLOW as required even though T3's upper-window inequality holds. |
| **T3** | Keep the synchronized family and set both delays to $7$. Before any receipt the target reopens by $f+1+\log(5/2)/(9/50)<f+7$. The late receipt is READY, so it cannot pay the prescribed protected MARK dose. |

[ring]: https://github.com/HevisNico/kernel-R/blob/293e86595f1bcacdf5a16b06fdb5438324f4d1fc/research/network-stability/NATIVE_RING_PHASE0.md
[reciprocal]: https://github.com/HevisNico/kernel-R/blob/b0b5ac7e8ed13da8ea7d0224b3288ccc30997c48/research/network-stability/ReciprocalPostBirth.lean#L1513
[dated]: ../network-stability/THEOREM.md
[quiet]: ../../proof/lean/KernelR/HybridQuietSourceArrival.lean
[aux]: ../../proof/lean/KernelR/HybridFirstCycleSchedule.lean
[weak]: ../../proof/lean/KernelR/HybridWeakInputCycleExistence.lean
[fire]: ../../proof/lean/KernelR/HybridFirstLearnedFireExistence.lean
[timing]: ../network-stability/NativeTiming.lean
[project]: ../../proof/lean/KernelR/HybridAutonomousCellProjection.lean
[mark-exists]: ../../proof/lean/KernelR/HybridCadenceMarkOnlyExistence.lean
[mark]: ../../proof/lean/KernelR/HybridCadenceMarkOnly.lean
[native]: ../network-stability/NativeRefinement.lean
[balance]: ../../proof/lean/KernelR/HybridInputBalance.lean
[replay]: ../network-stability/DatedReplay.lean
[unique]: ../../proof/lean/KernelR/HybridUniversalExecution.lean
