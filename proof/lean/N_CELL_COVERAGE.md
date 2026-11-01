# N-cell Lean coverage and remaining refinement obligations

This extension formalizes the compositional part of the
[finite-chain argument](../reciprocal_composition/THEOREM.md).
It does **not** turn the entire physical theorem into an unconditional Lean theorem.
The distinction is explicit in theorem signatures, not hidden in project axioms.

## Checked composition

| Written argument | Lean module and declarations | Scope |
|---|---|---|
| Packet definition and spacing | `Chain.Packets`: `Packet`, `Packet.ideal_gap`, `Packet.actual_gap` | Existential ideal dates and bounded phase errors; width-one pulses are separated |
| Wire rule | `Packet.wire`, `wire_actual`, `wire_delay_bounds` | Fixed centres shift ideal dates, arbitrary bounded errors add their full budgets |
| Relay closure | `Packet.relay`, `relay_actual_prefix`, `relay_actual_second_fire`, `relay_actual_first_high`, `relay_actual_regular_tail` | Constructs P(m+2,L-4,J), preserves retained errors and proves exact correspondence to the declared emitted input indices |
| Leaf packet | `leafPacket` | Constructs P(3,K-8,0) from the declared leaf firing dates and latency bounds |
| Universal induction | `Chain.Induction.compose_every_finite_chain`, `root_contract` | Every positive finite N; validates every intermediate tail and cumulative jitter budget |
| Actual stream interface | `Chain.Refinement.realized_chain` | Composes explicit routed streams, given a leaf refinement and local `RelayLaw` proofs |
| Resource algebra | `Chain.Algebra`, `traffic_closed_form`, `traffic_at_minimum` | Twelve integer identities, natural-number counts, root tail, root emissions and quadratic total traffic |
| Jitter specialization | `pathJitter_mono`, `uniform_jitter_total`, `full_jitter_iff_four_cells`, `fixed_delays_any_depth` | Nonuniform cumulative budgets; uniform min(1/20,3/(20 links)); full 1/20 jitter is sufficient through four cells |
| Dose words and settings | `Chain.Consequences` | Leaf/relay word counts, four total ERROR doses, two fast MARK doses, gain exp(12/5), final recovery interval |
| Cuts and terminal time | `cut_propagates`, `all_cells_quiescent_by` | Induction from explicit local silence and settling-time hypotheses |
| Same-gain root ordering | `same_gain_ready_comparison`, `first_crossing_no_later` | Residual charge cannot delay the first crossing when comparing the same realized gain |
| Local certificate endpoints | `Certificates.Composition003`, `Composition010` | All 162 strict comparisons and validity of all 352 rational enclosures in the two committed certificates |

The finite signal interface records an exact event count, so its refinement
contract excludes both missing and additional emissions. The packet representation
includes bounded padding phases beyond the finite packet.
Only indices below m+L represent actual events. This lets retained phase errors be
selected without adding a physical independence or retiming assumption.

The natural-number theorems prove the subtraction side conditions; integer
polynomial identities alone would not justify truncated natural subtraction.
No theorem restricts N to a tested maximum, and none assumes identical devices.

## What is still required for the full physical theorem

1. Instantiate the existing hybrid execution semantics and staged-birth extension
   with the leaf/relay protocols, including their source queues and contact gates.
   Prove protocol-specific existence/progress, port availability and terminal
   saturation. The semantics, physical bounds and finite-prefix event budget
   are already checked; they do not alone construct these executions. A genuine
   source-driven prefix is now constructed from every READY A birth with the
   original thirty-two-source queue, through its first MARK in (0.01,0.025),
   retaining thirty-one future tokens. Its later continuation remains open.
2. Sound enclosure membership for the actual exp/log expressions and trajectories.
   The generated Lean files prove exact endpoint comparisons, not that the
   physical quantities lie between those endpoints.
3. Complete preparation reachability for the leaf/relay protocols, including
   port permutations and later staged introductions. The first low-port phase,
   the complete conditional A38/B43/C14 prefix across births at 160 and 480,
   prepared-input returns and physical reserve invariance are checked in the
   [hybrid guide](HYBRID_EXECUTION.md).
   The B-to-C teaching transition through 639.9 now preserves A/B memories,
   derives C's own preparation and retains its future source queue. Period-four
   cadence initiation now reaches the actual fourth C input at 652, retaining
   its residual charge and all later sources. The local strong, MARK-only,
   combined MARK/ERROR and high-gain learned cases are proved from current
   physical bounds. The actual cadence cascade is now assembled through 789.9:
   C20/B18/A16, cumulative A54/B61/C34, own acquired memories and an empty
   final queue, conditionally on the supplied reaching executions. Arbitrary
   later introductions and physical every-N refinement remain open.
4. Proofs of the leaf refinement and `RelayLaw` from those semantics. In
   particular, no omitted or extra emissions, the full protected doses, the
   residual-raw-tail bound and the first-crossing latency bounds must be derived.
5. Physical silence/setting preservation after cuts, the local settling bound,
   and the 0/8, 4/8 and 8/8 frozen-probe response patterns.

Existing `Doses`, `Flow`, `Recovery`, `Energy` and `Cadence` lemmas support
these obligations but do not already discharge all of them. The local contracts
are ordinary quantified premises: callers cannot obtain a physical theorem
without supplying them. There are no admitted proofs or new axioms.

## Reproduction and falsification

Run the commands in the [Lean guide](README.md). The generated-evidence check
covers both N-cell certificates. The axiom audit includes every imported chain
and certificate theorem. Negative tests reject altered traffic counts and an
over-budget four-link jitter claim, in addition to the existing endpoint,
cadence and adaptive-record corruption cases.

The original written theorem and its authenticated snapshots are retained
unchanged. This guide states the current machine-checked coverage separately.
