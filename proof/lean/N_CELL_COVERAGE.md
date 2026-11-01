# N-cell Lean coverage and remaining refinement obligations

This extension formalizes the compositional part of the
[finite-chain argument](../reciprocal_composition/THEOREM.md).
It does **not** turn the entire physical theorem into an unconditional Lean theorem.
The distinction is explicit in theorem signatures, not hidden in project axioms.
The separately constructed birth prefix now reaches the first cadence C→B→A
wave, ending at A's actual FIRE in(653.8,655.1): cumulative A39/B44/C15 and
exact21 Cport0 sources656..736 pending. A is FAST at q=1; B/C retain actual
cuts, modes, raw states, energy paths and continuations. Own memories remain
as at the earlier first C-to-B receipt, including Cport0+1.8 and no new MARK.
The historical639.9 checkpoint retains three prepared cells, RAW absent and25
C sources. Both births at160/480 are genuine and independent. This finite
prefix does not supply physical leaf/relay contracts for arbitrary introductions
or every finite N.

`HybridBirthLearnedRest` separately bridges Aport2/Bport2 coordinate projections
of the639.9 state to isolated learned one-cell contracts with settling duration7.5.
The empty analysis queues do not physically remove global C tokens. Cport1's
gain is outside the imported narrow domain; the bridge does not instantiate
network routing or the finite-chain physical contracts.

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

1. Instantiate the hybrid semantics with physical leaf/relay protocols, source
   queues and contact gates, proving existence, port availability and terminal
   saturation. The constructed READY birth prefix reaches639.9 with
   A38/B43/C14 and the exact25 C640..736 sources. All three cells are
   prepared/q=0.1 with RAW absent. A's own port0/port2 log-gains have each
   gained1.8; B's own port1/port2 log-gains have gained0.6/1.8; C's own
   port1 log-gain has gained0.6. Each recovery has gained0.1 from its own
   independent birth value; all other gains are retained. The intermediate352
   weak cut and the low-recovery C path through496 remain in the witnesses,
   without charge resets. The new first cadence wire adds Cport0+1.8 and
   reaches H in(652.7,653.3) with A38/B43/C15 and21 future C sources. B is
   prepared with fresh RAW; C retains its true FAST cut. The subsequent
   first C→B→A wave reaches A's actual FIRE in(653.8,655.1), with cumulative
   A39/B44/C15 and the same21 sources. A is FAST/q=1 and B/C retain actual
   cuts; no new MARK occurs. The global656 handoff, remaining cadence and
   arbitrary-N constructions remain open. See the
   [current checkpoint and factory map](HYBRID_EXECUTION.md#constructed-protocol-checkpoint).
2. Sound enclosure membership for the actual exp/log expressions and trajectories.
   The generated Lean files prove exact endpoint comparisons, not that the
   physical quantities lie between those endpoints.
3. Complete preparation reachability for arbitrary leaf/relay introductions
   and port permutations. The specific original-birth A/B/C execution through
   639.9 and its first C→B→A cadence wave are constructed. The complete cadence through789.9 (A54/B61/C34)
   derives own memories, exact traffic and the final empty queue
   **conditionally on a supplied later execution**. These results do not
   construct arbitrary later introductions or an arbitrary-N execution.
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
cadence and adaptive-record corruption cases. The 29 paired controls in
`python scripts/check_hybrid_feedback_entry_negative.py` additionally check
the constructed weak entry and first reverse FIRE, own memories and exact
source/wire queues. The 40 additional paired controls in
`python scripts/check_hybrid_reverse_receipt_negative.py` pass for the
actual first receipt and352 handoff, own memories, exact queues and
A28/B15. The 40 subsequent pairs in `python scripts/check_hybrid_reverse_epoch_negative.py`
cover the constructed reciprocal epoch through459.9, its actual
sources and wires, retained own memories and A38/B27: all valid conclusions
compile and all altered claims are rejected. The 50 new pairs in
`python scripts/check_hybrid_c_teaching_existence_negative.py` pass for the
actual C birth/teaching, three-cell execution, own memories and A38/B43/C14.
The first-wave checkpoint passed the complete pinned build (9,440 jobs) and
global audit (24,948 project theorems). Source identities cover387 Lean files
and five unchanged upstream modules. Generated evidence, all16 robust
certificates and12 project tests pass. The43 new first-wave paired controls
pass: each valid conclusion compiles and every altered conclusion is rejected
with a Lean diagnostic. The preceding22 first-strong and40 first-wire paired
controls also passed. CI configures751 paired controls; this inventory does
not assert a local rerun of every suite. Fresh CI status is reported on the PR.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed; no physical
leaf/relay premise is replaced by a project axiom.

The original written theorem and its authenticated snapshots are retained
unchanged. This guide states the current machine-checked coverage separately.
