# N-cell Lean coverage and remaining refinement obligations

This extension formalizes the compositional part of the
[finite-chain argument](../reciprocal_composition/THEOREM.md).
It does **not** turn the entire physical theorem into an unconditional Lean theorem.
The distinction is explicit in theorem signatures, not hidden in project axioms.
The declared N=3 physical cadence is now constructed from A's READY birth
through789.9, with independent B/C births at160/480 and cumulative A54/B61/C34.
Its cadence emits A16/B18/C20. All cells finish READY/q=0.1 with RAW absent and
an empty global queue; own active gains A2/B2/C0 are birth+2.4 and own recoveries
birth+0.3. Other teaching gains are preserved. This constructs one declared
three-cell birth/source family; physical refinement for every finite N remains
open. Its construction is now in progress; see the [finite-chain proof ledger](EVERY_N_PLAN.md).

`birth_protocol_complete_cadence_exists` returns
`ConstructedBirthCadenceProtocol`, retaining both genuine births and the
actual two-cell execution between them. C teaching and cadence execute under
one fixed gated three-cell router. Retargeting preserves the complete physical
ledger and delivered occurrences, and cumulative counts54/61/34 are proved
for that actual staged execution.

The autonomous C witness and P(3,17,0) leaf packet remain components. B's real
receiver emits18 signals and supplies P(5,13,1/20), and A's receiver of the next
wire packet emits16. Causal weaving constructs actual global issuance and
arrival from the original external C25 queue. No reaching execution, receiving
calendar or output count is a factory premise; future wire tokens are not
preloaded into the global source queue. The previous C660 checkpoint and
C-only789.9 endpoint remain historical witnesses.

`HybridBirthLearnedRest` separately bridges Aport2/Bport2 projections of639.9
to isolated learned one-cell contracts with settling7.5. Its empty analysis
queues do not physically remove global tokens. Neither that bridge nor the
finite N=3 construction supplies universal physical contracts for arbitrary
introductions, port permutations or chain length.

## Checked composition

| Written argument | Lean module and declarations | Scope |
|---|---|---|
| Packet definition and spacing | `Chain.Packets`: `Packet`, `Packet.ideal_gap`, `Packet.actual_gap` | Existential ideal dates and bounded phase errors; width-one pulses are separated |
| Wire rule | `Packet.wire`, `wire_actual`, `wire_delay_bounds` | Fixed centres shift ideal dates, arbitrary bounded errors add their full budgets |
| Relay closure | `Packet.relay`, `relay_actual_prefix`, `relay_actual_second_fire`, `relay_actual_first_high`, `relay_actual_regular_tail` | Constructs P(m+2,L-4,J), preserves retained errors and proves exact correspondence to the declared emitted input indices |
| Leaf packet | `leafPacket` | Constructs P(3,K-8,0) from the declared leaf firing dates and latency bounds |
| Constructed physical C leaf | `HybridBirthCadenceLocalC`, `HybridConstructedCadenceLeafPacket` | Actual autonomous C639.9→789.9 ledger refines P(3,17,0); bounded-delay labels refine P(3,17,1/20), used by the constructed causal C→B→A weave |
| Constructed physical N=3 | `HybridLocalCadenceReceiver`, `HybridConstructedCadenceBC`, `HybridConstructedCadenceCascade`, `HybridBirthCadenceCascade`, `HybridBirthCadenceProtocol` | Actual leaf, B/A receivers and causal weave; A54/B61/C34 at789.9; every-N physical specialization remains open |
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

1. Generalize the concrete N=3 construction to arbitrary leaf/relay
   introductions, source queues, contact gates and port permutations. Derive
   physical preparation, availability and terminal saturation for every finite
   chain rather than assuming its local contracts.
2. Prove sound enclosure membership for the remaining exp/log expressions and
   trajectories. Generated endpoint comparisons alone do not supply it.
3. Extend the concrete C leaf and B/A receiver witnesses to the generic
   `RelayLaw` required at arbitrary depth, including exact event counts,
   protected doses, raw tails and latency bounds for each new introduction.
4. Formalize retained frozen probes, cuts/settings copies and their physical
   preservation semantics.
5. Establish universal refinement across every admissible execution and finer
   operational robustness. Constructive existence for this fixed N=3 family
   does not quantify over every event ordering or operational perturbation.

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
The preceding autonomous-C/leaf-packet checkpoint passed the complete pinned
build (9,458 jobs) and global audit (25,538 project theorems), with 405 Lean
source files and five unchanged upstream modules. Generated evidence, all 16
robust certificates and 12 project tests passed. Its 53 additional paired
controls passed: 25 local-C-tail, 20 constructed-leaf/projection and eight
actual high-return-prefix checks. The high suite had 32 passing pairs, and
that checkpoint configured 877 controls.

The complete N=3 export passes the pinned build (**9,489 jobs**) and global
axiom audit (**26,317 project theorems**), allowing only `propext`,
`Classical.choice` and `Quot.sound`. Source checks cover **436 Lean files** and
five unchanged upstream modules; generated evidence, all **16 robust
certificates** and **12 project tests** pass. All new proof modules compile
with the default heartbeat limit.

All **226 new paired controls pass**: 48 cascade/birth/protocol, 30 receiver/BC,
34 strong-jitter source, 22 learned-source prefix, 18 causal weave, 17 high-jitter,
14 jitter span, 12 MARK-only, 12 mixed, 12 router transport and 7 future-frame.
Each valid conclusion compiles before its altered conclusion is rejected with
a Lean diagnostic. CI configures **1,103 paired controls**, plus axiom-audit
corruption checks; this inventory does not assert a fresh local rerun of every
older suite. Fresh CI status and the verified commit are reported on the PR.

The public [headline](KernelR/Headline.lean) groups the existence, actual terminal
state/counts and own learned-memory theorems. The global
[README](../../README.md) records its exact signatures and `#print axioms` outputs;
the [model correspondence](../../docs/MODEL_LEAN_CORRESPONDENCE.md) maps equations
to their operational definitions. N=3 is finalized; the user has authorized the every-N work tracked in
[EVERY_N_PLAN.md](EVERY_N_PLAN.md). The validated baseline figures above remain
those of the N=3 commit; subsequent finite-chain checkpoints have their own audit.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed; no physical
leaf/relay premise is replaced by a project axiom.

The original written theorem and its authenticated snapshots are retained
unchanged. This guide states the current machine-checked coverage separately.
