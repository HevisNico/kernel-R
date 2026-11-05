# Exact dose counts over a whole execution

The new result in
[`HybridDoseCounting.lean`](../proof/lean/KernelR/HybridDoseCounting.lean)
expresses learned memory in terms of counts of complete, exposed sections of
an actual finite execution. It is a conditional execution theorem, rather
than a new source protocol or an assumption about the dose ledger. Its trace
interface is the native finite `Execution` semantics.

For each cell `i` and port `p`, let `k(i,p)` count complete exposed ERROR
sections and `j(i,p)` count complete protected MARK sections. Then

```text
z_final(i,p) = z_initial(i,p) + (3/5) * k(i,p)
b_final(i)   = b_initial(i)   + (1/10) * sum_p j(i,p)
```

The birth headline uses each cell's own birth memory for the initial value.
Its parameters range over every fixed device in `PhysicalBox`, including
independent cell and port choices in the declared +/-0.3% and +/-10% boxes.
No event date, rate or shared nominal memory occurs in the final formula.
The counts and whether the hypotheses hold can nevertheless depend on those
parameters, the inputs and the router.

`same_increments_of_same_counts` compares two executions with different fixed
parameters, routers, dates and initial memories. Equal section counts imply
equal final-minus-initial memory increments. The separate
`same_memories_of_same_birth_and_counts` also assumes equal initial memories
and concludes equality of final memories.

## What the theorem assumes

- **Full coverage of the execution.** For every cell and port, the trace has
  an ERROR cover and a MARK cover. Every move belongs to an inactive portion
  or to one of the counted full sections. No nonzero partial learning
  contribution is omitted.
- **Complete active sections.** Each counted section has an actual entry
  jump, a phase span from that execution, and an actual exit jump. The
  constructor reconstructs the original execution. ERROR spans stay exposed
  to the READY learning gate; MARK spans stay protected from READY.
- **Strictly open caps and positive energy.** `LearningGatesOpen` requires
  positive energy, log-gains strictly below their physical caps and recovery
  strictly below `11/10` throughout every flow, including its endpoints.
- **Birth and terminal boundaries.** The birth headline requires `BirthState`
  with all auxiliaries initially READY and all auxiliaries READY at the
  terminal boundary. `BirthState` alone also admits tiny ERROR residues;
  these must not be silently counted as complete sections.

A section that starts learning and then loses its main-mode gate cannot be
counted as a full exposed section. An inactive portion has no contribution
because of its modes, not because the user supplies a zero dose. Inactive
portions of auxiliary phases do not themselves change the learned memory.
The cover premise remains necessary even when an execution is complete
through its terminal horizon: terminal saturation alone does not mean every
learning phase has finished.

## Why these are counts of the actual trace

`ErrorSectionCover` and `MarkSectionCover` are inductive covers indexed by an
actual `Execution`. Their constructors admit:

1. An empty execution.
2. An actual move whose relevant actuation is structurally inactive,
   followed by a covered suffix.
3. An actual entry jump, a fully exposed span in the relevant auxiliary
   mode, its actual exit jump, and a covered suffix.

Only the third constructor increments the natural-number count. It records
no equation asserting that a ledger already equals a rational times that
count. The proof derives the full section dose from the operational guards
and integral equations, then adds it over the reconstructed trace.
Different covers of the same execution have the same count.

Each port is covered independently. This allows MARK sections on different
ports to overlap in time. `Execution.recovery_sum_marks` includes every port
in the final recovery increment; the theorem does not impose serial marks.
Simultaneous events are retained as actual jumps and have no direct learning
actuation. Exposure belongs to the phase span, not the ordering of its exit
jump relative to a simultaneous event on another component.

The construction tools in
[`HybridDoseCountingTools`](../proof/lean/KernelR/HybridDoseCountingTools.lean)
compose covers of adjacent actual traces. Port relabeling, router copies and
queue framing preserve their physical entry/span/exit structure. Local
sensor and protocol lemmas construct exposed ERROR and protected MARK covers.

[`HybridSectionRuns`](../proof/lean/KernelR/HybridSectionRuns.lean) records
whether a section is open at a trace boundary. This permits a flow to be cut
inside a learning section and interleaved with another cell's events. A run
closed at both ends reconstructs the original section cover with the same
count; an unfinished run does not provide a complete cover.
[`HybridCausalSectionRuns`](../proof/lean/KernelR/HybridCausalSectionRuns.lean)
uses the actual component paths and mode changes to preserve those runs
through causal weaving.

## Proof route

During a fully exposed ERROR span, the model gives

```text
m' = -L_e*m,   z' = 8*L_e*m = -8*m'
Delta z = 8*(1/10 - 1/40) = 3/5.
```

A fully protected MARK span similarly gives
`Delta b = (1/2)*(1 - 4/5) = 1/10` for that port. The rate affects the phase
duration, but cancels from these complete-section identities.

The cover induction uses `guarded_error_dose` and `guarded_mark_dose` for
full sections and proves zero actuation for inactive moves. It obtains the
whole-execution ledger equations. `Execution.gain_balance`,
`Execution.recovery_balance` and `Execution.recovery_sum_marks` then yield
the memory formulas. Thus the conclusion concerns the entire execution,
including intervening moves, rather than one assumed isolated phase.

The general algebraic theorem is stronger than the birth specialization:
the cancellation needs no particular fabrication box once the actual spans
and their exposure are supplied. The birth headline keeps the box and birth
hypotheses explicit to state the requested physical family.

## Scope of the independence claim

The formula states independence of the **increments**, conditional on the
counts and coverage conditions. It preserves initial variation. Two cells
with different initial log-gains need not end with equal log-gains after the
same count. Likewise, this result does not prove that all parameter choices
produce the same counts or spike dates.

An ERROR count is not automatically a count of failed source pulses. A MARK
count is a count of protected auxiliary sections, not a count of main FIRE
events. The theorem supplies no unbounded storage capacity: the strict caps
limit the admissible counts.

This is exact arithmetic in the mathematical model. Its fixed thresholds,
coefficients and shared drain/learning currents are part of that model.
Hardware readout, perturbations of those relations, a manufactured digital
counter and a general affine split/merge algorithm are not conclusions.

## Reproduction

From `proof/lean` with the pinned Lean toolchain and dependency cache:

```sh
lake build KernelR.HybridDoseCounting
lake build
lake build Audit
python3 scripts/check_hybrid_dose_counting_negative.py
```

The module prints the axiom dependencies of its headline results. The global
audit checks the new declarations along with the existing project. No old
release build counts or archived source certificates are changed by this
addition.
