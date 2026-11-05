# Review guide

**Review the fidelity of `CrossingExecution` to the written model first.**
Lean checks the proofs against the formal definitions; human review must judge
whether those definitions express the intended model. The checked build does
not replace this semantic review.

For exact dose counting, review whether `ErrorSectionCover` and
`MarkSectionCover` in [HybridDoseCounting](proof/lean/KernelR/HybridDoseCounting.lean)
express complete exposed sections of the actual execution: real entry and
exit jumps, uninterrupted phase exposure and coverage of every learning
contribution. Their `inactive` constructors must justify zero actuation from
modes alone; clipping or a closed energy gate must not hide partial learning.
See the [counting hypotheses](docs/EXACT_DOSE_COUNTING.md).

For [open-section runs](proof/lean/KernelR/HybridSectionRuns.lean), also check
that cutting a flow retains an already-open phase and its actual entry and
exit. A cut or an interleaved event on another cell must not create a new
complete section or discard a partial one. Review this preservation through
the [causal weave](proof/lean/KernelR/HybridCausalSectionRuns.lean).

Compare the [written main and auxiliary rules](kernel/README.md#main-unit)
with [HybridCrossingExecution](proof/lean/KernelR/HybridCrossingExecution.lean),
the [full-cell right continuation](proof/lean/KernelR/HybridCellOrbitGerm.lean)
and the [correspondence map](docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings).
In particular, review:

- FIRE/MARK require a strictly-below left neighborhood in the actual recorded
  history and an incoming-mode ODE continuation strictly above threshold on a
  right neighborhood. The latter solves all coordinates of the contact cell,
  including gains, recovery and energy, and continues counterfactually before
  applying the mode change. Review this convention at simultaneous events too.
- Crossing is geometric: positive slope is sufficient, but is not part of the
  definition. `WeakFlow` permits a threshold touch without firing.
- `CrossingCompleteThrough` excludes exactly the jumps satisfying their
  historical and right-crossing guards, including at the terminal date.
  The descending guards and raw/queue urgency remain in force.

The [descending-guard explanation](docs/MODEL_LEAN_CORRESPONDENCE.md#descending-guards)
gives the positive rates and recovery bound that make equality an unambiguous
downward crossing in the physical family.

After the definitions, review the theorem directions and hypotheses in
[CrossingChainHeadline](proof/lean/KernelR/CrossingChainHeadline.lean) and
[HybridCrossingProgress](proof/lean/KernelR/HybridCrossingProgress.lean).
Model-to-native refinement retains the exact paths and jumps; the converse
provides an observationally equal crossing representative. The correspondence
is proved for the declared finite-chain protocol, not for arbitrary initial
states or inputs. Infinite/maximal-run theorems retain their native interface.

## Parametric native family

The new [`Family`](proof/lean/KernelR/Family/) layer creates a separate
semantic review obligation. Compare [`Model`](proof/lean/KernelR/Family/Model.lean)
and [`Nominal`](proof/lean/KernelR/Family/Nominal.lean) with the unchanged
`Hybrid.lean`: each substituted constant, all field/work terms, the strict
flow preguards, every native jump guard/update, RAW support and queue urgency
must express the intended parameterization. Review both directions of the
nominal conversions, including preservation of the actual paths and terminal
completion. The bridge is to the native first-contact semantics; it is not a
parameterization of `CrossingExecution`.

Also review the hypotheses and limits of the new structural results:

- One `Constants` value is common to a network. Original fabrication
  parameters still vary per cell and port; the family does not silently
  enlarge `PhysicalBox` or change `BirthState`.
- `ErrorSectionCover` and `MarkSectionCover` in
  [`Family.DoseCounting`](proof/lean/KernelR/Family/DoseCounting.lean) must
  describe the actual complete exposed sections and account for every
  learning contribution. Counts may vary with a protocol; equality across
  members requires equal section doses, not only equal counts.
- `Flow.path_unique` in
  [`Family.FlowUniqueness`](proof/lean/KernelR/Family/FlowUniqueness.lean)
  retains coefficient signs, nonnegative rates and safe-path hypotheses.
  Initial-state positivity lemmas retain a separate positive-energy premise.
  [`Family.Energy`](proof/lean/KernelR/Family/Energy.lean) can discharge it
  through a positive reserve barrier under an explicit actual-work ceiling;
  review that this ceiling is not presented as a proved work estimate for a
  new protocol. `Jump.local_diamond` is local and native, modulo pending-list permutation;
  combining these results into arbitrary-family global execution uniqueness
  requires further work.
- The quiet witnesses prove nonempty safe execution classes without sources,
  learning or FIREs. They do not discharge active training/cadence existence.
- The [protocol-conditions catalogue](docs/PARAMETRIC_PROTOCOL_CONDITIONS.md)
  covers historical certificates and selected current Lean interfaces. Check
  that its sufficient inequalities are not described as necessary conditions
  or as an exhaustive dependency analysis of the current every-N proof.

The original crossing, physical-box, birth and finite-chain theorems keep
their existing scope. New paired controls and axiom checks support this
review but do not replace it.

The [validation ledger](proof/lean/EVERY_N_PLAN.md#validation-and-checkpoint-discipline)
records the build, axiom audit and paired controls separately from this human
review obligation.
