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

The [validation ledger](proof/lean/EVERY_N_PLAN.md#validation-and-checkpoint-discipline)
records the build, axiom audit and paired controls separately from this human
review obligation.
