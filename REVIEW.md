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
The applied `exact_section_counts` theorem constructs covers for the retained
finite-chain witness. Review this quantifier separately from the universal
endpoint and FIRE-date comparison: the latter does not construct ERROR/MARK
covers for every competing complete trace.

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
- `CellRightCrossing` is existential over full-cell `CellOrbitGerm` solutions.
  No generic uniqueness theorem for these germs is supplied. At a contact
  with positive incoming field, `CellOrbitGerm.crossing_of_positive_field`
  applies to every germ, so that crossing conclusion does not depend on
  choosing a particular germ. Outside this transverse case, review the
  existential convention as part of the model's semantics.
- `CrossingCompleteThrough` excludes exactly the jumps satisfying their
  historical and right-crossing guards, including at the terminal date.
  The descending guards and raw/queue urgency remain in force.

The [descending-guard explanation](docs/MODEL_LEAN_CORRESPONDENCE.md#descending-guards)
gives the positive rates and recovery bound that make equality an unambiguous
downward crossing in the physical family.

For the fixed-delay statement, review
[`canonicalFiniteChainRouter`](proof/lean/KernelR/HybridFiniteChainCanonicalRouter.lean)
and `ConstructedBirthCadenceChain.router_eq_canonical`. The router in the
public conclusion must be the declared chain with the supplied delays;
its topology must not be hidden behind an existential router. The
[fixed-delay headline](proof/lean/KernelR/FixedDelayChainHeadline.lean) takes
these functions before constructing either semantic witness. The indexed
corollary instead constructs them after the prescribed error family is given.

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
