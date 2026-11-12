# Review guide

Start with [`TrustedHeadline.every_finite_chain`](proof/lean/KernelR/TrustedHeadline.lean)
and the generated [trusted-base reading list](docs/TRUSTED_BASE.md). Read in
this order: the statement, the [cell laws](model/CELL.md) and their Lean
definitions, the crossing semantics, the [chain protocol](model/CHAIN_PROTOCOL.md),
the compared observations, and finally the verification trust (`Audit.lean`, the toolchain, dependency pins
and the trusted-base checker).

CI computes the project-definition closure of the statement independently of
the explicit allowlist and rejects an unlisted dependency or missing trusted
name. Mathematical semantic review therefore focuses on the trusted definitions
and the headline statement; the proofs are checked by Lean. This does not
claim a formally verified implementation of the checker, compiler or libraries,
or experimental validation of a physical device.

Within the crossing-semantics step, review the fidelity of `CrossingExecution`
to the written model. The checked build does not replace this semantic review.
The existing fixed-delay theorem and construction modules supply the proof;
they are not additional semantic assumptions of the trusted statement.

The sections below retain additional review guidance for claims outside that
headline, including learning-section coverage and progress.

For [finite port-memory saturation](docs/GAIN_MEMORY_SATURATION.md), review
`ErrorAvailable`, `CappedErrorSectionCover` and `WeakCappedErrorSectionCover`.
Exposure must retain READY and positive energy while permitting the automatic
cap gate to close. Counted phases need real entry/exit jumps and uninterrupted
ERROR states; inactive portions need mode-based reasons, not zero-dose
premises. The crossing result uses the actual `run.execution` cover, with a
coordinate-preserving single-flow argument rather than arbitrary-network
native/crossing correspondence. The theorem gives a conditional section-count
threshold, not input-to-section existence or a universal deadline. Cap
permanence concerns only the selected port's log-gain. The explicit stationary
at-cap witness does not prove reachability from below or from protocol births.

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

Compare the [written main and auxiliary rules](model/CELL.md#main-unit)
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

## Zero recovery outside the chain protocol

For the [separate zero-recovery result](docs/RESET_ZERO_RECOVERY.md), review
the unchanged SLOW field, recovery actuator gates and reopening guard first.
`NoMarkFlows` must refer to the selected cell's actual sensor modes on each
positive-duration flow; it does not assume the locked-mode conclusion.
The arbitrary-network crossing proof is direct in `WeakExecution` and then
`CrossingExecution`, without a generic model-to-native conversion.

Keep the hypotheses of the native quiet-sensor corollary distinct: no new
arrivals alone does not exclude a pre-existing MARK phase or active raw pulse.
The repair theorem requires an actual isolated fully exposed MARK section.
Check the explicit constant-flow witnesses, including the reserve equilibrium
99.89 and the current physical bounds. Zero recovery is admissible there but
is outside the declared nominal birth band. The result neither changes the
chain theorem nor proves the broader Reset Operator claim.

The [validation ledger](docs/VALIDATION_LEDGER.md#validation-and-checkpoint-discipline)
records the build, axiom audit and paired controls separately from this human
review obligation.

## Recovery-limited firing rate

Review the [separate rate statement](docs/RESET_RATE_SATURATION.md) and its
actual-path `RecoveryBound` premise. Initial recovery alone is insufficient for
a custom envelope because protected MARK phases can increase it. Review the
FAST/SLOW decomposition, actual firing labels and the one-firing finite-window
allowance. The arbitrary-network crossing result follows directly from weak
paths, not from a protocol-scoped correspondence. No arbitrary-queue progress
or loss of all excess inputs is inferred. The broader Reset Operator thesis
remains separate.

## Trained cells, networks and searches (v0.4.0)

These results are in
[`research/recursive-learning/native/`](research/recursive-learning/native/README.md#map-of-the-stop-learning-results),
outside the trusted base of `proof/lean`. They reuse its kernel definitions
unchanged. Review first the regime in
[STOP_LEARNING_SPEC.md](research/recursive-learning/native/STOP_LEARNING_SPEC.md):
the thresholds of the trained port, the 22-unit pulse spacing and the
`RestState` invariant between pulses.

Then check that each headline theorem quantifies over every complete run,
not only the constructed one (`stop_training_exists`, `trained_read_exists`,
`trained_coincidence_network`), and that its hypotheses are met by the named
witnesses (`trainedCell_witness`, `trained_chain_witness`,
`successive_search_witness`). In the searches, a wire that releases pulses
at preset dates stands for a clocked register that is not built from cells;
the [limits](docs/RELEASE_V0_4_0.md#limits) list this and the other modelling
choices. The [validation ledger](docs/VALIDATION_LEDGER.md#native-package-audit-v040)
records the axiom audit of the package.
