# Validation ledger

[Proof construction](FINITE_CHAIN_CONSTRUCTION.md) · [Reproduction commands](../proof/lean/README.md#reproduce)

## Validation and checkpoint discipline

### Full Lean validation at 0543640

The complete Lean workflow passed at revision
[`05436400704dc7fc2126d12d38e93d899300363b`](https://github.com/HevisNico/kernel-R/commit/05436400704dc7fc2126d12d38e93d899300363b)
in [CI run 42212189044](https://github.com/HevisNico/kernel-R/actions/runs/42212189044), including the build, global axiom
audit, trusted-base checks and regression controls.

The final report records **9,624 build jobs** (a cached replay of all default
targets, including dependencies) and **29,330 project theorem declarations**
audited. The only allowed axioms were `propext`, `Classical.choice` and
`Quot.sound`, with no admitted proofs or added project axioms. These
measurements describe that revision.

The [`trusted-base-validation-05436400704dc7fc2126d12d38e93d899300363b` artifact](https://github.com/HevisNico/kernel-R/actions/runs/42212189044/artifacts/13502314203)
contains the report and the captured build and audit logs.

### Memory saturation local validation

The separate [port-memory saturation result](GAIN_MEMORY_SATURATION.md)
adds native, weak and direct upward-crossing theorems without changing the
existing dynamics, guards, physical box, chain protocol or trusted headline.
The actual section cover permits cap closure and retains complete ERROR
entry/exit boundaries, READY exposure and positive energy.

Code checkpoint: `2f4d268d7842d53ce8da87af73c7491c02340ca2`, based on main
`0f39642`. Observed local checks on 6 November 2026:

- `lake build KernelR.HybridMemorySaturation KernelR.HybridCrossingMemorySaturation`
  passed; the crossing target used 3,550 dependency/build jobs. This is a
  targeted cached-dependency build, not the project-wide validation total.
- An earlier scoped `MemorySaturationAudit.lean` checkpoint passed for 1,966
  imported project theorem declarations. The final global measurement below
  includes the later stationary witness and is the current integration total.
- Source checks passed for 574 Lean files and the five inherited module
  identities. The frozen source-boundary check passed with only the exact
  new modules and root import added to its allowlist; its old base remains
  unchanged.

The full default local `lake build` passed with 9,626 jobs, including the
unchanged global `Audit` target: 29,425 project theorem declarations, using
only `propext`, `Classical.choice` and `Quot.sound`. All twelve paired
controls passed on the final code, including weak/crossing transfer and the
positive-duration at-cap witness; infrastructure timeouts are not accepted
as semantic rejections. Dependency caches were reused.

A fresh checked Lean export retained the same 84 trusted semantic declarations.
The source-hash record and reading list were regenerated for this checkpoint,
and the authenticated document check passed. These observations do not assert
a fresh external-dependency rebuild, rerun of every historical control, or a
complete green CI run. The stationary positive-duration witness begins at cap; no
cap-reaching section from a subcap protocol birth is claimed.

### Zero-recovery milestone local validation

The [zero-recovery result](RESET_ZERO_RECOVERY.md) is a separate
arbitrary-network obstruction, not a new finite-chain hypothesis or a general
Reset Operator theorem. `HybridZeroRecovery` proves native locked snapshots,
paths and no firing from SLOW/q=1/4/b=0 with no MARK flow on the selected cell.
`HybridZeroRecoveryCrossing` proves the corresponding weak and model crossing
statements directly, retaining that explicit no-MARK premise. The quiet-sensor
input-based corollary is native. A fully exposed isolated MARK repairs b=0 to
0.1; actual complete locked native and crossing witnesses of arbitrary
positive duration are constructed within the current physical bounds.

Code checkpoint: `d8f55708230082d3499ad0d06b62ee90f608f265`, based on main
`0f39642`. Observed local checks on 6 November 2026:

| Measurement | Recorded result and scope |
|---|---|
| Targeted build | The two new modules passed with 3,560 dependency/build jobs under Lean 4.35.0 and the pinned dependencies. This is not a fresh full-project rebuild. |
| Scoped axiom audit | `ZeroRecoveryAudit.lean` passed for 1,996 project theorem declarations in the imported closure, allowing only `propext`, `Classical.choice`, `Quot.sound`. This is not the count of new theorems or a global audit total. |
| New contracts | The modules declare 19 explicit public theorems. Their printed headline axiom profiles use only the three allowed axioms. |
| Paired controls | All 20 pairs passed: one for each new public theorem plus retention of the no-MARK hypothesis. Every original compiled before its altered version was individually rejected; parser and import failures are not accepted substitutes. |
| Non-vacuity | Actual complete locked native and crossing executions are constructed through every later finite horizon; the state is physically admissible for either fabrication box, but is not a nominal birth state. |

The full default local `lake build` subsequently passed with 9,626 jobs,
including the unchanged global `Audit` target: 29,377 project theorem declarations
with only the same three permitted axioms. Dependency caches were reused;
this is not a fresh external-dependency rebuild or a rerun of every historical
control. Completed remote CI is not claimed.

The original source-boundary base and byte-identity checks remain unchanged;
only the two exact new modules, dedicated audit file and added root import
are whitelisted. A fresh checked Lean export retained the same 84 trusted
semantic declarations. The source-hash record and reading list were
regenerated for the code checkpoint and their authenticated check passed.

### Trusted headline: fixed code checkpoint and final-head CI record

The initial mathematical and verification source checkpoint is
[`e7212249c339fdf282423912244d37c6925c0cd6`](https://github.com/HevisNico/kernel-R/tree/e7212249c339fdf282423912244d37c6925c0cd6).
The measurements below retain that initial scope and checkpoint. The generated
[trusted-base guide](TRUSTED_BASE.md) authenticates the current
verification checkpoint, including the auxiliary-attribution follow-up below.

| Measurement | Recorded result and scope |
|---|---|
| Local targeted build | `lake build KernelR.TrustedBase` passed with 3,790 dependency/build jobs. This is a targeted build including imported libraries, not a full-project local build or a source-file count. |
| Scoped local axiom audit | The unchanged `Audit.lean` scanner, importing `KernelR.TrustedBase` instead of the full root, checked 7,050 project theorems in that dependency closure. Only `propext`, `Classical.choice`, `Quot.sound` were permitted. This is not the global CI theorem total. |
| Local trusted statement check | The explicit allowlist contains 84 semantic parent declarations. The checked closure contains no construction structures; attributed compiler auxiliaries are traversed rather than treated as opaque leaves. |
| Local new paired controls | All 19 pairs passed: nine router/headline pairs and ten trusted-checker pairs. These are distinct accepted-original/rejected-mutation cases, not compiler-process counts or a total of the historical suites. |
| Local source hygiene | `check_sources.py` checked 571 project Lean files and the five inherited module identities. `check_trusted_source_boundary.py` authenticated every existing Lean file against base `17928f25086bd8e1765dee1fbf6acce8ebc1b673`; only the declared new modules and added root imports are allowed. |
| Local metadata freshness | A fresh checked Lean export matched the CI-produced declaration names, ranges and auxiliary attribution exactly. The renderer authenticates its fixed source snapshot and every written-model heading. |

The final-head CI record is generated by
[`trusted_validation_report.py`](../proof/lean/scripts/evidence/trusted_validation_report.py) only
after the complete regression sequence succeeds. The workflow preserves it
as `trusted-base-validation-<head-commit>`, including `validation.json`, the
captured full-target build log and global audit log. The JSON separately
records the exact PR `head_commit` and tested merge `build_commit`, CI build
jobs, globally audited theorems, project Lean files and new paired controls.
The PR description links that final record and its observed CI result.

A commit cannot contain its own hash in its checked-in ledger. The generated
CI record supplies the exact final-head reference; the static figures above
retain their fixed code checkpoint and local/scoped labels. They do not
claim that a still-running CI suite has completed. Mathematical human review
follows the [trusted reading path](../REVIEW.md); proofs are checked by Lean.

### Source-declared helper attribution

Verification checkpoint
[`789620b75fe40f983ae2a8a1944796067a157e0c`](https://github.com/HevisNico/kernel-R/tree/789620b75fe40f983ae2a8a1944796067a157e0c)
strengthens the checker without changing the mathematical statement, model
definitions or explicit allowlist. An independently source-declared helper
remains a separate semantic dependency even if its name ends in `match_1`,
`proof_1`, `_f`, or another recognized compiler-support suffix. Matchers also
require Lean's matcher metadata. Other generated support requires parent
source metadata and no independent source range; an equality instance is
attributed to an inductive only when its generated range lies inside that
inductive's source declaration.

The original literal-only counterexample was accepted before this change and
rejected afterwards. The checker inventory contains 49 pairs, covering every recognized suffix
family, private helpers, handwritten equality instances, genuine recursive
and private matchers, deriving with and without fields, helpers declared after
deriving, and separately compiled/imported fixtures. The complete new-suite
inventory is 60 pairs: these 49, two actual-headline checks, and nine
router/headline checks. All 60 pairs passed locally. The CI validation report uses the same
inventory function as the test runner, including imported-module controls.
The targeted `lake build KernelR.TrustedBase` passed locally with 3,790 jobs
and the same 84 semantic parents. A fresh checked export retains exactly the
same declaration metadata and 523 attributed helpers as the initial checkpoint.
The regenerated guide and manifest pin and authenticate this verification
checkpoint. The final-head CI artifact remains the authority for the full
project build, global audit and complete historical regression sequence.

### Explicit fixed-delay headline and reproducibility review

`FixedDelayChainHeadline.every_finite_chain_fixed_delay` takes the native delay
functions as inputs and states existence and universal outcomes in both native
and geometric semantics under `canonicalFiniteChainRouter`. The router's root,
parent, receiving port, contact window and delay index are explicit; the
constructed chain is proved to use that router. No protocol hypothesis or
axiom is added. The indexed-error theorem remains a separate result.

A local build of `KernelR.Recorded`, `KernelR.HybridFiniteChainCanonicalRouter`
and `KernelR.FixedDelayChainHeadline` passes **3,788 jobs**. The unchanged audit
scanner over these modules and their dependencies checks **7,083 project
theorems**, permitting only `propext`, `Classical.choice` and `Quot.sound`, with
no admitted proofs or added project axioms. These are scoped local totals.
Source hygiene passes for **567 Lean files**, including the five unchanged
inherited modules. `Recorded.lean` and its generator now use a finite
8,000,000-heartbeat budget; generated evidence still matches.

All **six paired fixed-delay controls** pass, covering the supplied delay,
both universal semantic contracts and literal parent/port/window/index/root
routing. The configured Lean paired-control inventory is **1,385**
(1,379 + 6). Thirteen project Python tests and all nine range tests pass;
all six range certificates replay independently, with **672 strict obligations**.
Their numerical payloads and pinned point sources are unchanged. All 16 robust
certificates and the generated Lean evidence replay unchanged.

The README's global **9,618 jobs / 29,298 theorems** are explicitly anchored
to `b5435f3`, not this revision. The complete suite at that checkpoint stopped
at its 90-minute limit after its build, audit and counting tests had passed.
The workflow here retains every check and uses the 120-minute budget also
proposed separately in PR #31.

### Exact counts on the constructed finite-chain witness

`ConstructedBirthCadenceChain.sectionCovered` constructs actual complete
ERROR/MARK covers without a caller-supplied cover or gate premise.
`exact_section_counts` identifies four ERROR sections on each active port
and three MARK sections per cell, summed over ports. The original birth,
physical-box, source-budget and wire hypotheses of the factories are retained.

The application graph builds in **3,758 jobs**. The unchanged audit scanner
imports all **48 changed modules** across this PR and checks **6,553 project
theorems** in their dependency closure, permitting only `propext`,
`Classical.choice` and `Quot.sound`, with no admitted proofs or added project
axioms. These are scoped local totals, not a completed local global build.
The umbrella imports all new modules for the ordinary global CI audit.

Source hygiene passes for **565 Lean files**, with all five inherited upstream
modules unchanged. All **six paired applied controls** in
[`check_hybrid_chain_section_counts_negative.py`](../proof/lean/scripts/negative/check_hybrid_chain_section_counts_negative.py)
pass, including counts, cover uniqueness and own-birth offsets. Together with
the 11 section-run pairs, the configured CI inventory is **1,379 pairs**
(1,362 + 11 + 6), separately from audit-corruption checks. The audit's positive
public/private controls and corruption-rejection controls pass locally.

The preceding `93abed8` checkpoint also passes the global build, global audit
and audit-corruption steps in
[Actions run 42012958868](https://github.com/HevisNico/kernel-R/actions/runs/42012958868).
Its remaining regression steps were running when this entry was prepared;
its global totals are not substituted for the scoped application totals above.

### Constructive section covers: checkpoint `93abed8`

The **33 changed Lean modules** and their dependency closure build successfully
in **3,749 jobs**. The unchanged audit scanner, importing those 33 modules,
checks **6,488 project theorems**, permitting only `propext`, `Classical.choice`
and `Quot.sound`, with no admitted proofs or added project axioms. This is a
dependency-closure audit, not a new full-project declaration total; global
validation of this checkpoint is left to its GitHub Actions run.

Source hygiene for this checkpoint covers **555 Lean files**, including the
15 new modules, with all five inherited upstream modules unchanged. All
**11 new paired controls** in
[`check_hybrid_section_runs_negative.py`](../proof/lean/scripts/negative/check_hybrid_section_runs_negative.py)
pass: closed counts, open boundaries, composition, exposure, foreign events,
router copies and port relabeling. The configured CI inventory becomes
**1,373 pairs** (1,362 plus 11), separately from audit-corruption controls.

This checkpoint supplies constructive local covers and preserves actual
section runs through causal weaving, queue framing and router changes.
The complete finite-chain cover-existence corollary is still in progress;
the applied counts of four active-port ERROR sections and three MARK sections
are not claimed by this checkpoint.

### Exact dose counting: checkpoint `62376ff`

At `62376ff7dda182bd7e31463eede337fb3390828b`, the local
`lake build KernelR.HybridDoseCounting` passes **3,502 jobs**. This is the
module build, not a new full-project build total. Its six printed headline and
count-uniqueness results use only `propext`, `Classical.choice` and `Quot.sound`.
Source hygiene covers **540 Lean files**, with all five inherited upstream
modules unchanged; generated evidence matches and all **16 robust certificates**
replay.

All **11 new paired controls** in
[`check_hybrid_dose_counting_negative.py`](../proof/lean/scripts/negative/check_hybrid_dose_counting_negative.py)
pass locally and in [GitHub Actions run 41994544240](https://github.com/HevisNico/kernel-R/actions/runs/41994544240).
The configured CI inventory is **1,362 pairs** (the preceding **1,351** plus
these **11**), separately from axiom-audit corruption checks. This inventory
counts generated cases; it does not assert a fresh rerun of all historical
suites. The completed global build in that run passes **9,593 jobs** and its
axiom audit checks **29,018 project theorems**, permitting only `propext`,
`Classical.choice` and `Quot.sound`, with no admitted proofs or added project
axioms. All regression steps and all three workflows at this revision finish
successfully. These totals describe `62376ff`, not subsequent revisions.

### Geometric crossing: checkpoint `ef5a510`

The geometric-crossing checkpoint at `ef5a510` passed a completely fresh local project
build (**9,592 jobs**) and global axiom audit (**28,970 project theorems**),
allowing only `propext`, `Classical.choice` and `Quot.sound`. Source checks cover
**539 Lean files**, with all five inherited upstream modules unchanged. All
**81 paired controls** passed: 14 geometric, six scalar transversality, seven
actual-contact, 36 constructed-chain and 18 causal-weave pairs. These are local
validation results, not a claim about an unobserved GitHub workflow run or a
published release. The genuine full-cell grazing fixture in
[`scripts/fixtures/crossing_grazing.lean`](../proof/lean/scripts/fixtures/crossing_grazing.lean)
exhibits a weak/model flow excluded by native first-contact urgency outside the
physical box and protocol; it is not a counterexample to the finite-chain result.

### Universal-complete result: historical validated checkpoint

The complete frozen-source universal checkpoint passes **9,557 build jobs**
and the global axiom audit of **27,741 project theorems**. Source checks cover
**504 Lean files**, with all five inherited upstream modules unchanged.
Generated evidence matches, **16 robust certificates** replay, and **12
project tests** pass. The three public `UniversalChainHeadline` declarations,
the native universal factory and the generic complete-execution comparison
use only `propext`, `Classical.choice` and `Quot.sound`.

All **20 new universal paired controls pass**: the valid conclusions compile
first and each altered conclusion is independently rejected with a Lean
diagnostic. The confirmed finite-chain inventory is **218 passing pairs**;
CI configures **1,321 pairs**, plus axiom-audit corruption controls. These totals
do not claim a fresh rerun of every historical suite. The frozen proof tree
is `5dab922f4adb45ff42f53377dcc784b689a27d43`. Verified code commit:
`eeff210df7a2c6297d532c10203312ded3c0bbf9`. Its Lean/workflow/control sources match
the frozen export exactly; only its Markdown documentation differs. The
following documentation/formatting commit records this identifier and removes one trailing space
in the universal preparation source, without changing any Lean statement or
proof. Those published sources are now integrated without changes to the Lean
files or controls; fresh integration CI is recorded separately and is not
presumed successful.

### Prescribed-error existence: historical validated checkpoint


The earlier prescribed-error existence construction passed the complete frozen-source
export: **9,543 build jobs**, **27,587 audited project theorems**, **490 Lean
sources**, generated-evidence checks, **16 robust certificates** and **12
project tests**. All three public indexed headline theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`. No admitted proof or added
project axiom is accepted. Verified indexed code commit:
[550fc9509c8390a07fdb0cec02170a72cbc3071c](https://github.com/HevisNico/kernel-R/commit/550fc9509c8390a07fdb0cec02170a72cbc3071c).
The following documentation-only commit records this identifier; the Lean,
workflow and control-script sources are unchanged from the verified code tree.

The 20 new indexed paired controls pass, bringing the confirmed finite-chain
inventory to **198 passing pairs** and the configured CI inventory to
**1,301 paired controls**, plus axiom-audit corruption checks. These totals
do not assert a fresh local rerun of every historical suite. The indexed
controls include actual final fast sender indices, prescribed delay values
and retained whole-execution terminal/count conclusions.

### Native-function construction: historical validated checkpoint

The completed native-function construction passed the pinned complete export:
**9,537 build jobs**, **27,515 audited project theorems**, **484 Lean sources**
and five unchanged inherited modules. Generated evidence, all **16 robust
certificates** and **12 project tests** pass. The audit allows only `propext`,
`Classical.choice` and `Quot.sound`.

At that checkpoint, all **178 finite-chain paired controls passed**:48 first-checkpoint,40 preparation,
15 full-budget,19 receiver,20 port/index and36 global-construction contracts.
Each valid conclusion compiles before its altered conclusion is individually
rejected with a Lean diagnostic. CI configured **1,281 paired controls**, plus
axiom-audit corruption checks; this inventory does not claim a fresh local
rerun of every historical suite. Verified code commit:
[2c50e42e4ba02bd77c20dfd2612a587dfda4c224](https://github.com/HevisNico/kernel-R/commit/2c50e42e4ba02bd77c20dfd2612a587dfda4c224).
A following documentation-only commit records that identifier; proof sources
are unchanged. Fresh CI status is recorded in PR #15; in-progress CI is not
labeled green.

That checkpoint's [native finite-chain headline](../proof/lean/KernelR/FiniteChainHeadline.lean) groups
existence from independent births, terminal memories/state and actual counts.
Its three `#print axioms` outputs contain exactly the three permitted logical
axioms. The [native headline source](../proof/lean/KernelR/FiniteChainHeadline.lean) retains those exact signatures.

### First exported checkpoint: historical validated baseline

Commit `21cf9821af0f90ada4301b9791ed8492f936d934` published the first13 modules.
Its complete exported-tree build passed **9,502 jobs**, its global audit
passed **26,659 project theorems**, and source checks covered **449 Lean
files**, with five inherited modules unchanged. Generated evidence, all
**16 robust certificates**, **12 project tests** and **48 new paired
controls** passed. CI configured **1,151 paired controls**, plus axiom-audit
corruption checks; that inventory does not claim a fresh local rerun of every
historical suite. These figures describe that commit, before the completed
common-birth construction.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the audit.
Each exported checkpoint must record exact build/audit results and its remaining
quantified premises. The N=3 baseline remains separately completed. A pause
stops new work; the branch, validated commits and this ledger provide the
restart point. No push, PR publication or merge is performed without the user’s
explicit instruction. The [historical PR description](../archive/plans/UNIVERSAL_EXECUTION_PR.md)
records the reviewed universal proof change; the current
[release checklist](RELEASE_V0_2_0.md) does not
authorize an automatic merge or release publication.

## Recovery-limited firing rate local validation

Code checkpoint: `b33af69356790f3ab45fd8dc4ee675c721221e3a`, based on main
`0f39642`. The new native and direct weak/crossing proof modules are
[HybridResetRate](../proof/lean/KernelR/HybridResetRate.lean) and
[HybridResetRateCrossing](../proof/lean/KernelR/HybridResetRateCrossing.lean). They establish
actual FIRE gaps and finite-window count bounds for arbitrary finite networks
under a pathwise recovery envelope, with a uniform specialization from the
initial built-in recovery cap. No protocol or completion premise is imposed.

Local validation on 6 November 2026:

- Full default `lake build`: passed, 9,626 jobs including cached dependencies.
- The unchanged global `Audit` target passed for 29,405 imported project
  theorem declarations, allowing only `propext`, `Classical.choice` and
  `Quot.sound`. New modules are included through the umbrella import.
- `python -m scripts.negative.check_hybrid_reset_rate_negative`: ten paired controls
  passed; valid contracts compile and mutated contracts fail with type errors.
- Source hygiene and five inherited-source identities passed; the unchanged
  base byte checks retain the same base and permit only named added modules.
- Generated numerical evidence freshness, sixteen robust certificate replays
  and all three project-layout tests passed.
- A fresh Lean metadata export retained the same 84 trusted semantic
  declarations. The source-hash record and reading list were regenerated for
  the code checkpoint; the authenticated document check passed.

The dependency caches were reused. These are local checks, not a fresh
external-dependency rebuild or the entire CI workflow. The new paired suite
is included in CI; the unchanged historical negative suites retain their
existing CI stages. See [scope](RESET_RATE_SATURATION.md).

## Native package audit (v0.4.0)

Release commit: `5d47261412a582f6b96ec139b67e406884d406cc` (tag `v0.4.0`).
The sources of `research/recursive-learning/native/` are identical at
`8e63786`, the main commit that precedes the release merge; the release merge
changes only documentation and metadata.

The "Recursive learning Lean proofs" workflow on `8e63786`
(run [43102068383](https://github.com/HevisNico/kernel-R/actions/runs/43102068383))
built the native package with Lean 4.35.0 and Mathlib v4.35.0. Its
`NativeAudit` target reports:

> RecursiveLearning audit passed for 5741 declarations, including 3525 theorems.

The audit covers every imported declaration whose name lies in the
`RecursiveLearning` namespace, private and generated declarations included
(equation lemmas, `match` and proof helpers), plus two named
`KernelR.Hybrid` declarations defined in the package. Each depends only on
`propext`, `Classical.choice` and `Quot.sound`. The native sources state 943
`theorem` or `lemma` declarations directly; the rest of the count is
generated declarations and the parent `recursive-learning` package.

The kernel definitions in `proof/lean` are unchanged by this release, and
its trusted-base record is not regenerated. The "Kernel R Lean proofs" run
on the release commit
([43114103132](https://github.com/HevisNico/kernel-R/actions/runs/43114103132))
passed.
