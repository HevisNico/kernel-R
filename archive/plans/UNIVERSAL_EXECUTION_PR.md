# Prove every complete finite execution of the physical finite-chain program

Historical description of [PR #17](https://github.com/HevisNico/kernel-R/pull/17),
which was merged into `proof/physical-finite-chain`. The publication and base
status below describe that review checkpoint. The proof modules are included
in this checkout. The [release checklist](../../docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md)
retains the historical v0.2.0 publication scope; later developments and local
validation are in the [current ledger](../../docs/VALIDATION_LEDGER.md).

Draft PR, published for review by explicit user instruction.
Branch: `proof/universal-execution`; review base:
`proof/physical-finite-chain` at `46c5672e0a5909d153c8130102cff5f25f276487`
(the proof head of #15). Main has the separate README-only #16 merge
`4e914909be0b2bb4bae1a71e8146351d8896115b`; this draft does not merge #15.

The previous theorem constructed one physical execution for each admissible
input/error family. This change proves that **every finite operational
execution from the same initial state under the same fixed router, complete
through the declared terminal T**, has the same physical endpoint and exact
ordered per-cell FIRE dates. It transfers the finite-chain terminal memories,
traffic counts and prescribed per-emission errors to those executions.

## Exact quantifier and result

For every positive finite N, admissible K, independent fixed fabrication and
READY birth data, and bounded prescribed wire-error family, there exist fixed
native delay functions and an actual complete physical witness, such that
every finite execution of that same birth program/router complete at T has:

| Actual observation | Proved conclusion |
|---|---|
| Terminal time | `T=160+4*(K-1)+(11/10)*(N-1)+8` |
| State | All READY/q=0.1, no RAW, empty pending queue |
| Active log-gain | Each cell's own birth value+2.4; leaf port0, relays port2 |
| Recovery | Each cell's own birth value+0.3 |
| FAST emissions at leaf-to-root depth j | `K-5-2*j` |
| Cumulative per-cell emissions | Its actual12/14 preparation count plus its FAST count |
| Entire birth-to-T emission ledger | `N*(K-N+8)+2` |
| Indexed error at actual kth FAST sender FIRE | `delay j F_jk=centre j+error j k` |

The existing birth/source, fabrication and jitter hypotheses are retained:
all cells independently born at0, 16 preparation inputs per cell, K period-four
leaf sources from160 already in the birth queue, `K≥4N+12`, fixed independent
±0.3%/±10% fabrication parameters, link centres within `[0.3+σ,0.4−σ]`, and
summed nonnegative error budgets≤0.15. The new native universal factory also
accepts arbitrary supplied fixed native delay functions satisfying those bounds.

No desired endpoint, event calendar, prepared state, local `CellLaw`, event
priority or uniqueness property is inserted as a caller premise. Existence is
retained, so the universal assertion is nonvacuous.

The global README also clarifies the paper attribution: its structural argument
concerns saturation when recovery can no longer keep pace with forcing.
The Lean theorem verifies the declared R protocol under its own parameter/input
hypotheses; it does not itself prove that broader saturation argument. The
existing AI attribution and explanatory paragraph are preserved verbatim.

## Why the universal result is now proved

- Physical integral-flow uniqueness compares the actual coordinates on common
  intervals, including actuator caps, positive reserve gates and energy.
- Legal instantaneous jumps have proved observational local diamonds. Initial
  enabled jumps can be stripped through a competing complete finite trace.
- Strong induction on the combined finite move count aligns positive flows,
  transports queue permutations and compares jumps without fixing their order.
- Generic complete-execution comparison yields equal endpoint time, physical
  coordinates, modes and RAW state, pending queues up to permutation, the
  global FIRE multiset, and **exact ordered per-cell FIRE lists**.
- The existing constructed finite-chain witness supplies the reference outcome.
  At every competing trace, FAST dates are its own full per-cell list after
  dropping the physically proved preparation count: 14 at the leaf, 12 at each
  relay. Prescribed-error indices apply to this actual suffix.
- Independent source-based universal preparation lemmas also derive each
  relay/leaf preparation through actual128 prefixes, retaining arbitrary
  interleavings of other cells and the leaf's future sources.

Review entry points: [public headline](../../proof/lean/KernelR/UniversalChainHeadline.lean),
[generic complete-execution comparison](../../proof/lean/KernelR/HybridUniversalExecution.lean),
and [finite-chain transfer](../../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean).

## Validation

The generic comparison, native universal factory and all three public headline
statements pass their local builds. Their axiom profiles contain only
`propext`, `Classical.choice` and `Quot.sound`. All **20 new universal paired
controls pass**: valid statements compile, and each altered conclusion is
independently rejected with a Lean diagnostic.

The complete frozen-source build passes **9,557 jobs**, and the global audit
passes **27,741 project theorems**, permitting only the three standard logical
axioms. Source checks cover **504 Lean files** with five upstream modules
unchanged. Generated evidence, **16 robust certificates**, **12 project tests**
and **20 new paired controls** pass. The confirmed finite-chain inventory is
**218 pairs**; CI configures **1,321 pairs**, plus axiom-audit corruption checks.
This inventory does not claim a fresh local rerun of every historical suite.

The [validation ledger](../../docs/VALIDATION_LEDGER.md#validation-and-checkpoint-discipline)
records the frozen proof tree and verified code commit
`eeff210df7a2c6297d532c10203312ded3c0bbf9`. A subsequent documentation/formatting commit records the
identifier and removes one trailing source-space, with no proof change.
Fresh CI status is recorded separately; no pending run is called successful. The indexed-existence figures
9,543 /27,587 /490 /198 /1,301 remain a historical checkpoint.

Reproduction from `proof/lean`:

```sh
lake build KernelR.UniversalChainHeadline
lake build
lake build Audit
python3 scripts/check_sources.py
python3 -m scripts.evidence.generate_evidence --check
python3 -m scripts.evidence.robust_evidence --check
python3 -m scripts.negative.check_hybrid_universal_execution_negative
```

## Scope

`CompleteThrough e T` means a supplied finite execution reaches T, has no
terminal enabled jump and leaves no token due by T pending. Stopped prefixes
and infinite/maximal runs are not silently included in this quantifier. This
comparison does not itself establish progress, infinite-run existence or a
new non-Zeno theorem. It does not make trace syntax, flow subdivision or the
ordering of simultaneous independent global events unique.

The indexed order remains **∀ admissible data/errors ∃ fixed native functions
and witness ∀ complete finite executions under that router**. It does not
assert one router uniform across different birth/error families, an online
synthesis algorithm or that every arbitrary router realizes prescribed errors.
Retained frozen probes, cuts/settings copies, operational drift/noise/amplitude
histories and the full written theorem retain their separate obligations.

Publication remains subject to the user's explicit green light. This file is
a prepared description, not an opened pull request or an authorization to push.
