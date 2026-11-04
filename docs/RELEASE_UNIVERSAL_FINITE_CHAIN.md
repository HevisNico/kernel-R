# Universal finite-chain release preparation

**Historical v0.2.0 release preparation.** The checklist and draft text below
retain their original release scope and validation counts. They are not the
publication instructions for the later geometric-crossing development; see the
[current proof ledger](../proof/lean/EVERY_N_PLAN.md#geometric-crossings-and-finite-prefix-progress).

This is a publication checklist and draft release text. It does not create a
tag or publish a release. The proposed next version is **v0.2.0**; the existing
`v0.1.0` remains the earlier robust N-cell composition checkpoint and does not
contain the universal complete-execution modules.

## Before publishing

1. Merge the universal-proof integration PR into `main` after its Lean,
   research and robust-evidence workflows pass on the final PR revision.
2. Check the three workflows on the resulting `main` commit as well. Record
   that exact commit as the release target; do not use a moving branch as the
   reproducibility identifier.
3. Check that the target contains
   `proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean`,
   `proof/lean/KernelR/UniversalChainHeadline.lean` and the universal paired
   controls in `proof/lean/scripts/check_hybrid_universal_execution_negative.py`.
4. Create the new release as a draft against that exact commit and use the
   text below. Review the tag target before publishing. GitHub's source
   archives must include the proof project and its pinned Lake manifest.
   Do not reuse the `v0.1.0` reproducibility ZIP as the new proof artifact.
5. If attaching additional archives or a PDF, record their source commit
   and SHA-256 checksums. Keep the frozen audit counts below attached to
   their original checkpoint unless a fresh audit supplies new counts.

## Draft release text

### Kernel R v0.2.0 - Universal finite-chain physical executions

For every positive finite chain length, admissible source length, independent
fixed fabrication parameters and READY births, and every admissible bounded
native wire-delay family fixed in advance, the declared R protocol has a
complete physical execution. Every finite execution of that same fixed
protocol, complete through its declared horizon, has the same physical
endpoint and ordered firing dates per cell.

The endpoint retains each cell's own learned active log-gain increment of
2.4 and recovery increment of 0.3. All cells and auxiliaries are READY,
with q=0.1, no RAW current and an empty pending queue. Exact firing counts
and a root cadence tail of at least eight pulses are derived from actual
physical trajectories. The tail has nominal period four and phase error
bounded by the cumulative wire-jitter budget, at most 0.15.

A separate indexed-error corollary constructs fixed native delay functions
realizing every prescribed bounded error sequence on actual fast sender
firings. Its delay functions are constructed from the prescribed data;
the native-delay theorem above accepts delay functions fixed in advance.

The release includes the physical uniqueness and confluence proofs, the
finite-chain universal declarations and paired corruption controls. The
Lean project pins Lean 4.35.0 and Mathlib v4.35.0. The frozen proof checkpoint
`eeff210df7a2c6297d532c10203312ded3c0bbf9` passed 9,557 build jobs and an
audit of 27,741 project theorems using only `propext`, `Classical.choice`
and `Quot.sound`. Its published follow-up
`f032e7f4dd07485945459236bd89e72748d6aec7` passed all three workflows.
These are historical checkpoint figures; the release target and its own
workflow checks must be recorded with the release.

The result concerns complete finite executions under the declared birth,
source, fabrication and delay hypotheses. It does not prove progress of
every stopped prefix, infinite-run existence, non-Zeno continuation or the
broader structural argument about saturation.

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

AI assists construction of models, code, proofs and documentation. Lean checks
the resulting proof terms against their definitions and hypotheses. That check
does not experimentally validate the physical assumptions or establish every
claim made in the repository.

## Reproduce the selected release commit

After checking out the exact release commit, from the repository root:

```sh
git rev-parse HEAD
python -B -m unittest discover -s tests
cd proof/lean
python scripts/check_sources.py
python scripts/generate_evidence.py --check
python scripts/robust_evidence.py --check
lake exe cache get
lake build KernelR.HybridUniversalBirthCadenceChain KernelR.UniversalChainHeadline
lake build
lake build Audit
python scripts/check_hybrid_universal_execution_negative.py
```

The [Lean workflow](../.github/workflows/lean.yml) runs the full configured
negative-control inventory as well. The root [README](../README.md) provides
the exact quantifiers, cadence formula, source links and axiom profiles.
