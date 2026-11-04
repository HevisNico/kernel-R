# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)

**Archived release v0.2.0 — DOI:** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

**R cells learn through pulses and transmit a cadence along every finite
directed chain, under the declared protocol. Lean verifies the physical
construction and complete-execution guarantees, with a proved geometric
upward-crossing correspondence for the finite-chain protocol.**

Each cell has two memories with complementary gates: input sensitivity
(gain) and recovery. The protocol changes both through the cell's own
dynamics, then transmits a cadence through the chain.

Three entry points:

1. [Detailed result, hypotheses and verification](docs/UNIVERSAL_FINITE_CHAIN.md).
2. [Geometric upward-crossing theorem](proof/lean/KernelR/CrossingChainHeadline.lean),
   `CrossingChainHeadline.every_finite_chain_every_crossing_execution`, followed
   by the [native first-contact construction](proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean)
   and [native indexed-error theorem](proof/lean/KernelR/UniversalChainHeadline.lean)
   used in its proof.
3. [Model ↔ Lean: equations and operational semantics](docs/MODEL_LEAN_CORRESPONDENCE.md).

For review, start with the [semantic review guide](REVIEW.md): fidelity of
`CrossingExecution` to the written model is the first human review obligation.

## Result: every finite chain, with explicit scope

> For every positive finite N, admissible source length K, independent fixed
> fabrication parameters and READY birth data, and every admissible family of
> bounded native wire-delay functions fixed in advance, the declared fixed
> chain router admits a complete physical execution in both semantics. Every
> finite execution in the model's upward-crossing semantics (and in the native
> first-contact semantics), from those same birth data and complete through
> the same horizon under that fixed router, has the same physical endpoint
> and ordered FIRE dates per cell.

The construction starts with all cells born at time zero and retains actual
continuous trajectories, pulse origins, deliveries and memory updates.
It derives:

- Each active log-gain is its own birth value +2.4; each recovery is its own
  birth value +0.3. Other gains retain their physical preparation memories.
- The root has a regular tail of `K-4*N-4 >= 8` pulses, with actual dates
  `t_k = τ + 4*k + η_k`, where `|η_k| <= J <= 0.15`. Successive intervals
  therefore lie in `[4-2*J, 4+2*J]`.
- At `T = 160 + 4*(K-1) + (11/10)*(N-1) + 8`, all cells and auxiliaries are
  READY, q=0.1, RAW currents have ended and the global queue is empty.

A separate indexed-error corollary constructs fixed native delay functions
realizing every prescribed bounded per-emission error sequence on actual
FAST sender firings. Its functions are constructed after the errors are given;
the native-delay theorem above takes the functions as inputs.

## Hypotheses

- `N >= 1`, `K >= 4*N+12`; the declared independent READY birth family.
- Fifteen fabrication parameters per cell, independently chosen in either
  the ±0.3% or ±10% box and fixed in time.
- Canonical width-one exponential pulses. Each cell receives sixteen
  period-eight preparation inputs; the leaf receives K period-four inputs
  from time 160. These sources are present in the birth queue.
- One fixed directed-chain router, closed during preparation and open on
  `[160,T+1)`. Each non-root FIRE issues exactly one token to its parent on
  port 2 at `F+δ_j(F)`; the root has no outgoing link.
- Fixed admissible delay functions, with delays in `[0.3,0.4]` and summed
  nonnegative jitter budgets `J <= 0.15`. The source length and path budget
  must remain admissible as N grows.

[Exact birth, parameter, delay and source hypotheses](docs/UNIVERSAL_FINITE_CHAIN.md#result-every-finite-chain-with-explicit-scope).

## Limits

The native event guards use first threshold contact. A separate geometric
semantics requires an actual approach from below and an incoming-mode ODE
continuation above the threshold. Their correspondence is proved for the
constructed finite-chain protocol, including every complete competing model
execution, without adding protocol hypotheses. See the
[threshold correspondence](docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings).

The model comparison covers finite crossing executions satisfying
`CrossingCompleteThrough model T`. The native proof uses `CompleteThrough e T`.
Both reach T, resolve the terminal jumps enabled by their respective semantics
and leave no token due by T pending. Constructed witnesses supply both classes.
Global simultaneous-event order and flow subdivisions may differ. For the same fixed program, the
[progress theorems](proof/lean/PROGRESS.md) extend legal finite prefixes to
later horizons and prove time divergence for infinite presentations maximal
under extension at a flow limit. Physical jumps cannot accumulate in bounded
time under the event-budget hypotheses.

The theorem covers the declared finite directed-chain protocol. General cyclic
networks, operational noise/drift, retained probes and settings-copy variants
have their own coverage boundaries. Formal verification of the model does not
experimentally validate a physical device. See the [coverage map](proof/lean/N_CELL_COVERAGE.md).

## Lean headline: signatures, axioms and reproduction

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**; dependency commits are
recorded in [lake-manifest.json](proof/lean/lake-manifest.json).
From the repository root, with Lean installed:

```sh
git rev-parse HEAD
cd proof/lean
lake exe cache get
lake build KernelR.CrossingChainHeadline
lake build
lake build Audit
```

For the current geometric-crossing revision, the
[validation ledger](proof/lean/EVERY_N_PLAN.md#validation-and-checkpoint-discipline)
records a fresh local build of **9,592 jobs** and a global audit of
**28,970 project theorem declarations**, permitting only `propext`,
`Classical.choice` and `Quot.sound`, with no admitted proofs or added project
axioms. These are recorded local validation results. The archived v0.2.0
universal proof checkpoint recorded **9,557 jobs** and **27,741 declarations**.

[Exact Lean signatures, axiom outputs and checkpoint evidence](docs/UNIVERSAL_FINITE_CHAIN.md#lean-headline-signatures-axioms-and-reproduction) ·
[Fresh-checkout rebuild and full controls](proof/lean/README.md#rebuild-project-proofs-without-a-restored-project-cache).

## Model ↔ Lean: equations, events and assumptions

The [correspondence page](docs/MODEL_LEAN_CORRESPONDENCE.md) links charge,
auxiliaries, gain/recovery, energy, gates, thresholds, jumps and births to
their Lean definitions. The [cell guide](kernel/README.md) states the equations.

## Supporting work and provenance

[Experiments, historical results, certificate replay and viewer QA](docs/EXPERIMENTS_AND_REPRODUCTION.md) ·
[Dated provenance and scope](docs/PROVENANCE.md) ·
[Release checklist](docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md).

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
Its broader argument about saturation when recovery cannot keep pace with
forcing remains separate from the R protocol theorem.

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

AI assists construction of models, code, proofs and documentation. Lean checks
the resulting proof terms against their definitions and hypotheses. That check
does not experimentally validate the physical assumptions or establish every
claim made in the repository.

Source code is [MIT](LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).

