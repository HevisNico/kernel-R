# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)
**Archived release v0.2.0 — DOI:** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

## Why it matters

Kernel R makes learning exactly predictable in a model of asynchronous cells
with fabrication mismatch. In every complete run of the declared protocol,
each cell's memory increments are the same across the allowed fabrication
parameters, wire delays and legal orders of simultaneous events. Lean proves
this from the cell's differential equations for chains of any finite length.

During a full learning phase, the cell integrates a sensor's discharge between
fixed charge thresholds. The fabrication rate cancels from the dose.

- A complete ERROR phase adds `Δz = 8 × (0.1 − 0.025) = 0.6` to the port's
  log-gain when the cell stays READY.
- A complete MARK phase adds `Δb = (1 − 0.8) / 2 = 0.1` to the cell's
  recovery rate when the cell stays protected.

These exact increments require positive energy and an open cap gate for the
relevant memory throughout the phase. No external controller computes the
learning updates. Under the declared protocol, a chain with independent
fabrication variation of up to ±10% and bounded wire jitter ends with the same
memory increments for every allowed choice of parameters and delays. Its
output rhythm has bounded timing error.

> **Scope of the robustness.** Each port's gain cap, sensor rates and sensor
> input gain (`C, L_m, L_s, L_e, M`) may vary across cells and ports, with
> values fixed in time. Thresholds and actuation factors are exact.

## An R cell in one picture

```mermaid
stateDiagram-v2
    direction LR
    READY --> FAST: q crosses 1 upward
    FAST --> SLOW: q reaches 1/4 after one time unit
    SLOW --> READY: q reaches 0.1
    note right of READY
      admits input pulses
      ERROR sensor phases raise input gains here
    end note
    note right of SLOW
      protected: admission closed
      MARK sensor phases raise recovery b here
    end note
```

The cell emits one pulse during FAST and keeps input admission closed in
FAST and SLOW. Each of its three input ports has a sensor that sees raw pulses
even during protection and cycles through READY → MARK → SILENT → ERROR → READY.
The log-gain `z` can change while the main cell is READY. The recovery rate
`b`, which governs SLOW decay, can change while the main cell is protected.
See the [cell laws](model/CELL.md) and [glossary](docs/GLOSSARY.md).

## The main result

**In plain words.** Take a chain of any positive finite length. Choose its
fabrication parameters independently within the ±10% or ±0.3% box and start
every cell in READY, near its nominal resting values. Send each cell a
preparation train, then drive the leaf with a regular rhythm. Each link
delivers pulses with a delay in `[0.3, 0.4]`. The delay functions are fixed
in advance and may vary over time, with summed jitter budgets at most 0.15.
With these inputs fixed, the theorem gives the following guarantees.

- **A complete run exists** in the model's upward-crossing semantics.
- **Every complete run agrees** on the physical endpoint and each cell's
  ordered firing dates, regardless of the legal order of simultaneous events.
- **Each cell learns exactly.** Its active input log-gain ends at its birth
  value + 2.4, and its recovery rate ends at its birth value + 0.3.
- **The rhythm crosses the chain.** The root's output ends with at least eight
  pulses at dates `τ + 4k + η_k`, with `|η_k| ≤ 0.15`.
- **The chain ends READY.** At the horizon every main unit and sensor is READY,
  each main charge is 0.1, and no pulse current or delivery remains.

**Formally.** The Lean statement is
[`TrustedHeadline.every_finite_chain`](proof/lean/KernelR/TrustedHeadline.lean),
whose meaning is fixed by a machine-checked list of definitions, the
[trusted base](docs/TRUSTED_BASE.md).

> For every positive finite chain length N, every admissible source length K,
> all independent fixed fabrication parameters and READY birth data, and every
> admissible family of bounded wire-delay functions fixed in advance, the
> fixed chain router admits a complete physical execution in both semantics.
> Every finite execution in either semantics, from the same birth data and
> complete through the same horizon under that router, has the same physical
> endpoint and the same ordered firing dates in every cell.

The [finite-chain specification](model/CHAIN_PROTOCOL.md) gives the exact
birth bounds, source length `K ≥ 4N + 12`, and delay assumptions. The
[theorem guide](docs/UNIVERSAL_FINITE_CHAIN.md#result-every-finite-chain-with-explicit-scope)
gives the detailed outcomes.

The result holds both in the model's upward-crossing semantics and in Lean's
native first-contact semantics, with the
[correspondence between them](docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
proved for this protocol. A corollary realizes any prescribed sequence of
bounded per-pulse wire errors on the actual sending firings.

## What is not claimed

- **Only complete executions.** The theorem compares executions complete
  through the horizon. Separate [progress theorems](proof/lean/PROGRESS.md)
  extend every legal finite prefix of this protocol to later horizons and prove
  time divergence for infinite native runs maximal under extension at a finite
  flow limit.
- **Learning and cadence only for this protocol.** Cyclic networks, noise or
  drift during operation, and other protocols have their own
  [coverage boundaries](proof/lean/N_CELL_COVERAGE.md).
- **Dose counts on the constructed run only.** The
  [counting theorem](docs/EXACT_DOSE_COUNTING.md) gives four ERROR phases on
  the active port and three MARK phases across each cell's ports in the
  constructed execution. The universal comparison transfers the resulting
  memory increments to every complete execution.
- **Thresholds held exact.** See the scope note above.
- **A model, not a device.** Formal verification does not experimentally
  validate any hardware.
- **The Reset Operator argument is separate.** Its broader saturation claim
  is not part of these theorems.

## Other proved results

| Result | Scope | Statement |
|---|---|---|
| **Event order does not matter.** Executions complete through the same horizon agree on the physical endpoint up to pending-list order, and on each cell's ordered firing dates. | Native semantics for any finite network, including cycles, with the same parameters, initial snapshot and fixed router, under the physical bounds. | [endpoint](proof/lean/KernelR/HybridUniversalExecution.lean#L21-L29) · [dates](proof/lean/KernelR/HybridUniversalExecution.lean#L31-L43) |
| **Recovery limits the output rate.** If recovery stays at most `β > 0`, two firings of a cell are at least `1 + log(5/2)/β` apart (about 1.833 at the built-in cap). A window of length L contains at most `1 + L/(1 + log(5/2)/β)` firings. | Any topology, both semantics. | [guide](docs/RESET_RATE_SATURATION.md) · [Lean](proof/lean/KernelR/HybridResetRateCrossing.lean) |
| **Zero recovery can lock a cell.** A cell starting in SLOW with charge 1/4 and zero recovery cannot fire again while no sensor spends positive time in MARK. An isolated, fully exposed MARK phase can restore recovery to 0.1. | Any finite network and router. Lock in both semantics, conditional repair in native semantics. | [guide](docs/RESET_ZERO_RECOVERY.md) |

## How to check it

The project pins **Lean 4.35.0** and **Mathlib v4.35.0** ([lake-manifest.json](proof/lean/lake-manifest.json)).

```sh
cd proof/lean
lake exe cache get
lake build
lake build Audit
```

The audit checks every project theorem and allows only `propext`,
`Classical.choice` and `Quot.sound`. The source checks reject `sorry`, added
axiom declarations and `native_decide`. See the
[recorded full validation](docs/VALIDATION_LEDGER.md#full-lean-validation-at-0543640),
[exact signatures and axiom outputs](docs/UNIVERSAL_FINITE_CHAIN.md#lean-headline-signatures-axioms-and-reproduction), and
[fresh-checkout rebuild instructions](proof/lean/README.md#rebuild-project-proofs-without-a-restored-project-cache).

## For reviewers

Lean checks every proof. Human review starts with whether `CrossingExecution`
faithfully represents the written model. See the [reading path](REVIEW.md).

## Repository map

| Folder | Contents |
|---|---|
| [`model/`](model/README.md) | Cell laws and the finite-chain protocol |
| [`proof/lean/`](proof/lean/README.md) | The verified Lean development, audit and regression controls |
| [`docs/`](docs/UNIVERSAL_FINITE_CHAIN.md) | Theorem guides, model ↔ Lean correspondence, provenance, glossary |
| [`research/`](research/README.md) | Robustness and reset-window research modules |
| [`archive/`](archive/README.md) | Earlier experiments, certificates and specifications |

Further: [proof construction](docs/FINITE_CHAIN_CONSTRUCTION.md) ·
[explicit router](proof/lean/KernelR/ExplicitFiniteChainRouter.lean) ·
[experiments and certificate replay](docs/EXPERIMENTS_AND_REPRODUCTION.md) ·
[provenance](docs/PROVENANCE.md) · [release checklist](docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md)

## Origin, AI assistance and license

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).

It is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT**
(OpenAI), under the direction of Nicolas Breuillaud. AI assists the
construction of models, code, proofs and documentation. Lean checks the
resulting proof terms against their definitions and hypotheses.
That check does not experimentally validate the physical assumptions or
establish every claim made in the repository.

Source code is [MIT](LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
