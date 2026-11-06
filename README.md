# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)

**Archived release v0.2.0 — DOI:** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

## In short

An R cell is a simple model of a pulse-driven unit, loosely inspired by
neurons. It charges when pulses arrive, fires when it reaches a threshold,
then goes through a protected recovery phase before it can fire again. It
learns by adjusting two memories: how sensitive it is to each input, and how
fast it recovers. Each memory can only change in its own phase: sensitivity
while the cell is ready to fire, recovery while it is protected.

We prove that a chain of R cells of any finite length, with independent fixed
fabrication variations of up to ±10% and bounded wire delays, ends with exactly
specified memory changes and passes on a rhythm with bounded timing variation.
The guarantee covers every run of the declared protocol that is complete
through its horizon, not only simulated ones, and every step of the proof is
checked by the Lean proof assistant. Different parameter and delay choices can
produce different firing dates; the exact equality of dates compares runs with
the same parameters, birth data and router.

A [separate general result](#beyond-chains-event-order-does-not-change-the-result)
also shows that simultaneous-event order cannot change complete runs' physical
endpoints or firing dates, beyond chain networks.

## The theorem

Lean statement: [`TrustedHeadline.every_finite_chain`](proof/lean/KernelR/TrustedHeadline.lean).
Its meaning is fixed by an explicit, machine-checked list of definitions:
the [trusted base](docs/TRUSTED_BASE.md).

> For every positive finite chain length N, every admissible source length K,
> all independent fixed fabrication parameters and READY birth data, and every
> admissible family of bounded wire-delay functions fixed in advance, the
> fixed chain router admits a complete physical execution in both semantics.
> Every finite execution in either semantics, from the same birth data and
> complete through the same horizon under that router, has the same physical
> endpoint and the same ordered firing dates in every cell.

The theorem holds in the model's own semantics, where a cell fires on an
actual upward crossing of its threshold, as well as in the native first-contact
semantics. The construction starts with all cells born at time zero and keeps
the actual continuous trajectories, pulse origins, deliveries and memory
updates.

## What it guarantees

For every complete execution under the theorem's hypotheses:

- **Learned memories.** Each cell's active input log-gain ends at its own
  birth value + 2.4, and its recovery rate at its own birth value + 0.3.
  Other gains keep their preparation memories.
- **Transmitted cadence.** The root's output ends with a regular tail of
  `K - 4N - 4 >= 8` pulses at dates `t_k = τ + 4k + η_k`, with
  `|η_k| <= J <= 0.15`, so successive intervals lie in `[4 - 2J, 4 + 2J]`.
- **Clean final state.** At `T = 160 + 4(K-1) + (11/10)(N-1) + 8`, every cell
  and sensor is READY, each cell's charge is 0.1, no pulse current remains and
  no delivery is pending.

A corollary also realizes any prescribed sequence of bounded per-pulse wire
errors on the actual sending firings, with delay functions built after the
errors are given.

## Hypotheses

- `N >= 1` and `K >= 4N + 12`.
- Fifteen fabrication parameters per cell, chosen independently in the ±0.3%
  or ±10% box and fixed in time.
- Independent READY births at time zero: charges and memories within 10⁻⁵
  of their declared values, initial energy in `[50,100]`, and no active pulse
  currents.
- Canonical width-one exponential pulses. Each cell receives sixteen
  period-eight preparation inputs; the leaf then receives K period-four
  inputs from time 160. All sources are in the birth queue.
- One fixed directed-chain router, closed during preparation and open on
  `[160, T+1)`. Each non-root firing at date F sends one pulse to its parent
  on port 2 at `F + δ_j(F)`; the root has no outgoing link.
- Delay functions fixed in advance, with delays in `[0.3, 0.4]` and summed
  jitter budgets `J <= 0.15`.

Exact statements: [birth, parameter, delay and source hypotheses](docs/UNIVERSAL_FINITE_CHAIN.md#result-every-finite-chain-with-explicit-scope).

## Beyond chains: event order does not change the result

Lean also proves a general result for R's first-contact operational rules.
For any finite number of cells, any fixed routing rule (including cycles),
any finite input queue and any initial state within the
[declared physical bounds](proof/lean/KernelR/HybridPhysicalInvariant.lean#L7-L11),
two finite executions complete through the same time have the same physical
state and exactly the same ordered firing dates in each cell. The compared
runs share the same fixed parameters, initial state and routing rule.
Parameters must satisfy the [declared fabrication bounds](proof/lean/KernelR/Hybrid.lean#L96-L103).

Simultaneous events can be processed in different legal orders, and continuous
motion can be divided into different steps. Neither changes these results.
Only the list order of pending deliveries may differ.

Here, [complete](proof/lean/KernelR/Hybrid.lean#L192-L193) means that the common
final time has been reached, no event remains enabled and no delivery due by
that time remains pending.

This proves uniqueness when complete executions exist; it does not establish
existence or indefinite progress for every network. The correspondence with
the written model's upward-crossing rule is proved for the finite-chain
protocol, not for arbitrary cyclic networks.

Lean proofs: [same physical endpoint](proof/lean/KernelR/HybridUniversalExecution.lean#L21-L29)
and [same firing dates](proof/lean/KernelR/HybridUniversalExecution.lean#L31-L43).
See also the [threshold correspondence](docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings).

## What is not claimed

- **Only complete executions.** The theorem compares executions complete
  through the horizon T. For this same fixed finite-chain protocol, separate
  [progress theorems](proof/lean/PROGRESS.md) extend every legal finite prefix
  to later horizons. They also prove time divergence for infinite native runs
  maximal under extension through a finite flow limit. An infinite list of
  flow subdivisions alone need not have divergent time.
- **Learning and cadence only for this protocol.** Those guarantees cover
  finite directed chains with the declared inputs. Cyclic networks, noise or
  drift during operation, and other protocol variants have their own
  [coverage boundaries](proof/lean/N_CELL_COVERAGE.md).
- **Learning-phase counts on the constructed run only.** On the constructed
  execution, the memory changes come from exactly four complete ERROR phases
  on the active port and three protected MARK phases summed over each cell's ports
  ([counting theorem](docs/EXACT_DOSE_COUNTING.md)). The theorem transfers
  the resulting memories to every complete execution, not these counts.
- **A model, not a device.** Formal verification of the model does not
  experimentally validate any physical hardware.
- **The Reset Operator argument is separate.** The broader claim about
  saturation when recovery cannot keep pace with forcing is not part of this
  theorem.

## How to check it

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**; dependency commits
are recorded in [lake-manifest.json](proof/lean/lake-manifest.json). From the
repository root:

```sh
git rev-parse HEAD
cd proof/lean
lake exe cache get
lake build KernelR.FixedDelayChainHeadline KernelR.CrossingChainHeadline
lake build
lake build Audit
```

Latest recorded full validation: revision `05436400704dc7fc2126d12d38e93d899300363b`,
[CI run 42212189044](https://github.com/HevisNico/kernel-R/actions/runs/42212189044).
The complete Lean workflow passed, including the build, global axiom audit,
trusted-base checks and regression controls. Its final report records
**9,624 build jobs** (a cached replay of all default targets, including
dependencies) and **29,330 project theorem declarations** audited, permitting
only `propext`, `Classical.choice` and `Quot.sound`, with no admitted proofs
or added project axioms. These measurements describe that revision. The run's
`trusted-base-validation-05436400704dc7fc2126d12d38e93d899300363b` artifact
contains the report and captured build/audit logs. Historical checkpoints
remain in the [validation ledger](proof/lean/EVERY_N_PLAN.md#validation-and-checkpoint-discipline).

[Exact Lean signatures and axiom outputs](docs/UNIVERSAL_FINITE_CHAIN.md#lean-headline-signatures-axioms-and-reproduction) ·
[Fresh-checkout rebuild](proof/lean/README.md#rebuild-project-proofs-without-a-restored-project-cache).

## For reviewers

Lean checks every proof. What needs human review is whether the definitions
mean what the model says. Start with the
[trusted-base reading path](REVIEW.md): the fidelity of the execution
semantics (`CrossingExecution`) to the written model comes first.

## Going further

- [Detailed result, hypotheses and verification](docs/UNIVERSAL_FINITE_CHAIN.md)
- [Model ↔ Lean: equations and operational semantics](docs/MODEL_LEAN_CORRESPONDENCE.md),
  including the [threshold correspondence](docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
  between the native first-contact semantics and the model's upward
  crossings, proved for this protocol
- [Cell equations](kernel/README.md)
- [Explicit finite-chain router](proof/lean/KernelR/ExplicitFiniteChainRouter.lean)
- [Fixed-delay construction](proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean) ·
  [indexed-error theorem](proof/lean/KernelR/UniversalChainHeadline.lean)
- [Experiments, historical results, certificate replay and viewer QA](docs/EXPERIMENTS_AND_REPRODUCTION.md)
- [Dated provenance and scope](docs/PROVENANCE.md) ·
  [release checklist](docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md)

## Origin, AI assistance and license

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).

It is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT**
(OpenAI), under the direction of Nicolas Breuillaud. AI assists the
construction of models, code, proofs and documentation. Lean checks the
resulting proof terms against their definitions and hypotheses; that check
does not experimentally validate the physical assumptions or establish every
claim made in the repository.

Source code is [MIT](LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
