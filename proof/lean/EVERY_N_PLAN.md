# Physical finite-chain proof: obligations and checkpoints

This is the continuation of the validated three-cell result in PR #14.
The user authorized work on the every-N obligations on 2026-11-02.
The new work has its own branch and draft PR; it does not alter the N=3 PR.

## Target and quantifiers

The target is the physical construction underlying the
[written finite-chain theorem](../reciprocal_composition/THEOREM.md): every
positive finite N, independently chosen fixed fabrication parameters at each
cell/port, declared common READY birth families, and explicit per-emission
wire errors obeying a cumulative budget. We aim to construct actual hybrid
executions. A theorem about every admissible execution is a separate obligation.

The scalable preparation is its own protocol: all cells are born at time0;
16 direct period-eight inputs prepare each relay on port2 and the leaf on
port1, with routes closed. The fast phase starts at160 and supplies K inputs
to the leaf on port0, with K >= 4*N+12. This is not a retiming of the staged
A/B/C birth protocol. No settings copy or physical state reset is allowed.

## Proof ledger

| Obligation | Available result | Work required |
|---|---|---|
| Packet algebra | Arbitrary finite-N induction, counts and resource identities already compile | Connect it to actual physical execution witnesses |
| Receiver, budget0.10 | Actual generic LocalCadenceReceiver, exact ledger-derived outputPacket | Expose its finite Signal and dependent compositions without assuming an output calendar |
| Receiver, full budget0.15 | Width-one separation is supported abstractly | Reprove actual first/second strong charge bands and mixed response; current bands are not valid on the larger domain |
| Relay timing interface | Physical high latencies in[0.16,0.26] and first<=rest; packet closure already proved | Keep this directly proved interface distinct from the older narrower RelayLaw bounds |
| Variable-length leaf | Actual25-input C leaf and arbitrary high-response train | Generalize the three weak inputs, strong/MARK prefix and remaining train to arbitrary K |
| Finite global causality | Generic one-head prepend weaver with exact traces/energy/queues | Iterate it over actual preceding executions; initial fast queue contains only external leaf sources |
| Birth preparation | Physical one-cell and port-generic local components | Construct each declared16-input preparation from its own birth, then parallelize under closed routing |
| Terminal state/memories | True READY returns, reserve and own-memory bounds | Uniform finite-N horizon and count/memory conclusions for the assembled execution |
| Probes/cuts | Written results and finite evidence | Explicit frozen-copy/cut semantics and physical proofs |

## Why the larger jitter budget needs a new proof

A packet at J<=0.15 allows dense gaps[3.7,4.3] and the first transition gap
[3.7,4.4]. The N=3 receiver uses[3.8,4.2] and[3.8,4.3]. In particular its
second-strong band[0.122,0.14] cannot simply be reused: the nominal SLOW charge
at the new gap extremes lies outside that band. New inequalities must retain
the actual charge and energy clocks, not strengthen an assumption silently.

## Checkpoint discipline

Each substantial checkpoint records its exact source commit, build/audit
results, newly passed positive/negative controls, and remaining quantified
premises in the new PR. Uncompiled work is never described as a checked result.
The N=3 headline and its verified code commit remain the completed baseline.
A pause request stops new work; the current branch, validated commits and this
ledger provide a restart point. No merge is performed automatically.

## First exported checkpoint: validated

Thirteen new modules provide: the actual16-input leaf preparation from birth
(14 FIREs, own gain/recovery changes and a true quiet endpoint159.9); an
independent finite-family product; a finite causal-chain induction; exact
receiver signals and their dependent packet composition; variable-K weak and
first-MARK prefixes and the generic cadence suffix; full-budget packet gap
bounds and the two true strong SLOW spans; and source-program restriction
preserving the physical path. All thirteen modules pass with the default heartbeat limit.
The complete exported-tree build passes **9,502 jobs** and the global audit
passes **26,659 project theorems**, allowing only `propext`, `Classical.choice`
and `Quot.sound`. Source checks cover **449 Lean files**, with five inherited
modules unchanged. Generated evidence, all **16 robust certificates**, **12
project tests** and **48 new paired controls** pass. CI configures **1,151 paired
controls**, plus axiom-audit corruption checks; this inventory does not assert
a fresh local rerun of every historical suite. The PR records the exact
validated commit and the actual CI status.

This is not the completed birth-to-cadence theorem for everyN. The finite-chain
and signal compositions still have explicit local physical construction
premises. The generic complete LeafK, low-port relay preparation, expanded
mixed/high receiver and their final assembly remain work in progress.
