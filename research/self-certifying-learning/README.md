# Self-certifying learning: discrete foundations

An independent first proof package for repair budgets and time-limited
observation contracts. It uses **Lean 4.35.0 and Std only**: no Mathlib,
Kernel R definitions, circuit data or other research-package imports.

The research question is whether a system can improve how it maintains a
task while preserving its ability to detect and repair the next failure.
This checkpoint proves discrete ingredients and counterexamples. It does
not yet implement that adaptive system, derive certificates from physical
observations, or claim a new universal principle.

## What is checked

| Statement | Source | Exact scope |
|---|---|---|
| Terminal potential + eta times correction count is at most initial potential + injected disturbance | `Run.balance` in [Budget](SelfCertifyingLearning/Budget.lean) | Every finite trace satisfying the three transition contracts; idle transitions cannot increase potential for free |
| Available rank-decreasing repairs reach a valid state | `repair_exists` in [Budget](SelfCertifyingLearning/Budget.lean) | Constructs a finite path bounded by the initial natural rank; not a real-time or scheduler-fairness result |
| Finite coordinate bounds imply a weighted global decrease | `CouplingCertificate.decrease` in [Composition](SelfCertifyingLearning/Composition.lean) | Explicit positive weights and a positive margin, including all cross-coordinate damage |
| Coordinate corrections enter the finite-run ledger | `CouplingCertificate.prepend` in [Composition](SelfCertifyingLearning/Composition.lean) | Connects the coordinate inequalities to `Run`; disturbances still need their own bound |
| A concrete two-level system stabilizes | `stabilizes`, `path_balance` in [TwoLevel](SelfCertifyingLearning/TwoLevel.lean) | Each correction removes three local ticks and adds one to the other level; all finite correction orders have the same accounting |
| An observation envelope supports a deadline | `safe_until_deadline` in [Deadline](SelfCertifyingLearning/Deadline.lean) | Safety at every intermediate discrete time, assuming the envelope holds there |
| Decisions remain conditional on their context and deadline | `Decision.apply`, `expired_not_usable` in [Deadline](SelfCertifyingLearning/Deadline.lean) | `Usable` is a proposition, not an implemented validity monitor |
| Shared observations cannot certify a property false in a compatible world | `indistinguishable_cannot_accept` in [Deadline](SelfCertifyingLearning/Deadline.lean) | Information limit for any sound observation-only checker |

All potentials, counts, damage bounds and disturbance budgets are natural
ticks. Rational data with a common denominator can be scaled into these
units, provided the required inequalities are established. The package
does not formalize arbitrary real-valued dynamics or round measurements
into certified ticks. Actual reserves in the deadline theorem are signed
integers, so negative reserves are not silently clipped to zero.

The coupling certificate checks the finite weighted inequalities directly.
It does not prove the M-matrix equivalence, compute an inverse, or establish
uniform bounds for towers of unbounded depth. The example has delta = 3,
cross-damage = 1, weights = (1, 1) and eta = 2. [TwoLevel](SelfCertifyingLearning/TwoLevel.lean)
constructs its transitions and proves validity is equivalent to having no
enabled correction. This is a discrete repair example, not a learned
refresh policy or a physical R execution.

## Counterexamples are part of the result

[Counterexamples](SelfCertifyingLearning/Counterexamples.lean) checks:

- Three adjacent levels with relative couplings 4/5 need not admit positive
  weighted margins, even though each adjacent pair product is below one.
- Error smaller than half a dose does not determine an exact count without
  locating the threshold relative to the dose lattice.
- Reaching a threshold exactly provides no reserve against downward error.
- Without repair availability an incorrect state can be a deadlock.
- Bounding corrections does not bound idle/surveillance events.
- Two constant-rate continuations share every available observation before
  the next probe at time 10, yet one is safe and the other is already unsafe
  at time 6. The rates are 10 and 22 ticks per time step, starting at 110.
  This represents a possible hidden rate change immediately after the
  initial sample. It refutes safety based on a stale rate estimate, not the
  deadline theorem with its full-interval envelope premise.

## Reproduce

From this directory, with the pinned Lean distribution on PATH:

```sh
lake build
python3 -B verify.py --report .lake/validation.json
```

No package download is required after Lean itself is installed. The
[dedicated workflow](../../.github/workflows/self-certifying-learning.yml)
checks the same distribution digest as the repository's existing installer.
It builds, audits and runs the controls without requesting a Mathlib cache.

[Audit](Audit.lean) examines every declaration originating in the six
project modules, including private and generated declarations and names
outside the project namespace. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed; project axioms and admitted proofs are rejected.
The source inventory check requires every proof module to be imported.

[verify.py](verify.py) compiles the unmodified module before each of twelve
semantic mutations. A parser/import/name failure or timeout is not a
successful rejection. Three further controls test unused external-namespace
and private axioms and an admitted theorem against the compiled audit.
The report records current source hashes and the actual audit output.

The [recorded local checkpoint](validation.json) passed the full standalone
build: 239 audited declarations, including 107 theorems (generated helpers
included), six project modules, twelve paired semantic controls and three
audit controls. All thirteen repository tests also passed. CI at the
published commit is a separate check; this local record does not predict it.

These checks establish the stated Lean implications, not the fidelity of a
physical implementation to their premises. The full historical Kernel R
build is a separate CI gate; this package does not import or rebuild it.

## Next obligations

1. Implement observation-derived contexts with explicit possible future
   perturbations, deadlines, renewals and a safe fallback.
2. Charge genuine search reopenings separately from periodic renewals.
   Status changes alone do not bound either by disturbance magnitude.
3. Specify a repair-capacity condition: one dose need not compensate for
   all loss incurred during a long observation gap.
4. Fix the discrete comparison in [EXPERIMENT_DRAFT.md](EXPERIMENT_DRAFT.md)
   before running it. No adaptive experiment is run in this checkpoint.
5. Instantiate the contracts in R or another physical model without
   assuming the observations already prove their own soundness.

The existing `stop_training_exists`, cumulative-need, trained-read and
robust-adoption results have **not** been rederived as corollaries here.
The circuit refresh evidence remains empirical evidence in its own scope.

## Prior work and claim boundary

These ingredients have substantial precedents. This checkpoint makes no
novelty claim about self-stabilization, weighted potentials, hysteresis,
certificates or self-triggered sampling:

- [Dijkstra, self-stabilization](https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD426.html).
- [Hespanha, Liberzon and Morse, hysteresis-based supervisory switching](https://doi.org/10.1016/S0005-1098(02)00241-8).
- [Dashkovskiy and Kosmykov, interconnected hybrid systems](https://arxiv.org/abs/1012.5528).
- [Robust self-triggered MPC](https://www.sciencedirect.com/science/article/pii/S0005109816301881).
- [Plemmons, nonsingular M-matrix characterizations](https://doi.org/10.1016/0024-3795(77)90073-8).

Any later contribution must identify what is added by the physical
learning realization, observation contracts and their composition.
