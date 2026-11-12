# Self-certifying learning: discrete foundations

An independent first proof package for repair budgets and time-limited
observation contracts. It uses **Lean 4.35.0 and Std only**: no Mathlib,
Kernel R definitions, circuit data or other research-package imports.

The research question is whether a system can improve how it maintains a
task while preserving its ability to detect and repair the next failure.
This checkpoint proves discrete ingredients and implements an observation-level
supervisor: interval-based search reopening and a fresh, maximal admissible
probe delay. A conservative fallback now closes the delayed repair/scheduling
loop under a fixed full-duration loss ceiling. Physical parameter identification,
search inside an epoch and adaptive envelope switching remain open. There is
no claim of a new universal principle.

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
| Honest interval separation charges each reopening to distinct sampled variation | `reopening_bound` in [Renewal](SelfCertifyingLearning/Renewal.lean) | Executable hysteresis; arbitrary honest interval widths; no false reopening in a constant world |
| Sufficiently large resolvable movement triggers reopening | `detects_resolvable_change` in [Renewal](SelfCertifyingLearning/Renewal.lean) | Movement at least granularity plus the two report widths; checked at a visit |
| The selected positive wait is maximal and safe | `plan_spec`, `plan_safe` in [Scheduler](SelfCertifyingLearning/Scheduler.lean) | Within a finite cap and certified loss ceiling; `none` requires repair or abstention |
| A current report plus known future slew yields a loss ceiling | `rate_ceiling_sound` in [Scheduler](SelfCertifyingLearning/Scheduler.lean) | Uses a supplied slew bound over the whole cap; cannot certify an arbitrary hidden jump |
| Bounded-error measurements produce sound controller inputs | `measurement_sound` in [Controller](SelfCertifyingLearning/Controller.lean) | Signed reserve lower bounds below zero are refused; no R sensor correspondence yet |
| The supervisor refreshes safety even when search memory is retained | `visit_safe`, `run_reopening_bound` in [Controller](SelfCertifyingLearning/Controller.lean) | Concrete executable `visit`/`run`; conditional service at each accepted window and separate reopening accounting |
| Delayed saturated repairs reach a usable reserve in bounded time | `recovery_restores`, `recovered_ready` in [Repair](SelfCertifyingLearning/Repair.lean) | Positive net dose, sufficient capacity and an explicit finite batch; service may fail during recovery |
| A generated wait/write loop preserves service and bounds writes and elapsed time | `execution_safe`, `write_bound`, `clock_accounting` in [ClosedLoop](SelfCertifyingLearning/ClosedLoop.lean) | Starts with a repair buffer; ceiling must hold throughout all waits and writes |
| A guarded observation window can hand off to the fallback | `guarded_visit_handoff` in [ClosedLoop](SelfCertifyingLearning/ClosedLoop.lean) | Schedule against service plus repair-time loss; next phase needs its own envelope |
| The transition contracts have an executable plant witness | `simulate_realizes`, `simulated_service` in [RepairPlant](SelfCertifyingLearning/RepairPlant.lean) | Finite discrete execution, worst-case leakage, end-delivered dose and saturation; no hardware claim |
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

## Executable supervisor

[CONTROLLER.md](CONTROLLER.md) specifies the new observation-level mechanism,
its proof chain and its limits. Every visit constructs its safety plan from
the **fresh** rate interval, while only a sufficiently separated interval
replaces the search anchor. A retained anchor is not a certificate that an
old rejection or old policy remains valid.

With reserve 110, required reserve 10, zero slew and cap 40, exact rate 10
permits a wait of 10; rate 22 permits 4. At rate 12 the wait shortens to 8
even when a granularity-5 search anchor stays at 10. An interval [0, 200]
requires refusal at that reserve although it does not prove a rate change.
These are kernel-checked examples, not a preregistered adaptive comparison.

## Delayed repair loop

[REPAIR.md](REPAIR.md) specifies the conservative fallback, its finite recovery
batch and their different service guarantees. A service floor r and repair
loss U*tau require buffer `r + U*tau`; a positive net dose and enough capacity
then permit return to a positive wait. The generated loop has proofs for
intermediate-time safety, write count, elapsed time and absence of an endless
write-only episode. A concrete executable plant realizes its contracts.

The observation supervisor can hand off to this loop when it preserves that
buffer. A fixed loss ceiling for the entire fallback epoch is still required;
the code does not infer future physical bounds or automate safe reconfiguration.

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

[Audit](Audit.lean) examines every declaration originating in the twelve
project modules, including private and generated declarations and names
outside the project namespace. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed; project axioms and admitted proofs are rejected.
The source inventory check requires every proof module to be imported.

[verify.py](verify.py) compiles the unmodified module before each of thirty-six
semantic mutations. A parser/import/name failure or timeout is not a
successful rejection. Three further controls test unused external-namespace
and private axioms and an admitted theorem against the compiled audit.
The report records current source hashes and the actual audit output.

The [recorded local checkpoint](validation.json) records the current standalone
build, audited declaration/theorem counts, twelve project modules, thirty-six
paired semantic controls and three audit controls. Generated helpers are
included in declaration counts. CI at the published commit is a separate
check; this local record does not predict it.

These checks establish the stated Lean implications, not the fidelity of a
physical implementation to their premises. The full historical Kernel R
build is a separate CI gate; this package does not import or rebuild it.

## Next obligations

1. Derive the measurement and future-slew assumptions from an actual sensor
   and plant. Bounded-error scalar measurements are now handled; R binary/count
   observations and unforeseen physical jumps are not.
2. Implement search and its stored decisions inside each epoch. Reopening
   accounting is now proved for the interval monitor, but it does not bound
   search work, safety refusals or periodic certificate renewals.
3. Automate switching between fresh observation policies and the conservative
   delayed-repair fallback, with valid envelopes, admission checks and costs
   at every switch. The fallback and guarded handoff are now proved; adaptive
   selection of their physical contracts is not.
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
