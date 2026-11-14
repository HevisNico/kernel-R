# Kernel R v0.5.0: a simulated circuit certified port by port, and a supervisor that stays verifiable

**Release notes for v0.5.0**, released on 2026-11-13. Counts and limits
describe the release commit.

## Summary

This release adds a supervisor, proved in Lean, that keeps a degrading task
in service from dated, bounded-error observations without giving up the
observations that reveal its next error. Four discrete experiments,
each preregistered before implementation and run once, test it with a
known leak ceiling, with a ceiling estimated from observations, with a
broken assumption, and with recovery after that rupture.

It also applies the tolerance theorem of v0.4.0 to a transistor-level
simulation of the R cell, port by port, with bounds measured on each port's
own run. 37 of 200 new ports are certified by preregistered rules, and 57
by a directional rule fixed afterwards on the same ports. On 1 140 fresh
noisy repetitions of those 57 ports (same cells, new noise) the count is
always the predicted one; the directional rule has not yet been tried on
new cells. In every
step of this certification, no certified port had its count contradicted.

The kernel definitions are unchanged.

## Results

**A supervisor that stays verifiable**

- **Service and cost.** For the plan generated from dated bounded-error
  observations, service holds at every time of the accepted plan and the
  number of writes is bounded. Safety is derived from the stated physical
  laws, not assumed. A stale observation is refused, never redated, and
  every contract expires at a horizon fixed in advance.
  [`system_safe`](../research/self-certifying-learning/SelfCertifyingLearning/OfferFactory.lean)
- **Availability.** Under a hard loss ceiling and a funded initial
  reserve, a fixed fallback is always available, and service holds at every
  future time if one physical trajectory realizes every prefix.
  [`perpetual_service`](../research/self-certifying-learning/SelfCertifyingLearning/Availability.lean)
- **Observation has a price.** Every observation attempt is charged, and
  the selector returns the cheapest certified plan in a finite catalogue
  of plans that end at the same deadline.
- **Composition.** Supplied weights are checked exactly against the
  coupling inequalities between levels; a two-level instance is accepted
  and an accumulating three-level chain is rejected.

**Four preregistered experiments.** The leak jumps at a date the
controllers do not know. A naive controller spaces its probes as long as
it sees no failure; a prudent one probes every period.

| Run | Supervisor | Prudent | Naive |
|---|---|---|---|
| [v1](../research/discrete-refresh-experiment/run-v1/REPORT.md), leak ceiling known | 1 247, no missed danger | 2 211 | 1 014, 759 dangerous periods unseen |
| [v2](../research/adaptive-refresh-experiment/run-v2/REPORT.md), ceiling estimated under a bounded-variation law | 1 325, no missed danger | 2 211 | 1 014, 739 dangerous periods unseen |
| [v3](../research/refresh-contract-rupture/run-v3/REPORT.md), leak jumps from 10 to 140, beyond that law | detected at the next probe, one period after the jump in this run (probes were 6 periods apart; the guarantee is the next probe), contract refused, no false safety declaration | | |
| [v4](../research/recovery-v4/run-v4/REPORT.md), v3 then recovery | four unguaranteed repairs, service resumed after a fresh external authorization, zero false safety claims, total cost 5 421 as predicted | | |

All seven predictions of v1, eight of v2, seven of v3 and eight of v4 hold.

- **Recovery after a refusal.** An explicitly unguaranteed mode probes
  every period and repairs within a budget; it makes no safety claim
  without a fresh measurement, and returns to a guaranteed contract only on
  an external authorization bound to a new generation, a fresh issue time
  and a full expiry. [recovery](../research/refusal-recovery/README.md)
- **Calibration.** The leak and the dose of these runs match the refresh
  records of the circuit
  ([calibration](../research/adaptive-refresh-experiment/R_CALIBRATION.md)).

**Certification of a simulated circuit**

- **The circuit.** A transistor-level R cell in the SkyWater 130 nm
  process trains and stops by itself across mismatch, noise, corners and
  temperature; 22 of 24 registered checks and predictions hold.
  [circuit study](../research/circuit/README.md)
- **The bridge.** Integral charge balances of the circuit give the
  kernel's dose identity; the need theorem is extended to doses that vary
  from write to write and to a cumulative error budget.
  [`needAlong_of_cumulative_tolerance`](../research/recursive-learning/native/Search/VariableNeedTolerance.lean) ·
  [bridge](../research/circuit/lean/README.md)
- **Certification on 200 new ports:**

| Step | Ports certified | Counts contradicted |
|---|---|---|
| Margins measured, two conditions declared | 59 | 0 |
| Threshold offset measured on each cell | 58 | 0 |
| Gain also measured independently, as amended before the test runs | 37 | 0 |
| Directional rule, fixed after the campaigns and applied to the same ports (retrospective) | 57 | 0 |
| 20 fresh noisy repetitions of the 57 ports (same cells, new noise) | 1 140 of 1 140 trials right | 0 |

  The directional rule bounds silence and firing separately
  ([`needAlong_of_asymmetric_cumulative_tolerance`](../research/recursive-learning/native/Search/AsymmetricNeedTolerance.lean)).
  The repetitions give a one-sided 95% bound of 0.288% on the probability
  of a wrong count per trial, pooling the ports and counting the 1 040
  independent runs: 100 runs give two ports, so the 1 140 trials are not
  all independent, and the 0.262% of the generated report assumes they
  are. In 925 of the 1 140
  trials the port is certified again from that trial's own measures.
  [repetitions](../research/circuit/repetition/REPORT.md)

  The registered gain measure certifies no port, because the mirror
  current changes after a FIRE; the corrected measure was declared before
  the test runs. Every port whose count differs from its prediction is
  outside the certified domain.
  [first campaign](../research/circuit/certification/REPORT.md) ·
  [measured conditions](../research/circuit/certification-unconditional/REPORT_AMENDMENT_1.md)

**A controller that is reused and adapts**

- Under a fixed calendar, a native selector read returns to rest and is
  prepared again, for any number of rounds, with three input deliveries
  per round in every complete run.
  [`calendar_rounds_exists`](../research/recursive-learning/native/Teaching/SelectorRounds.lean)
- A second level chooses among search policies. The evaluator and the
  acceptance rule are outside its mutable state, and a policy is adopted
  only if it beats the current one by more than twice the evaluator's
  error bound. [adaptive search](../research/reusable-controller/ADAPTIVE.md)

## Limits

- The circuit results are simulations of one cell. No device was measured.
- The joint read of the circuit fires near 0.267 units, outside the window
  proved for the model, (0.239, 0.256]. The simulated cell takes the arrival
  of each pulse from ideal signals.
- The repetition bound pools ports assumed interchangeable; per port, 20
  repetitions bound the error only at 13.9%. The threshold of a cell is
  measured once, on one port; the gain of a read that fires is checked by
  the current up to 0.75 unit.
- The supervisor experiments are discrete models. The variation law of v2
  is supplied, not learned. In v4 the new ceiling comes from an external
  authority that knows the simulator. Decisions come from Lean lemmas; the
  experiment wrappers have no end-to-end proof. The link to the circuit is
  a nominal calibration.
- The `PREDICTION.md` of v3 was revised once, in `07caf3f`, before any
  implementation or execution; the report cites that version.
- The adaptive controller's general theorems assume the evaluator's error
  bound.

Next: the supervisor applied to the simulated circuit, a variation law
that refutes and replaces itself, and a two-level learning tower.

## Verification

Each package has its own build, axiom audit and CI workflow; see its
README. Every audit allows only `propext`, `Classical.choice` and
`Quot.sound` and fails on admitted proofs. The circuit reports regenerate
from the committed results, and the experiment evidence is checked in CI.
The lakefile version fields are left unchanged: several validation
records pin the lakefiles by hash.

## AI assistance

As described in the main README, the work is directed by Nicolas
Breuillaud with AI assistance on models, code, proofs and documentation.
Lean checks the proof terms against their definitions and hypotheses.
