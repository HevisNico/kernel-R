# Two-level refresh experiment — design draft, not preregistration

No empirical controller comparison has been run for this package.
Kernel-checked deterministic witnesses are included. Publishing this file
does not register an experimental protocol: the unresolved choices below
must be fixed, versioned and published before running the comparison.

## Implemented ingredients, not a completed protocol

[CONTROLLER.md](CONTROLLER.md) now fixes a concrete candidate supervisor:
bounded-error scalar reports, interval-separation search epochs, a fresh
safety ceiling `report.hi + slew * cap`, and the maximal affordable positive
wait within `cap`. Zero affordable wait means repair or abstention. The
monitor's reopening count is proved bounded by true sampled variation.

These choices settle parts of information, future-envelope and memory
semantics **for that discrete candidate only**. They do not supply R's
sensor model, choose a perturbation distribution, define the within-period
repair sequence, or fix the naive/prudent baselines. Kernel-evaluated
examples are not an adaptive trial and do not preregister a comparison.

[REPAIR.md](REPAIR.md) additionally fixes a conservative reference plant:
per-tick loss, dose at write completion, saturation, and a fallback that
preserves the repair-time buffer. A finite deterministic trace and general
realization theorem are kernel-checked. They are not an adaptive comparison.
The remaining protocol must choose numerical distributions, sensor behavior,
phase switching, baselines and costs; no empirical results are being
retrospectively preregistered here.

[EPOCHS.md](EPOCHS.md) now fixes admission and accounting for supplied
finite-lived contracts: complete-phase deadline coverage, a common handoff
reserve, explicit switching credit and refusal when no offer qualifies.
A checked two-contract trajectory includes rejection of an expired candidate.
`OfferFactory` now implements a producer for fresh bounded-error scalar
readings under known slew/hardware limits, with an end-to-end proof and a
second deterministic witness. The experiment must instantiate its sensor and
physical bounds and choose a renewal policy; these witnesses do not establish
adaptive performance or perpetual availability of honest offers.

[REVIEW_FOLLOWUP.md](REVIEW_FOLLOWUP.md) adds an explicit per-observation-attempt
price and a finite-catalogue minimum among complete certified plans ending at
the same deadline. These declared prices are not energy measurements, and
catalogue optimality does not settle the online comparison. The fixed-fallback
availability theorem supplies a candidate availability baseline under a hard
loss ceiling and funded initial reserve/deficit.

## Objective

Compare the cost of maintaining a scalar task under leakage while retaining
explicit observation deadlines and repair capacity. Separate continuous
discrete-time safety from recovery after a temporary service violation.
Do not count absence of probes as successful service.

Level 1 loses reserve through a nonnegative leakage process and receives a
bounded positive dose on a designated repair event. Level 2 selects probe
spacing from 1 through 40 base periods. It sees only commanded actions,
their dates and reported responses; simulator ground truth is available
only to the scoring process. The order of leakage, sampling, detection and
writing within a period must be fixed before implementation.

## Essential choices before registration

| Item | Required decision |
|---|---|
| Service | Define the reserve band and whether service must hold between probes; a FIRE is not automatically the required read window |
| Perturbations | Fix allowed rate/jump bounds and times; separately label trials that violate the declared envelope |
| Information | Define response noise and what bounds can actually be inferred from binary/count observations |
| Future envelope | Specify how a current bound remains valid through the next sample; a fitted past rate is insufficient |
| Repair | Fix dose interval, caps, delay and whether one or multiple writes can restore the reserve |
| Controllers | Fully specify a naive cost policy, fixed prudent spacing and contract-constrained adaptation, including initialization and tie rules |
| Memory | Record the context of each decision, expiry, renewal, invalidation and genuine reopening |
| Accounting | Separate service, probes, trial searches, renewals, writes and reopenings |

The historical interval of about 22 cycles between refresh writes is a
calibration clue, not a certified bound on every future leakage trajectory.
The first abstract counterexample already shows why an unbounded hidden
increase defeats an old sampling schedule.

## Candidate hypotheses, to make executable before registration

1. For every trial inside the stated envelope, the contract policy preserves
   the chosen safety condition or the separately declared recovery bound.
2. Every internal correction satisfies the coordinate inequalities and every
   increase in the weighted potential is charged. Then the Lean ledger
   bounds correction count. Logging a desired budget after the fact is
   insufficient: transitions must realize its premises.
3. A reopening bound requires a fresh nonoverlapping charge to a variation
   budget, or another explicit resource. Expiration renewals can occur even
   in a constant environment and must not be charged to nonexistent drift.
4. Compare actual cost against fixed prudent sampling at the same service
   guarantee. The naive controller is not assumed to lose; measure its
   unsafe exposure separately from its observed errors.

Report ground-truth unsafe duration, detection latency, repair latency,
total cost and the separate counters for every trial. A delay bounded by 40
is not sufficient if the physical reserve expires before then. Include
counterexamples with a rate jump just after a probe, insufficient repair
capacity, noisy boundary observations and a continuously valid environment
requiring periodic renewals. Preserve every failure and abstention.

## Subsequent physical work

Only after an executable discrete protocol and its hypotheses are fixed:
derive the R observation correspondence, implement the observation scheduler
and recovery actions, then register transistor-level trials. The current
refresh simulations do not establish the two-level closed-loop contract.
