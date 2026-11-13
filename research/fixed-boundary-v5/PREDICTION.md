# V5 preregistration: service inside a fixed physical boundary

Publish this file alone before v5 implementation or generation/inspection of
any new seeded scenario. This is a safety and availability milestone, not an
adaptive-learning claim. The optimistic law is omitted from the controller;
its identical-action negative result remains in the preceding exploratory
study, #119 at `2cd95d2043ad2c964304a64178f3b7f1c377d671`.

## Known evidence versus genuinely new observations

The v3 scenario (10 to 140 at 661) has already been explored. Its early-refill
cost 5671 and restricted oracle cost 5516 are known, not blind predictions.
V5 tests whether a Lean-kernel implementation reproduces those exact numbers.
The gap is `155/5516 = 2.8100...%`: claim **less than 2.82%**, not less than 2.8%.
This ratio applies only to that known scenario and the action family below.
There is no preregistered 2.82% promise for random scenarios or other physics.

The twelve seeded scenarios below are new confirmatory cases. Their exact
rates, noise, cost and oracle gaps must not be computed before this protocol
is published and the tested implementation is frozen. No pilot or subset is
permitted. Report all cases, distributions and failures; do not replace seeds.
The separate exploratory economic sweep uses its own scope and no v5 seeds.

## Fixed physical boundary and chronology

H=150, service S=100, capacity C=660, dose D=220, one-tick delivery latency;
initial reserve 440; horizon t=0..1320 inclusive; exact integer arithmetic.
Within the boundary, every period's loss lies in [0,150], reserve-sensor error
in [-2,2], rate-sensor error in [-1,1], and each commanded dose is delivered
once at the next tick with upper saturation at 660. Signed reserves are never
clipped at zero. Future hard bounds are supplied physical premises, not
inferred from previous observations or justified by a runtime authority.

Order: loss, pre-delivery measurement if due, delivery of an earlier command,
then decision. Each probe costs 1 and includes both sensor channels; each
commanded write costs 10. Pay the initial and terminal probes. At t=1320,
finish pending delivery and read the sensors, but issue no new command. Stop
claiming service after the scored horizon. No runtime external permits or
root events are issued; the prior boundary-justification and computation costs
are not assigned prices. Report all costs without reset or refunds.

## Controller and the invariant to prove

At each observation, form fresh lower/upper post-delivery bounds from report
minus/plus 2, adding 220 and clipping at 660 only if a dose just arrived. Let
L=max(fresh lower, previous H-based carried lower); there is no optimistic
carried bound. Initially use the fresh lower alone. Require `250 <= L <= 660`.

If the measured rate lower `report-1` exceeds 150, refuse and discard carry.
Otherwise, if entry is not Ready, refuse. For a Ready state:

1. If fresh upper + 220 <= 660, write early, duration 1.
2. Otherwise let d=min(40, floor((L-250)/150)). If d>0, wait d; else write.
3. Carry `L-150*d` after waiting, or `min(660,L-150+220)` after a write.

The matched safe-prudent comparator uses the same bounds and guard but waits
one tick when a certified wait exists; otherwise it writes. Both policies
must be covered by Lean safety/availability results. The Python runner must
invoke the proved Lean choice kernel, with a separate arithmetic audit of
saved decisions and plant traces. Prove guard preservation, pre-delivery and
post-delivery service across composed actions, sensor/carry soundness, and a
finite horizon/action-cost bound. State precisely the gap between the proved
Lean model/kernel and the tested Python orchestration; do not claim a formal
proof of arbitrary Python execution.

No fresh observation can increase the guaranteed wait beyond the hard-H
guard. Early refill has no access to future rates, jump times, seeds or noise.
Physical truth belongs only to the plant, scorer and explicitly omniscient
comparison algorithm. Guard premises and all unsafe intervals remain visible.

## Frozen comparator family and oracle

Freeze the finite dynamic-program comparator of #119 at the dependency SHA
above: at each paid observation, any Ready state may issue one write (duration
1) or any integer wait d in 1..min(40,floor((L-250)/150)). The endpoint lower
uses H-based carry and the next fresh measurement exactly as above. A terminal
observation may shorten a wait at 1320. It costs 1 and issues no next action.
All physical pre/post states follow the same losses, sensor errors and dose
laws as the controller. Cost is probes+10*writes; no terminal inventory value.

The offline optimizer knows every future loss and sensor error. It may write
early and may waste dose at saturation. Report its probes, writes, saturation
loss and final reserve; the 2.82% comparison does not require equal terminal
reserve. It is an optimum only in this specified action family, not a global
physical optimum or an implementable autonomous controller. Validate optimal
costs by independent forward and backward dynamic programs, including every
seeded case. Preserve disagreement as failure, not an opportunity to retune.

## Scenario generation, fixed before inspection

Use Python 3.12 `random.Random` with three independent streams per seed s:
plant `Random(s)`, reserve errors `Random(s+100000)`, rate errors
`Random(s+200000)`. Generate all reserve errors for t=0..1320 with
`randint(-2,2)` and all rate errors with `randint(-1,1)`. Generate plant arrays
as follows, without rejection, resampling or seed substitution:

- Seeds 2026111301..2026111304 (single jumps): draw initial rate as
  `10*randrange(16)`, jump date as `randrange(1,1321)`, then new rate as
  `10*randrange(16)`. Use initial rate before that date and new rate from it
  onward, including the allowed case of no numerical change.
- Seeds 2026111305..2026111308 (slow variation): draw initial rate as
  `10*randrange(16)`. For t=1..1320, whenever t%20==0, update rate by
  `choice((-10,0,10))` clipped to [0,150]; otherwise retain it.
- Seeds 2026111309..2026111312 (periodic jitter): draw each rate independently
  as `10*randrange(16)` for every t=0..1320.

The known replication uses rates 10 before 661 and 140 thereafter; errors
`(7*t+1)%5-2` and `(5*t+2)%3-1` as in v3/v4. One outside-boundary control uses
that same deterministic scenario with post-jump rate 170 instead of 140.
Keep recording after refusal with no new commands through t=1320; do not
hide the consequent service loss. No oracle ratio is defined for that control.

## Registered outcomes

- S1: the known replication has zero unsafe pre/post periods, no refusal,
  zero runtime external authorizations, 1171 probes, 450 writes, total 5671,
  final post reserve 440; matched safe prudent cost 5821.
- S2: known-scenario oracle cost 5516, matching both solvers; exact fraction
  (5671-5516)/5516 < 282/10000. Retain its terminal reserve and saturation loss.
- S3: all twelve in-bound seeded early-refill and safe-prudent runs complete
  with zero unsafe pre/post periods, zero refusals and no external authority.
- S4: independent audits of saved rows, source/protocol hashes, paid calendars,
  saturation, carry and total cost have zero issues. All within-bound oracle
  costs match both solvers and are at most their corresponding policy cost.
- S5: outside-boundary rate170 control refuses on its first post-jump probe,
  no later than t=663, and emits no later commands. Report its actual detection
  date and all unsafe periods. Do not assert safety outside the boundary or
  detection of every arbitrarily small/brief breach of H.
- S6: publish each seeded cost, oracle gap, probes, writes, minimum pre reserve,
  final reserve and saturation loss, plus min/median/max summaries. Report
  the number with gap below 2.82% and without cost improvement versus prudent;
  neither number has a success threshold. No statistical population guarantee
  or significance claim follows from twelve selected seeded cases.

## Publication and single-batch execution

Preserve all historical source/evidence. Publish tested implementation after
this protocol. Before the batch, #119's exact head must have all workflows and
latest-attempt jobs completed successfully. Publish that snapshot and a durable
RUN_ATTEMPT marker identifying protocol and implementation commits. Execute one
exclusive `run-v5` batch containing the known replication, the twelve generated
scenarios, matched prudent runs and the outside-boundary control. Oracle/audit
calculations are comparisons, not additional controller trials.

Publish scenarios, append-only raw decision/plant traces, oracle results,
unedited generated report, verdicts, tool versions, source hashes, stdout/stderr
and exit status. CI only checks proofs and saved evidence; it never generates
or reruns this registered batch. Synthetic unit tests must not execute any
registered scenario or shortened pilot. Preserve failures and partial output;
an existing attempt marker after interruption forbids a second launch.
