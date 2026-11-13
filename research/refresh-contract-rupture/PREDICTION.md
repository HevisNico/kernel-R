# V3 contract rupture — preregistered negative test

Publish this file alone on PR #114 before writing the v3 implementation.
Then publish the tested implementation, execute one adaptive trajectory once
in a new exclusive `run-v3` directory, and publish every result unchanged.
Do not modify or rerun v2 or v1. A failed or interrupted registered execution
is retained and not retried. CI must inspect saved evidence, not run a trial.

## Frozen dependencies and purpose

Freeze v2 and its published evidence/calibration at
`09b8558fd41516de816544920b5c40315cf53a80`. Use its actual `Contract` wrapper
and Lean bridge unchanged. The v2 law was upward excursion at most B=10
within H=41 periods. This test deliberately violates that law.

The purpose is to test detection, invalidation, refusal and truthful reporting,
not to claim service under violated assumptions. In particular, no system can
promise immediate awareness of an unseen arbitrary jump between probes.

## Plant and information

Use v2's initial reserve 440, service floor 100, capacity 660, delivered dose
220, write latency one period, cap 40, initial paid probe and horizon 1320.
Retain its deterministic sensor errors and radii, prices (probe 1, write 10),
signed reserve, alarm semantics and order: loss -> measurement -> detection
-> delivery of the previous command -> next decision. No instantaneous write,
floor clipping, free final sample, or command after the last scored period.

Only change the plant leakage: 10 before period 661, **140 from period 661**
onwards. Controllers continue to receive the declared B=10/H=41 and do not
receive the new true rate or jump time except through paid sensor reports.
No baseline controller is needed: this is one negative test of the adaptive
controller already compared in v2. All 1320 periods remain scored even after
refusal, while the uncontrolled plant continues leaking. No hidden fallback
or automatic recovery is allowed.

V2's already published prefix was inspected when choosing this test. It has
reserve 220 after period 660, and a wait issued at t=656 with ceiling 20 and
next probe t=662: an active probe spacing of **6 periods**. Since the histories before the jump are identical, the
expected first post-jump probe in v3 is t=662. This is an explicit adversarial
case selected from prior evidence, not an independently sampled statistical
trial or a secret pilot of v3.

## Repair capacity and fixed post-refusal behavior

The post-refusal policy is fixed to **blocked stop**, not an emergency mode.
No new measurements, writes, offers or autonomous restart are permitted after
refusal. The plant and scorer continue to period 1320; unsafe exposure is not
truncated at the refusal boundary. This predicts no recovery in this run.

The repair-power inequality is NOT violated by leakage 140:

    dose 220 > leakage 140 * latency 1 = 140,
    physical net gain per continuously commanded write = 220 - 140 = 80.

Even the fresh inferred ceiling would be 150..152, yielding a positive net
gain of 68..70 and capacity target 100+2*U <=404 <660. Thus this case must not
be reported as “the actuator cannot keep up” or “no valid configuration exists.”
The observation violates the PREVIOUS horizon contract. At the expected
refusal instant t=662, true reserve is -60 and the raw sensor lower is -64.
The old carried estimate 139 is no longer valid and must be discarded. The
fresh diagnostic ceiling is 150 (rate report 139 plus error 1 plus B=10), whose
ready guard is 100+150=250; -64 does not meet it. A valid numerical repair
configuration is not an admissible safe continuation from this entry state.
Furthermore, the failed variation law cannot simply be assumed valid again
by issuing a new number. A separately justified recovery/reauthorization
protocol would be needed; none is part of this preregistered test.

## Violation and refusal

At each probe the unchanged v2 bridge checks the current rate interval against
the previous ceiling. A lower endpoint above that ceiling is a **demonstrated
violation**; an upper-only exceedance is merely ambiguous. The former discards
the carried lower and returns `refuse`. The runner latches invalidation,
records its evidence and schedules no later probe, command or new operational
contract. A new numeric ceiling computed in the refusal record is diagnostic,
not an accepted lease. Any pending dose from an earlier command would still
be logged and delivered; it would not count as continuing controller action.

Synthetic checks before the registered run must include a proven violation
with ample reserve, so refusal cannot pass merely because a separate readiness
check also happens to fail.

## Truthful safety declarations: a necessary distinction

There are two different statements, logged separately and never rewritten
retrospectively:

1. `measured_safe_pre`: a claim about **this sampled pre-write instant only**,
   issued iff a paid probe's raw reserve lower (report minus error 2) is >=100.
   It uses no carried bound and is never extrapolated to later periods. No
   probe means this field is false/unknown, not that the physical state is
   known unsafe. This claim must never be false on ground truth and must be
   issued at least once (no vacuous always-unknown result).
2. `conditional_contract_active`: an unrevoked, unexpired accepted contract
   is currently being relied upon, **conditional on its variation/delivery
   premises**. It is not an unconditional declaration of actual safety. It
   can remain active during an undetected physical violation. Detection
   revokes it before reporting the new status for that period.

The scorer separately records true pre/post unsafe periods, undetected unsafe
periods, every unsafe period with an active conditional contract, and every
period where actual leakage exceeds the active ceiling. These counters must
remain visible even if all controller refusal assertions pass. Calling a
conditional certificate an unconditional all-time safety guarantee would
fail this test; relabeling past rows after detecting the jump is forbidden.

This distinction is essential: if “no falsely safe period” meant no actual
failure while an old conditional contract is still active, this scenario is
expected to **refute** that stronger statement, not prove it.

## Registered predictions

| ID | Prediction |
|---|---|
| R1 | Last pre-jump probe t=656, active spacing 6, first post-jump probe t=662: detection delay 1 <= 6 periods. Its rate report 139 gives interval [138,140], whose lower endpoint 138 exceeds the old ceiling 20: exactly one demonstrated invalidation, zero ambiguous-only exceedances |
| R2 | At t=662, refuse with fresh lower -64, discarding carried 139; latch blocked stop. Zero later probes, commands or accepted leases; no recovery through t=1320. Positive repair power does not override invalidation and failed entry readiness |
| R3 | Zero false `measured_safe_pre` claims, at least one true such claim, and no unconditional safety claim based on an absent probe or carried bound. No past row or safety declaration is changed after detection |
| R4 | Exactly 1 dangerous period strictly before detection (661), <= active spacing 6; 1 dangerous detection period (662), then 658 dangerous periods (663..1320). Totals: 660 pre-write unsafe, 660 post-write unsafe, 1 undetected unsafe; all retained separately |
| R5 | Exactly one unsafe period with an active conditional contract (661); the stronger uninterrupted-service assertion is **false**, explicitly reported as REFUTED rather than omitted |
| R6 | Common plant/action fields through t=660 match the archived v2 prefix; no assumption violation, refusal or invalidation before the jump; final reserve is -92180 |
| R7 | The trace audit validates noise bounds, period order, one-period delivery, costs, alarm persistence, evidence for invalidation and the cessation of control; it expects the B/H law to fail and never marks that premise satisfied globally |

The expected reserves are analytic consequences of the published prefix:
x(661)=220-140=80, x(662)=80-140=-60 and x(1320)=220-660*140=-92180.
Noise cannot hide the large rate-interval separation. The service alarm can
only detect the first unsafe interval at the paid probe t=662.

## Evidence and publication

Retain each period, including t=0 and all periods after refusal, with the v2
fields plus sampled safety claims, accepted-contract status/ceiling/expiry,
latched invalidation and scorer-only truth flags. Controller inputs remain
bounded-error reports, time and action history; scorer flags are never inputs.

Publish protocol and code commits/hashes, Python/Lean versions, clean source
state, raw CSV, stdout/stderr, exit status, all R1–R7 verdicts and the separate
refutation of unconditional uninterrupted service. Preserve every failure.
Do not reclassify a failed prediction as a successful test after seeing it.

Add CI outside the frozen v2 directory to compile its bridge, check its local
proofs and synthetic tests, and independently validate stored v1/v2/v3 evidence.
It must never invoke any `--run-once` entry point or controller trajectory.
This closes the independent auditor's CI finding without changing v2.
