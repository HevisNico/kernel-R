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
next probe t=662. Since the histories before the jump are identical, the
expected first post-jump probe in v3 is t=662. This is an explicit adversarial
case selected from prior evidence, not an independently sampled statistical
trial or a secret pilot of v3.

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
| R1 | First post-jump probe at t=662; its rate-interval lower endpoint exceeds the old ceiling 20; exactly one demonstrated invalidation, zero ambiguous-only exceedances |
| R2 | The decision at t=662 is refusal; its lower uses the fresh observation, not the old carried certificate; no later probes, commands or accepted leases |
| R3 | Zero false `measured_safe_pre` claims, at least one true such claim, and no unconditional safety claim based on an absent probe or a carried bound |
| R4 | Exactly 660 pre-write unsafe and 660 post-write unsafe periods (661..1320), exactly one undetected unsafe period (661), all retained in the report |
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
