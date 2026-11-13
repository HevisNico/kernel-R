# V4 preregistration: rupture, acknowledge, repair, resume

Publish this protocol before implementation or any v4 trajectory. Publish the
tested implementation next. Run exactly one new trajectory in exclusive
`run-v4`, after the exact #117 prerequisite has all workflows/latest jobs
successful. Preserve every failure; do not rerun, tune or replace evidence.
Synthetic tests must not execute this registered trajectory or a shortened
pilot of it. CI audits saved evidence; it never launches a trial.

## Frozen basis and intervention

Use #117 at `c6684f796d092b2324489cb9920f78a9fcca7a5a`, including its unchanged
Supervisor and Lean decision kernels. Preserve v1/v2/v3 and their recorded
evidence. V4 executes its own copy of the registered scenario, using the
unchanged v2 Contract until its first refusal, then the unchanged R1 Supervisor.
It does not invoke an old experiment runner or overwrite an old run.

Retain the v3 horizon 0..1320 inclusive, initial reserve 440, service 100,
capacity 660, dose 220, latency one period, and leakage 10 before t=661 and
140 from t=661 onward. Signed reserves are not clipped at zero. Retain the
deterministic errors `((7*t+1)%5)-2` for reserve and `((5*t+2)%3)-1` for rate,
with radii 2 and 1. The physical order is loss, pre-delivery measurement,
detection, delivery of an earlier command, next decision.

At the first refusal, revoke the old lease, discard its carried lower bound
and enter `recovery-unguaranteed` at the **same paid observation**. Do not
sample twice. Configure eight recovery commands and 82 external phases, with
no automatic credit replenishment. Probe each recovery period and command the
full dose while credit remains, as R1 specifies. A dose already pending is
acknowledged once. Costs and dangerous exposure never reset on handoff.

At t=1320, take a paid terminal pre-delivery observation and complete any
previous delivery, but issue no new decision/command. This explicit endpoint
readout does not claim service after the scored horizon. Any normal due time
after 1320 is replaced by this final readout; the expected run already probes
every period after the refusal.

## External reauthorization and its justification

The external authority issues one root authorization at the **fixed time
t=666**, selected now by the arithmetic below, not after running v4. It binds
ceiling 150, service 100, dose 220, capacity 660, latency 1, and expiry 1640.
The model's registered plant has rate exactly 140 at every t>=661, hence
rate<=150 throughout the authorization interval. Prove this inequality in
Lean directly from that piecewise plant definition.

This is an external, model-based justification. The ceiling is not learned
from recovery reports, measured on a transistor circuit, or an unconditional
guarantee for an unknown future environment. Sensor and delivered-dose laws
are the registered simulator's laws, independently checked in the trace.
Report this scope in the final summary, not only in the body.

R1 permits at most eight decisions per phase. The single root authorization
therefore supplies fresh eight-decision tokens at the first eligible visit
at/after 666 and whenever the preceding phase completes. Every token binds
the current recovery generation, current issue time, bound 150 and root
expiry 1640. Phase completion increments generation through the unmodified
R1 code. Tokens do not change the root ceiling or gain access to plant truth.
The authority receives time and supervisor request state only. Invalid or
insufficient-entry tokens are not treated as successful reauthorization.

Count both the single external root event and every token instantiation.
The registered abstract prices are probe=1, commanded write=10, root=1,
token=1. Report probe/write cost separately so comparison with v3 remains
legible. These are declared accounting units, not measured energy or human
certification effort. No hidden/free repeated authorization is allowed.

## Predictions, derived before execution

The archived v3 supplies the prefix: after660 reserve220; at661 reserve80;
at662 reserve-60, fresh lower-64, rejected carried lower139. Its 180 probes
include the refusal at662; before that visit there are179 probes and29 writes.
Four recovery deliveries give post reserves20,100,180,260 at663..666. At666
the reserve error is+1, so the fresh lower after delivery is259, above the
new guard100+150=250. At667 the pre-delivery reserve is120 and its fresh
lower116, so the first sampled safe pre-instant after the outage is667.

After authorization, R1 waits only when its fresh lower>=400. A write is
chosen below400; since fresh lower>=actual post-4, its following post reserve
is at most403+80=483. Waiting reduces reserve by140. The new entry starts260,
so post reserves stay below550 and every chosen wait has length1. Ready is
maintained: a wait starts with actual post>=400 and next fresh lower>=256;
a write starts above the guard and gains at least76 in the fresh lower.

There are654 active decisions at666..1319, hence82 eight-decision tokens.
For active write count w, dose conservation gives
`post(1320) = 260 - 140*654 + 220*w = -91300 + 220*w`.
In fact post reserves stay in260..483: a wait starts at actual post>=400
and ends at>=260; a write adds80 to a post already>=260. Conservation then
forces w=417 and final reserve440, without a pilot or trajectory computation.
No prediction is revised afterward.

| ID | Registered prediction |
|---|---|
| V1 | V3 common plant/legacy-decision prefix matches through refusal662; last pre-jump probe656, first post-jump probe/refusal662, one demonstrated legacy invalidation, no ambiguous-only event |
| V2 | Exactly four unguaranteed recovery commands662..665 and their deliveries663..666; fresh entry-64 at662 and259 at666; no recovery interval guarantee; five boundary-inclusive recovery probes662..666 cost45 with its exit probe counted once |
| V3 | Root issued exactly666; first token admitted at666 using generation1, bound150 and fresh post-delivery entry; no old carried bound is used; no later demonstrated violation or failed-entry refusal |
| V4 | New guarantee begins **post-delivery666**, not pre666; every pre-instant667..1320 and every post-instant666..1320 is safe under the registered model; first recovered sampled-safe pre-instant667 |
| V5 | Zero false sampled-instant declarations, zero false new pre/post guarantee declarations, nonzero true declarations; exactly six pre-unsafe periods661..666, three post-unsafe periods661..663, and one undetected unsafe period661; none removed from the trace |
| V6 | 838 paid probes, 450 commanded/delivered writes (29 legacy +4 recovery +417 authorized), 82 tokens (first +81 renewals), one root event; probe/write cost5338, complete cost5421; final reserve440 |
| V7 | The old v3-style conditional status is unsafe at661; its incoming lease also reaches the detection instant662. Report both statuses. Unconditional uninterrupted service across the whole run remains REFUTED |
| V8 | No source/protocol/evidence alteration, no double-paid handoff probe, no write at1320, no outstanding physical dose after the endpoint, no budget refund; independent arithmetic, timestamp, authorization, cost and hash-chain audits have zero issues |

## Safety labels and evidence

Keep `sampled_safe_pre` distinct from all interval claims. No probe means
unknown, not a safe or unsafe measurement. Record old-lease status separately
on arrival and after detection. Do not retroactively relabel t=661 as safe.

For the new contract, record separate `guaranteed_pre` and `guaranteed_post`.
At666, pre40 is unsafe and unguaranteed; post260 is the newly authorized
origin. The first new guaranteed pre-instant is667. Never multiply a
post-authorization flag by a pre-delivery state and call that a false claim.
Alarm detection precedes dose delivery; alarm clearance follows fresh
post-delivery evidence. Retain both alarm fields and all unsafe exposure.

Append every period once, with a row hash chain, original legacy decision
fields, supervisor/authority status, inputs, commands, deliveries, claims,
and cumulative costs. Truth is confined to plant and scorer. The trace auditor
must recompute expected decisions algebraically from the recorded reports,
without launching another controller/plant trajectory. Publish unchanged raw
CSV, root/tokens evidence, all verdicts, generated report, stdout/stderr,
exit status, tool versions, clean source status and source/protocol hashes.

Before the attempt, publish a persistent RUN_ATTEMPT marker identifying the
tested implementation and protocol. Once this marker exists, a lost session
or failed attempt must not cause a second launch. Publish surviving failure
evidence and report the interruption instead. The only registered output is
exclusive `run-v4`. Keep learned-variation preparation out of this trial.

The result is a finite, discrete model demonstration of breaking, detecting,
repairing and reauthorizing service. It is not transistor-level validation,
a statistical repetition study, learned future variation, or a new proof of
the complete Python runner.
