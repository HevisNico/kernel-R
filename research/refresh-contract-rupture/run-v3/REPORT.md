# V3 contract rupture — unedited generated report

One preregistered negative-test trajectory. V2 and V1 were not rerun or modified.
Protocol: `07caf3fdf22c1cd28f05a2159d40aceaa33af80b`.

## Detection and blocked stop

Last pre-jump probe: 656; spacing: 6 periods.
First post-jump probe and invalidation: 662; delay: 1 period(s).
Demonstrated invalidations: 1; ambiguous exceedances: 0; refusals: 1.
After refusal: 0 probes, 0 commands, 0 active-contract periods.
The record distinguishes the new diagnostic ceiling from an accepted contract.

## Unsafe exposure — including after refusal

| Quantity | Periods |
|---|---:|
| Dangerous strictly before detection | 1 |
| Dangerous at detection | 1 |
| Dangerous after detection | 658 |
| All pre-write unsafe | 660 |
| All post-write unsafe | 660 |
| Undetected unsafe | 1 |
| Unsafe with active conditional contract | 1 |
| False sampled-instant safety declarations | 0 |

True sampled-instant safety declarations: 179.
Undetected unsafe timestamps: [661].
Unsafe conditional-contract timestamps: [661].
First physical B/H breach: 661; global variation premise satisfied: False.

**Unconditional uninterrupted service: REFUTED.**
A conditional contract was still active during the unseen jump. Its past period
is not relabeled safe after detection. Sampled safety claims use only fresh
sensor lower bounds and never extend to an unobserved interval.

## Repair power and cost

Dose 220 > 140 × latency 1; physical net gain would be 80 per commanded write.
Thus the refusal is not an actuator-power impossibility. At detection, the old
contract is contradicted and the fresh entry lower is below the ready guard.
The preregistered policy is blocked stop, not emergency recovery.
Probes: 180; commands/deliveries: 29/29; cost: 180+290=470.
Final signed reserve: -92180.

## Registered predictions

| ID | Verdict |
|---|---|
| R1 | PASS |
| R2 | PASS |
| R3 | PASS |
| R4 | PASS |
| R5 | PASS |
| R6 | PASS |
| R7 | PASS |

Trace audit issues: 0.

No parameter or prediction was changed after publication; no registered run was repeated.
Rows were appended and hash-chained at emission; no retrospective label update is performed.
All 1320 physical periods are counted even though control stops at refusal.
This is a deliberately selected counterexample using the published v2 prefix,
not a probabilistic guarantee or a physical transistor validation.
