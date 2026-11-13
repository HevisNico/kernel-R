# R1: bounded recovery after refusal

This is a new discrete protocol, based on merged v3, not an amendment to its
recorded experiment. Historical v1/v2/v3 sources and evidence stay frozen.
No new campaign or transistor run is part of this milestone.

## Fixed scope

The implemented route to resumption is **external reauthorization**. A finite
observation window alone cannot prove a future leakage law. Learning that law,
window-based empirical validation, random scenarios, a learning tower, and
physical calibration remain separate milestones.

On refusal, revoke the old lease and discard its propagated lower bound.
Create a fresh recovery generation. Before entering recovery, fix a budget N
of repair periods, immutable hardware, prices and the required service floor.
Every recovery visit requires a fresh observation at its scheduled tick. Use
signed reserve bounds, including negative ones. Acknowledge a dose arriving
at the visit exactly once, using the existing pre-measurement / post-delivery
ordering. Hardware in R1 has one-period delivery latency.

Without an admissible reauthorization, command one full configured dose and
probe again one period later while credit remains. At the endpoint N, probe
but issue no further recovery command. Exhaustion is terminal, unavailable
and unguaranteed. A missing/stale reading is a protocol fault and fails closed.
There is no promise of indefinite observations at finite total cost.

## Claims and resumption

During recovery, the only safety declaration is about the freshly measured
**pre-delivery instant**, justified by its sensor error bound. It is never an
interval lease. There is no claim that repair restores uninterrupted service.
The old unsafe exposure is not erased by later recovery.

A reauthorization must identify this generation and this visit, carry a
finite nonempty phase and expiry covering its entire execution, preserve the
service floor, dose, capacity and latency, and pass the existing gain, capacity
and fresh-entry guards. Resumption uses a fresh post-delivery lower bound;
negative values must be rejected before conversion to natural numbers.

The numeric gate checks compatibility, not physical truth or authentication.
The trusted external channel and the new phase's rate, flow and delivery
evidence are explicit premises of the resumed-service theorem. A bit, a
successful arithmetic check or an uncontradicted past window is not a physical
certificate. No future bound is inferred from the recovery samples.

## Proof obligations and controls

1. All recovery safety declarations are sound under honest fresh measurements,
   without any leakage or repair-progress premise.
2. Every continuing recovery step schedules the next probe at exactly +1 and
   spends one repair credit. No recovery interval lease can be emitted.
3. At most N repairs and N+1 observations occur, including the terminal sample.
   Cost is bounded by `(N+1)*probePrice + N*writePrice`, independently of leak.
   A resumed phase is charged separately; recovery is never refunded.
4. Only an admissible external permit resumes. Its proof connects to the
   existing full-execution service theorem, conditional on new physical laws.
5. A separate signed restoration theorem may assume positive net gain,
   adequate capacity and actual delayed delivery. It must not assume service
   during the damaged interval, nor turn this into unconditional liveness.

Tests cover negative reserve, stale observations, stale generation/issue,
expiry before phase completion, changed hardware/service, insufficient entry,
zero net gain, exhausted credit, and a second refusal. Paired Lean mutations
must fail for semantic reasons, not missing imports or parse errors.

## Follow-on ordering

Close this recovery contract first. Then preregister learning/refutation of a
variation rule and a randomized scenario suite before execution. Report all
failures and distributions. Next instantiate the composition verifier on two
learning levels with immutable observation obligations. The R voltage/state
map, waveform dose/leak units and transistor leakage-jump campaign require
their own physical protocol. Python-wrapper refinement, measurement latency
and non-bounded sensor noise are explicitly outside R1's theorem.
