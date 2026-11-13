# Bounded recovery after refusal

R1 adds an explicitly **unguaranteed recovery mode** after v3's refusal. The
implemented exit is external reauthorization. A successful past observation
window is not evidence of a future leakage bound.

The protocol was published separately before implementation in
`c7a28a8da704cda80ff7a364424eda15f5281ae4`. Read [PROTOCOL.md](PROTOCOL.md) for
scope and the ordering of later milestones. The saved v1/v2/v3 experiments,
their source hashes and the standalone foundation package remain unchanged.

## Executable behavior

`controller.Supervisor` starts at a refusal boundary. Give it the current time,
the last generation, any dose already pending at that boundary, a repair
budget N and an external-phase budget E. Its only plant inputs are fresh
observations and externally supplied permits. It never receives plant truth.
The old carried reserve and old lease are absent from its state.

Each recovery visit probes the pre-delivery reserve. An acknowledged delivery
is applied once, with capacity saturation, to form the fresh post-delivery
lower bound. Without an admitted permit it commands the maximum dose and
probes one period later. After N recovery commands, the endpoint is still
observed but no further recovery command is sent. Exhaustion and missing,
stale, malformed or inconsistent observations terminate without an interval
guarantee. Failed probe attempts are charged.

The fixed discrete hardware is service 100, dose 220, capacity 660, delivery
latency one period, sensor radius two reserve units, maximum authorized wait
40 periods and maximum eight decisions per external phase. During an active
phase, the rate report has assumed radius one. The input channel must report
delivery honestly; neither sensor accuracy nor actuator performance is proved
from circuit data here.

Each external permit binds generation, issue time, expiry, loss ceiling and
decision count. Service, dose, capacity and latency cannot be changed by a
permit. The entry gate checks positive net gain, capacity, repair buffer and
the complete initial planned phase before allowing resumption. A negative
reserve is rejected before conversion to natural numbers.

After admission, the Python supervisor dispatches the existing Lean repair
policy, using a fresh lower bound at each visit. It checks expiry for every
actual action and never exceeds the permitted decision count. A demonstrated
rate violation revokes the lease before the same observation is reused for
recovery. A completed phase also requires a new authorization. Every such
return increments the generation. Neither repair credit, phase credit nor
the accumulated cost is reset. A permit for an old generation is rejected.

The adapter labels an authorized phase `authorized-conditional`, not an
unconditional physical guarantee. The external channel is assumed trusted;
numeric admission is not cryptographic authentication and does not establish
future physics. Continuous service during that phase needs the explicit
rate/flow/delivery hypotheses below. A jump between probes can violate them,
as in v3; later detection does not erase that exposure.

## Proof map

| Module | Established result | Premises / limits |
|---|---|---|
| `Machine` | Every sampled-instant claim in a finite recovery run is sound | Fresh honest reserve measurements; no leakage assumption |
| `Machine` | At most N repairs and N+1 probe attempts; cost ≤ `(N+1)p + Nw` | Fixed recovery budget and nonnegative prices, including the terminal sample |
| `Machine` | Every continuing repair schedules exactly +1; no write at zero credit | One-period delivery model; recovery frames carry no interval lease |
| `Machine` | External handoff yields the existing full-phase service theorem | Fresh signed entry, numeric admission, actual bounded rates, flow and delayed delivery |
| `Restoration` | Signed endpoint bounds and finite restoration | Positive net gain, target within capacity and actual deliveries; no interior service claim |
| `Runtime` | Each admitted active action preserves service and its endpoint bound | Fresh entry and actual action dynamics; detected rate violation is refused |
| `Examples` | Nonvacuous recovery/admission and refusal fixtures | Deterministic exact arithmetic, not empirical evidence |

`Machine.run` ends at handoff, exhaustion or fault. The executable adapter
continues into the active policy and can return to recovery on a later
violation. That orchestration is covered by synthetic tests, **not a new
end-to-end Python refinement theorem**. This is a deliberate distinction
between the proved kernel and the tested wrapper.

For the adapter's entire lifetime, at most N recovery commands and `8E`
active decisions can be dispatched. Every nonterminal probe dispatches one
such action, so its accounting bound is `(N+8E+1)p + (N+8E)w`. This is the
wrapper's separate conservative bound, checked in tests; the Lean
`cost_bound` theorem concerns one recovery run. A resumed action is billed
in addition to the final recovery probe, never hidden or refunded. External
authorization-generation costs and real energy consumption are not modeled.

The signed example starts at −64. Under a **newly justified** loss ceiling
150, dose 220 and capacity 660, five delayed endpoints are 6, 76, 146, 216,
286. The last value passes guard 250. Its pre-delivery value is only 66, so
the final recovery visit still cannot declare the pre-delivery instant safe.
The example is not a rerun of the recorded v3 plant and establishes no
measured physical ceiling. Arbitrary leakage need never permit restoration.

## Validation

Run from this directory with pinned Lean 4.35.0:

```sh
lake build
python3 -B verify.py --report .lake/validation.json
```

The verifier audits all declarations of all five package modules, rejects
nonstandard axioms and proof shortcuts, runs nine synthetic integration
tests and twelve paired semantic proof mutations. Each mutation's original
module must compile first. Import/parser failures do not count as rejection.
Tests include a complete recovery/resumption, a second contract rupture,
missing delivery, exhausted budgets and stale permits. CI does not invoke
any experiment runner.

The next milestones remain: learning/refuting variation rules, preregistered
random scenarios, a coupled learning tower, a physical R observation bridge,
and weaker sensor/latency assumptions. No randomized campaign or transistor
simulation has been run for R1.
