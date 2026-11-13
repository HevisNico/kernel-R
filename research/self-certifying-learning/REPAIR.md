# Delayed repair and the conservative fallback loop

The new layer connects scheduling, delayed writes and a finite reserve
capacity. It proves two different guarantees: maintaining service from a
buffered start, and restoring a usable reserve after a finite explicit batch.
Restoration alone does not promise service during the batch.

## Model and admission conditions

Let `r` be the service floor, `U` a certified loss ceiling per tick, `tau` a
positive write duration, `d` a guaranteed dose delivered at completion, `K`
the guaranteed usable reserve capacity, and `C` a positive maximum wait.
All are natural ticks. The actual reserve trajectory is signed.

| Quantity | Definition | Role |
|---|---|---|
| Repair-time loss | `L = U * tau` | The dose cannot compensate for this loss before it arrives |
| Repair buffer | `G = r + L` | Starting here permits service through the complete write interval |
| Restart target | `T = G + U` | Enough buffer remains for at least one positive wait |
| Net gain | `q = d - L` | Strictly positive progress requires `d > L` |
| Conservative pulse endpoint | `min(K, x + q)` | Saturation is included in the propagated lower bound |

`Config.Valid` checks `tau > 0`, `C > 0`, `d > L` and `T <= K`.
`Config.Ready x` additionally checks `G <= x <= K`. The production
`ClosedLoop.choose` refuses invalid configurations and unbuffered starts.
This is intentional: it does not silently label a repair with temporary
service loss as uninterrupted operation.

Capacity has a precise scope. The controller caps its *estimate* at K; the
concrete reference plant saturates exactly at K. The general endpoint
contract also admits plants with at least that usable capacity and at least
the stated dose. Only a lower service specification is proved, not an upper
read-window limit for an analog circuit.

## Executable decisions

At a ready state with certified lower bound x, the loop calls the existing
scheduler with **G as the floor**, not r. If a positive wait c is affordable,
it waits that long and propagates `x - U*c`. Otherwise it commands one write,
waits tau ticks and propagates `min(K, x+q)`. It then repeats the same rule.

The reserve estimate is propagated using the known ceiling; this fallback
does not learn a new leakage rate or require a fresh measurement after each
write. Every estimate remains a lower bound under the realization contract.

`guarded_visit_handoff` connects the previous observation-level supervisor:
calling `Controller.visit` with G as its reserve floor leaves enough reserve
at its next visit to enter this fallback. A call with only r does not provide
that handoff guarantee. The loss envelope for the next phase must still be
established separately; an old finite-lived certificate is never extended.

## Guarantees and costs

- `execution_safe` proves service at **every discrete time**, including
  write interiors, over every finite generated execution. Its premises are
  per-tick loss bounds and delayed-dose endpoint laws, not assumed safety.
- `next_ready` preserves the buffer and capacity invariant. `returns_to_wait`
  proves that within `D + 1` decisions at least one positive wait occurs,
  where `D = max(0, T - x)`. There cannot be an endless write-only episode.
- `ledger_run` constructs the original potential ledger from the executable
  transitions. For every prefix, `writes <= D_initial + U * wait_time`.
  Repair-time loss has already been charged through net gain q; it is not
  omitted. The last saturating write may remove less than q deficit ticks,
  so the proof conservatively charges one tick per write.
- `clock_accounting` proves `elapsed = wait_time + tau * writes`.
  `time_progress` proves n decisions take at least n ticks. `clock_upper`
  proves they take at most `n * max(C, tau)` ticks.

These bounds do not count search, sensing energy or unrelated background
work. They are intentionally conservative, not optimal-dose or global-cost
claims. Persistent leakage can require indefinitely many repairs over an
unbounded lifetime; the bound applies to each finite prefix.

For a planned n-decision fallback epoch, `H = n * max(C, tau)` is a computable
horizon for acquiring the needed envelope. For example, a current honest
rate interval and a known future slew bound can supply a ceiling through H
using the earlier `rate_ceiling_sound` theorem. Admission must then be checked
with that ceiling. A ceiling established only through the next probe is
insufficient for an entire multi-write recovery. Changing configuration
between epochs requires a newly justified buffer and envelope.

## Explicit recovery with possible service interruption

`Repair.pulses` executes a prescribed number of saturated endpoint updates.
Any available budget Q satisfying `T <= x + Q*q` reaches the target.
The simple computable budget `max(0, T-x)` always suffices for valid integer
configurations. It may overestimate the required writes.

`recovery_endpoint` propagates a sound initial lower bound through delayed
write endpoint laws. `recovery_restores` proves that the target is reached
at `budget * tau` ticks. For initial `0 <= x <= K`, `recovered_ready` also
establishes a valid entry estimate for the service-preserving loop.

This batch is distinct from `choose`, which refuses unbuffered starts.
Calling the explicit batch allows service interruption; it needs actual
write availability and the same full-batch physical envelope. Negative
initial certified reserves, failed writes, actuator exhaustion and unbounded
rate jumps are outside this restoration theorem.

## Concrete executable witness

`RepairPlant.simulate` constructs a deterministic trajectory that realizes
the controller contracts: each tick loses U, a write adds its dose only at
completion, and the endpoint saturates at K. `simulate_realizes` proves
this for every admitted configuration and finite execution. The general
safety theorem therefore has a concrete realization, not just conditional
transition assumptions. Values after the finite execution are held fixed
by the witness; no post-horizon physical guarantee is asserted.

For `r=10, U=2, tau=3, d=7, K=20, C=4`, the buffer is 16, the restart target
18 and the net gain one. Starting at 16 produces two writes then one wait:

| Time | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| Reserve | 16 | 14 | 12 | 17 | 15 | 13 | 18 | 16 |
| Event | Write starts | Loss | Loss | Dose; next write | Loss | Loss | Dose; wait starts | Wait ends |

The action trace, values, seven elapsed ticks, two writes and full service
claim are checked by Lean. Starting at 12 instead admits a six-write explicit
recovery batch reaching 18 after 18 ticks, with no claim of service throughout.

Negative examples show why the admission conditions matter: starting a
write at bare service reserve 10 yields 8 one tick later; dose 6 exactly
matches repair loss and makes no progress; capacity 17 blocks the restart
target 18. The production policy refuses all three unsafe configurations or
starts. These are theorem examples and controls, not a preregistered
adaptive comparison or transistor-level evidence.

## Remaining work

[EPOCHS.md](EPOCHS.md) now supplies executable selection of finite-lived
contract offers, explicit switching charges, and a service theorem over the
composed calendar timeline. `OfferFactory` now constructs those envelopes from fresh bounded-error
observations and known slew/hardware guarantees; [STATUS.md](STATUS.md)
records the end-to-end result. Learning the physical bounds, ensuring perpetual
affordable renewal and modeling real sensing/dispatch delays remain open. The next physical bridge must
derive actual dose, timing, saturation, sensor and leakage guarantees. These
properties have not been established for R, continuous-time circuitry or
fabricated hardware by this package.
