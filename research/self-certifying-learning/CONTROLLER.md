# Observation-level supervisor: checked contract

This checkpoint implements a supervisor, not an adaptive physical learner.
It consumes scalar measurements with stated error bounds and a known bound
on future rate increase. It preserves the distinction between search memory,
current safety, and the cost of receiving fresh observations.

## Inputs and decisions

At each visit the supervisor receives a nonnegative leakage-rate interval
`[lo, hi]` and a nonnegative lower bound on current reserve. A configured
service reserve `r`, cap `C`, slew `s` and positive reopening granularity `g`
remain explicit. `fromMeasurement` constructs the input from a nonnegative
rate measurement with bounded absolute error and a signed reserve measurement
with bounded error. If the reserve lower bound is negative, it returns
`none`; conversion to natural ticks must not silently certify zero.

| Part | Executable rule | Justification required |
|---|---|---|
| Search memory | Keep the anchor interval unless `anchor.hi + g <= next.lo` or the reverse separation holds | The two intervals contain their actual sampled parameter values |
| Fresh safety | Always use `U = next.hi + s * C`, including when the anchor is retained | Over the next C ticks, actual rate at k is at most current true rate + s * k |
| Probe wait | Largest integer c in 1 through C with `U * c + r <= lowerReserve` | Reserve loses at most the actual rate per tick |
| Refusal | Return `none` if no positive wait is certified | Caller must repair or abstain; refusal is not successful service |
| Ideal restart | `max(0, r + U - lowerReserve)` unit writes suffice for a one-tick plan when C is positive | Writes are instantaneous, uncapped and add at least one certified tick each; no concurrent loss in this ideal sublemma |

The ceiling uses the entire cap, so it can be conservative. Maximality is
only among waits satisfying this particular ceiling, not among every safe
policy or under a global energy objective. C = 0 is handled by refusal;
zero rate and slew permit the full cap when the service reserve is present.

`visit` returns the retained/new anchor, a reopening flag and an optional
relative delay. `run` iterates the same executable transition over reports.
The timestamp source, actual observation dispatch and recovery on refusal
are outside this observation-level implementation.

## What the proofs connect

1. `measurement_honest` and `measurement_sound` transform stated measurement
   error bounds into interval containment and a signed reserve lower bound.
2. `rate_ceiling_sound` combines current interval containment with a known
   future slew bound. `enclosure_from_steps` derives the reserve enclosure
   from per-tick dynamics rather than assuming safety itself.
3. `visit_safe` certifies service at every discrete time through an accepted
   visit's selected delay. Each new visit needs current measurement and
   dynamics premises. It cannot extend an expired old certificate.
4. `charged_execution` constructs the original `Budget.Run` ledger from
   interval separation and the triangle inequality. A true sample-to-sample
   change is injected once; reopening resets the epoch's residual credit.
5. `run_reopening_bound` applies that ledger to the executable supervisor:

   `g * number_of_reopenings <= sum |theta[i+1] - theta[i]|`.

True values appear in the proof and evaluation record, never in the
controller's decision inputs. The right-hand side is actual sampled
variation, not variation of the noisy measurement centers, and it is not
claimed to be an observable certified number. It is also not automatically
the same quantity as accumulated physical leakage: variation of a rate and
integral of that rate have different meanings and units.

Every reopening uses a fresh epoch. Noise alone cannot reopen in a constant
honest world, even if interval widths change. Conversely, movement at least
`g + anchor_width + next_width` guarantees reopening at that visit. This
provides a sufficient detection condition, not a bound on detection time;
wide intervals may conceal a change indefinitely.

## The separation that matters

Search reopening is not the universal trigger for safe action. An unchanged
search anchor does not justify an old schedule or an old rejection verdict.
The supervisor refreshes its safety decision unconditionally from the latest
report. Two kernel-checked examples demonstrate why:

- Anchor [10, 10], next [12, 12], g = 5: no reopening, but at reserve 110 and
  required reserve 10 the wait falls from 10 to 8 (slew 0, cap 40).
- Anchor [10, 10], next [0, 200]: no proven separation, but the same reserve
  supports no positive wait. Refusal is necessary despite zero reopenings.

Periodic renewal/observation, safety refusal, repair, and search work are
separate costs. The reopening theorem bounds none of the others. Nor does
it justify retaining arbitrary decisions inside an epoch; those decisions
still need their own context-dependent validity proof.

## Remaining experiment and physical obligations

[REPAIR.md](REPAIR.md) now provides a conservative delayed-write loop, an
executable discrete plant witness and a guarded handoff theorem. It accounts
for finite dose, latency, saturation and leakage during repair. The earlier
ideal unit-write example is no longer the only repair result.

There is still no learned estimate of future slew, physical R recovery
theorem, automated envelope-switching policy or comparative performance result.
`EXPERIMENT_DRAFT.md` remains a design draft. Before running a comparison,
fix the experimental plant/sensor parameters, temporal ordering across
observations and control phases, baselines, costs and out-of-envelope trials
in an executable protocol. The proved fallback alone does not settle these
adaptive experimental choices.

In particular, a jump immediately after a probe that exceeds the declared
slew invalidates `visit_safe`'s premises. The earlier indistinguishability
counterexample still applies. No amount of search-memory bookkeeping can
recover information the sensor has not yet obtained.
