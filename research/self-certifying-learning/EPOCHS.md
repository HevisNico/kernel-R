# Finite-lived contracts and paid reconfiguration

The coordinator now selects and executes successive repair/scheduling phases
under different supplied contracts. It checks completion deadlines, preserves
a common handoff reserve, and carries terminal deficit forward. New deficit
caused by reconfiguration is paid from an explicit finite credit budget.

This layer consumes candidate contracts. It does not learn their physical
truth or guarantee that a fresh admissible candidate will always exist.

## Runtime interface

A `Policy` fixes one service requirement and a common handoff reserve. A
`Cursor` records calendar time, the propagated reserve lower bound, current
deficit debt and remaining switching credit. An `Offer` supplies a repair
configuration, a positive number of decisions, an issue time and an expiry.

At each boundary, `select` tries candidates in order. Put a preferred offer
first and prudent fallbacks afterwards. `run` executes the first eligible
phase and continues from its computed endpoint. Its result distinguishes
`complete` (all supplied requests processed) from `blocked` (no supplied
candidate passed). Refusal does not advance the modeled clock.

Eligibility requires all of the following:

- The configuration has positive net repair gain and enough usable capacity.
- Its service requirement equals the policy's fixed requirement.
- The entry lower bound, clipped to the new guaranteed capacity, is ready
  for the new repair buffer.
- The phase has a positive decision count and its contract is already issued.
- Its **completion**, not just its dispatch, lies before or at expiry.
- Its endpoint estimate preserves the common handoff reserve.
- Any increase in deficit fits within the remaining switching credit.

`select_sound` proves membership and admission for the actual selected offer;
`select_exists` proves a supplied admissible fallback will be found.
`select_none_iff` characterizes refusal exactly. These are arithmetic and
program-consistency guarantees, not authentication or physical validation
of the offers.

## Debt survives renewal

Let D be the old terminal deficit, D' the new configuration's entry deficit,
and B the remaining switching credit. The coordinator charges

`q = max(0, D' - D)`

and admits only when `q <= B`. It then spends q and executes the previously
proved phase ledger. The combined potential is **deficit + remaining credit**.
It cannot increase for free at a reconfiguration boundary.

For every generated prefix:

`terminal_debt + writes <= initial_debt + actual_switch_credit_spent + sum(U_i * wait_time_i)`

and

`remaining_credit + actual_switch_credit_spent = initial_credit`.

Consequently, writes are bounded by initial debt, initial switching credit
and the accumulated certified wait-loss budgets. Per-phase repair-time loss
is still accounted for inside each positive-net-dose condition.

This is not a restart of the proof with a fresh deficit allowance per phase.
`same_config_no_charge` proves that renewing the same configuration at its
own endpoint consumes no new switching credit. The old terminal deficit
remains in the next ledger. Clipping an estimate to a smaller guaranteed
capacity may increase deficit and is charged too.

Switching credit has reserve-tick units. It is a configured accounting
allowance, not a measured battery, energy cost or bound on physical drift.
The earlier hysteresis theorem still separately bounds search reopenings by
actual sampled parameter variation. No theorem identifies every contract
renewal with a search reopening, or derives this credit budget from drift.

## One calendar-time guarantee

`EpochSafety.composed_safe` lifts each admitted phase's existing safety and
endpoint theorem to one global state trajectory. The next phase starts
exactly at the previous phase's endpoint, using its propagated lower bound.
`phase_dates` verifies that every relative time in the phase lies inside its
contract's issue/expiry interval. The fixed service floor is preserved across
configuration changes.

`contiguous_clock` proves that elapsed phase time equals the change in the
calendar cursor. `elapsed_accounting` splits it into waiting time and write
time, with each phase's own latency. `no_zero_time_phases` bounds the number
of phases by elapsed ticks; zero-decision renewals cannot create an infinite
instantaneous dispatch loop.

These results require `Realizes`: the actual loss and delivered-dose laws
for the selected phases at their actual calendar times. Valid-looking dates
and inequalities do not manufacture a true future envelope. Boundary
computation and dispatch are instantaneous in this model; real observation,
reprogramming or scheduling delays must be covered by an added timed model.

If no offer qualifies, the service theorem ends at the blocked boundary.
It does **not** claim continued service while the real plant keeps leaking.
An expired fallback, insufficient handoff reserve or exhausted switching
credit can therefore prevent continuation. Sustained availability requires
an additional mechanism that supplies honest, timely, affordable offers.

## Checked two-contract example

Both configurations have service 10, dose 10, write latency 3, capacity 30
and maximum wait 4. The policy's handoff floor is 19. The initial reserve
lower bound is 20, with zero carried debt and two switching credits.

| Phase | Certified loss ceiling | Lease | Actions | Endpoint |
|---|---:|---|---|---|
| Preferred | 2 | Time 0 through 5 | Wait 2, then write | Time 5, reserve 20 |
| Prudent fallback | 3 | Time 5 through 11 | Write, then write | Time 11, reserve 22 |

At time 5, the first supplied candidate has expired at time 4 and is rejected.
The prudent fallback is selected. Its new deficit is two, so both switching
credits are consumed. The run contains three writes and two waiting ticks.
The reference state sequence for times 0 through 11 is
`[20, 18, 16, 14, 12, 20, 17, 14, 21, 18, 15, 22]`.

The finite checker in `EpochExamples` verifies **transition laws**, then the
general composition theorem proves service throughout the whole run. The
checker reads full reference-model state values; it is not a proposed sensor
and does not certify hidden physical parameters from the action log alone.

Negative examples reject a lease that expires before completion, a switch
with only one credit, a nominal phase that spends the handoff reserve, and
a request with no current offer. A same-configuration renewal has zero new
charge. These are kernel-checked examples, not a preregistered empirical
comparison or evidence about fabricated R cells.

## Final producer integration

[STATUS.md](STATUS.md) and `OfferFactory` now close the finite-prefix producer
integration: fresh bounded-error observations, a known future slew and fixed
hardware guarantees produce the supplied offers. The end-to-end theorem
derives their transition laws from actual-rate dynamics and delayed delivery.
It does not learn these physical guarantees or ensure perpetual availability.
Search decisions inside epochs, real sensing/dispatch costs and a physical
bound on affordable reconfiguration remain separate research obligations.
