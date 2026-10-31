# Learned-state closure and conditional indefinite operation

This extension supplies physical and analytic building blocks for a future
indefinite-operation theorem. **It does not yet prove that an R network trained
from birth will respond forever. There is no proved instance of `PulseContract`
in this repository.**

## Results and boundaries

| Module | Proved result | Remaining physical premise |
|---|---|---|
| `KernelR/HybridFuture.lean` | A complete silent execution of any duration from every state in `LearnedRest`; the section, gains, recovery and reserve bounds are preserved | Entry into this learned section |
| `KernelR/HybridFuture.lean` | Later source tokens can be placed in an existing execution's initial queue without changing its physical ledger | Every added token must be due at or after that execution's endpoint |
| `KernelR/HybridFuture.lean` | Every earlier horizon of a complete finite execution has a complete execution, including all enabled zero-time events at that horizon | An existing complete execution extending to that horizon |
| `KernelR/LearnedResponse.lean` | The three-dose gain and prepared recovery fit the learned section; a unique reference first contact is in `(0.3,0.9]`; constant-recovery return is before `7.5` | Full doses, actual mode ordering and constant recovery must be established by the protocol proof |
| `KernelR/LearnedResponse.lean` | An observed single-input READY firing has the reference latency for its actual gain | The stated READY span, exact initial rest, one fresh raw input and no ERROR on that port |
| `KernelR/Indefinite.lean` | Compatible responding execution prefixes reach unbounded times; a complete execution exists at every finite horizon of an arbitrary sufficiently separated input schedule | `PulseContract`: actual one-input execution, learned-domain closure, exact firing count and fixed latency |
| `KernelR/FutureControls.lean` | A nonempty learned section and positive-duration idle execution; concrete counterexamples to dropping the positive gap, strengthening the energy floor, allowing a weak gain, or ignoring a token due at an endpoint | No responding-cycle witness is supplied by these controls |

All statements use the fixed-parameter, canonical-amplitude operational field of
`Hybrid.lean`. They do not instantiate the conditional drift/noise/amplitude
results of the `Robust` modules.

## The learned section

`LearnedRest` requires every main and auxiliary mode READY, no active raw
current, an empty pending queue, exact main rest `q=0.1`, auxiliary charges
within `1e-5` of `0.025`, and reserve in `[50,100]`. The selected active gain is
in `[1.8,1.9]`, recovery is in `[0.17,0.2]`, and every log-gain is below or at
its physical cap. The section permits different parameters and states in every
cell and port.

`LearnedDomain` additionally fixes **all** log-gains and recovery coordinates
to a reference snapshot. Auxiliary charges and energy need not be identical
between rounds. Waiting evolves them by their actual ODEs; it does not reset
them. The real inequalities `three_dose_gain_in_section` and
`prepared_recovery_in_section` connect the gain/recovery ranges to the exact
updates in the existing slow-protocol arguments. They do not establish the
other entry coordinates or the reachability of that protocol in Lean.

## What the physical idle proof constructs

With no current and every unit READY, the actual work is zero. The candidate
trajectory is

```
q(t) = 0.1
m(t) = 0.025 + (m(s)-0.025)*exp(-(t-s)/2)
E(t) = 100 + (E(s)-100)*exp(-10*(t-s))
z(t) = z(s),  b(t) = b(s).
```

Lean proves its derivatives equal the operational field, obtains every prefix
integral equation by the fundamental theorem of calculus, verifies all strict
guards and constructs an actual `Flow` and `Execution`. Zero waiting time is
handled by `Execution.nil`. The invariant holds for every allowed initial
sensor charge and reserve, not just for a single equilibrium sample.

## The real analytic bounds

The exponential estimates in `LearnedResponse` follow from Mathlib's proved
finite-series bounds. The response is bounded above by `a*t`, and its value at
`t=0.9` is proved strictly greater than `0.5`. These bounds establish a first
threshold contact for every gain in `[1.8,1.9]`, and uniqueness follows from
the first-contact property. Continuity gives equality with the threshold.
The return bound uses the actual real `log(5/2)`.

These are proofs of expression bounds; they do not infer the desired sequence
of hybrid modes. In particular, the single-input response lemma cannot be used
through an ERROR/raw overlap that changes the gain.

## From one input to compatible future prefixes

`PulseContract` is an ordinary theorem parameter containing the following
remaining obligation: from **every** state in the learned domain, an input
queued at that state's date admits a finite actual execution that

1. emits exactly one event per cell at the supplied fixed cell latency;
2. returns to the learned domain at the supplied settling duration `D>0`;
3. keeps every such latency nonnegative and strictly below `D`.

The future schedule may be irregular: it only requires
`input(k)+D <= input(k+1)`. The physical idle theorem supplies the waiting
between cycles. Recursive choices retain the actual state left by each cycle.
The next cycle never starts from an independently chosen copy of the section.

There is no infinite pending list and no extra source-injection jump. Prefix
`k` starts with the first `k` external source tokens already queued. To extend
it, the next token is prepended to the earlier execution; its due date is
checked against that execution's endpoint. `withFuture_ledger` proves the
earlier actuations and emissions unchanged. Queue order is not an event
priority. Every delivery still consumes an actual occurrence of a queued token.

For the constructed prefixes, every cell's complete emission list is exactly

```
[input(0)+latency(i), ..., input(k-1)+latency(i)].
```

This excludes missing and additional emissions in those prefixes. Their terminal
times are unbounded. `complete_at_every_horizon` then cuts a sufficiently long
prefix at any requested finite horizon, processing guards and deliveries at the
cut rather than leaving an enabled endpoint event unhandled. Positive spacing
also proves that only finitely many source indices can occur at a bounded time.
The selected restriction extends strictly beyond the requested horizon and is
proved to contain every source dated at or before it. This matters when the
next input is due exactly at a preceding cycle's settling date.

The result constructs compatible responding prefixes **conditional on the
existential one-cycle contract**. It does not yet prove that every admissible
complete execution of the physical network has that behavior. A universal
one-cycle refinement, or appropriate uniqueness/coverage results for compatible
event orders, is needed for that stronger guarantee.

## Next physical obligations

1. Construct the one-input hybrid cycle from the learned section, including
   auxiliary crossings, raw end, FAST/SLOW exits and all compatible event orders.
2. Derive the chronology that suppresses further gain/recovery updates and
   excludes extra firings; prove the selected section closes under that cycle.
3. Instantiate routing, fixed wire delays and a sufficient network settling
   duration for a finite chain, then instantiate `PulseContract`.
4. Prove the universal cycle refinement and connect the existing birth/training
   protocol to this learned domain.

The added theorem therefore closes the *waiting, compatible-prefix construction
and arbitrary-horizon extraction* parts of the indefinite-operation argument.
It leaves the local responding cycle and birth-to-learned execution as explicit
physical work, rather than treating them as consequences of finite certificates.

## Validation

The normal `lake build` and `lake env lean Audit.lean` import every new module
through `KernelR.lean`. `FutureControls` includes positive controls and proofs
of the negations of overstrong claims. These are concrete counterexamples, not
only failed attempts to apply a theorem with a mismatching type. Existing
source/evidence checks, physical controls and Python suites remain unchanged.
