# Cell-family structure and nominal protocol conditions

This document separates two claims:

1. Structural results can quantify over the constants of an R cell, with the
   sign, ordering and exposure hypotheses needed by the particular theorem.
2. The existing cadence protocol has numerical margins that were proved for
   the original constants. Its whole-network result is not established merely
   by placing new constants in a record.

The parameterized layer is under [`KernelR/Family`](../proof/lean/KernelR/Family/).
[`Constants`](../proof/lean/KernelR/Family/Constants.lean) separates the values
from `Admissible`. The original definition is the `nominal` specialization.
[`Model`](../proof/lean/KernelR/Family/Model.lean) carries those constants into
the vector field, guards and operational transitions. The old protocol and its
certificate data keep their original meaning.

## 1. Constants and the nature of their dependencies

| Quantity | Nominal value | Structural role | Additional protocol dependence |
|---|---:|---|---|
| Main threshold `threshold` | 1 | READY-to-FAST guard | Main response must cross it within the required latency bracket |
| Main FAST exit `fastExit` | 1/4 | FAST-to-SLOW guard | `log(threshold/fastExit)/a` must fit the chosen chronology |
| Main rest `rest` | 1/10 | SLOW-to-READY guard and READY equilibrium | Recovery must finish before, or after, selected inputs as required |
| Auxiliary threshold `auxThreshold` | 1 | READY-to-MARK guard | Auxiliary root bracket and crossing direction |
| MARK exit `markExit` | 4/5 | MARK-to-SILENT guard | MARK completion must occur in its required main-mode window |
| ERROR entry `errorLevel` | 1/10 | SILENT-to-ERROR guard | ERROR exposure or protection must match the chosen pulse case |
| Auxiliary rest `auxRest` | 1/40 | ERROR-to-READY guard | Whole auxiliary cycle must fit between inputs |
| Gain factor `gainFactor` | 8 | ERROR increment equals factor times charge drop | Learned gain must lie in firing bands and remain below its physical cap |
| Recovery factor `recoveryFactor` | 1/2 | MARK contribution equals factor times charge drop | Learned recovery must produce the required return windows and stay below cap |
| Decay `a` | log 4 | FAST flow and emitted pulse shape | Numeric response roots and FAST/pulse-duration synchronization |
| READY leak `kappa` | 1/2 | Dissipative READY main/auxiliary flow | Response bounds, residual tails and strict root brackets |
| Pulse width `pulseWidth` | 1 | RAW support and expiry | Nonoverlap, raw-tail bounds and deadlines expressed in pulse ages |
| Recovery cap `recoveryCap` | 11/10 | Monotone actuation gate | Entire counted MARK sections must retain headroom |
| Energy pump `energyRate`, target `energyTarget` | 10, 100 | Reserve dynamics | Work bound must support a positive invariant reserve interval |
| SLOW work `slowWork` | 11/10 | Reserve work term | Enters the reserve estimate |

The auxiliary rates `Lm`, `Ls`, `Le`, input gain `M` and gain cap `C` are
per-port fabrication parameters. In the existing `PhysicalBox`, only these
five values per port vary independently in the specified +/-0.3% or +/-10%
boxes. Thresholds, the two actuation factors and the pump constants do not
vary in that old result. The family layer makes these different dependencies
visible rather than silently enlarging that fabrication box.

### Structural formulas do not require the nominal numbers

On a fully exposed ERROR interval, the balance is

`Delta z = gainFactor * (m_in - m_out)`.

On a fully protected MARK interval, the contribution to recovery is

`Delta b_port = recoveryFactor * (m_in - m_out)`.

For complete admissible sections, the two per-section doses are therefore

`errorDose = gainFactor * (errorLevel - auxRest)` and
`markDose = recoveryFactor * (auxThreshold - markExit)`.

These identities need matching drain/actuation currents and the actual exposure
conditions. They do not require `a=log 4`, `kappa=1/2`, a chosen input period,
or a response-latency bracket. Positivity of a dose is needed when recovering a
unique integer count from that dose; it is a distinct assumption from the
balance identity. The structural confluence and flow-uniqueness statements have
their own hypotheses in the family modules; admissibility alone is not a proof
of existence, open energy gates, or progress of a new numerical protocol.

## 2. Numerical conditions required by the nominal teaching/cadence argument

The following is a readable classification of the existing sufficient
conditions. It is not a claim of necessity or a minimal characterization.
For every historical certificate inequality, its exact name and both bound
keys are listed in the [generated catalogue](parametric_protocol_conditions.json).
The original certificates store the actual outward numerical intervals.

Let `w` be pulse width. For positive auxiliary rates, the ideal phase durations
are `log(auxThreshold/markExit)/Lm`,
`log(markExit/errorLevel)/Ls` and `log(errorLevel/auxRest)/Le`.
With auxiliary crossing date `tau`, denote the three cumulative boundaries by
`t_mark`, `t_error` and `t_finish`. An interval proof uses lower and upper bounds
on each of these quantities, not an assumed common date for all devices.

For a constant admitted gain and a pulse age `t` before the first main event,
write `Q(t) = rest + x*exp(-kappa*t) + g*h(t)`, with the appropriate pulse
response `h`. The original closed form is
`h(t) = a/(a-kappa)*(exp(-kappa*t)-exp(-a*t))`.
Its use at new constants requires treating `a=kappa` separately or imposing
`a != kappa`; structural dose identities do not have this restriction.

| Obligation family | Sufficient inequality or required case distinction | Existing numerical witness / source |
|---|---|---|
| Initial auxiliary and first contact | `m_birth < auxThreshold`; response below threshold at `tau_lo` and above at `tau_hi`; positive derivative on the bracket | `tau` in `(0.015,0.03)`; `aux.root_*` in composition verifier |
| Auxiliary reset before next input | `w < t_finish_lo` and `t_finish_hi < next_input_gap_min` | `aux.finish_after_raw`, `aux.finish_before_fastest_next_input` |
| Weak input has no main event | A bound for the whole trajectory, including the changing gain and residual RAW overlap, remains below `threshold` | `leaf.weak_{0,1,2}.no_fire`; local `silent_*_no_first_crossing_even_with_overlap` |
| Strong first contact | `Q(root_lo) < threshold < Q(root_hi)` with the corresponding monotonicity/first-contact proof | `*.lower_sign`, `*.upper_sign`, `*.increasing` in composition verifier |
| MARK precedes ordinary firing | `t_mark_hi < root_lo` | `*.MARK_precedes_fire` |
| Firing precedes ERROR | `root_hi < t_error_lo` | `*.fire_precedes_ERROR` |
| Entire ERROR protected on an ordinary response | `t_finish_hi < earliest_main_return` | `*.ERROR_entirely_protected`, including the changed-recovery case |
| Protected teaching input lands in SLOW | Previous FAST has ended, but the accumulated recovery drain has not yet reached `log(fastExit/rest)` | `*.past_FAST`, `*.still_in_SLOW` |
| Complete protected MARK | `t_mark_hi < reopen_lo` | `*.entire_MARK_protected` |
| MARK-only versus MARK-then-ERROR | Either `t_finish_hi < reopen_lo`, or `reopen_hi < t_error_lo` | Separate `first_miss` and `second_miss` obligations, not an interchangeable dose word |
| No second firing on an unfinished raw tail | The post-return trajectory bound stays below `threshold` | `relay.second_miss.no_refire_from_tail` |
| Recovery before subsequent input | Latest return is before the earliest next arrival | `steady_tail.ready_before_every_input`, `relay.transient_return_before_next_input` |
| Gain and recovery headroom | Every attained log-gain is below `log(C_port)` and recovery is below `recoveryCap` | `caps.final_gain`, `caps.final_recovery`; current Lean final-headroom theorem |
| Positive reserve | An actual work bound supports a positive invariant reserve interval | Nominal `W < 500`, with pump `E'=10*(100-E)-W` and `E` in `[50,100]` |
| Packet shape is preserved | New prefix and settling gaps remain in the allowed packet intervals | `output.first_new_slow_*`, `output.second_new_slow_*`, `output.settling_upper` |
| All remaining events finish by the horizon | A cell-latency bound, per-hop delay-plus-latency bound and final-return bound fit the terminal formula | `horizon.cell_latency`, `horizon.hop_budget`, `horizon.last_return_budget` |

For a different pump `E'=rho*(E_star-E)-W`, a sufficient lower-boundary
condition is `W_max <= rho*(E_star-E_min)`; an upper boundary additionally
uses nonnegative work and `E_max >= E_star`. This algebra explains the role
of the nominal number 500. It is not, by itself, a new all-family work estimate.

The equality `exp(-a*w)=fastExit/threshold` holds at the nominal constants,
making FAST duration equal RAW width. The structural transfers do not require
that synchronization. Any protocol proof relying on it must replace it with an
explicit equality or with chronology bounds appropriate to the new constants.

## 3. Current universal Lean protocol: interfaces outside the historical index

The certificates below are historical written-proof layers. The current
common-birth universal Lean proof also contains direct real estimates and
different response envelopes. In particular, its broad high-gain latency
interface `[4/25,13/50]` must not be confused with the narrower historical
certificate brackets such as `[0.24,0.25]`.

| Current source and interface | Explicit condition / role | Category |
|---|---|---|
| [`Hybrid.lean`, `PhysicalBox`](../proof/lean/KernelR/Hybrid.lean) | `epsilon` is `3/1000` or `1/10`; independent nominal-relative boxes for `C,Lm,Ls,Le,M` | Numeric physical family |
| [`Hybrid.lean`, `BirthState`](../proof/lean/KernelR/Hybrid.lean) | Main rest, recovery, auxiliary rest and log-gain bands of radius `1/100000`; energy `[50,100]` | Numeric birth family |
| [`HybridBirthCadenceChain.lean`, `birth_cadence_chain_exists`](../proof/lean/KernelR/HybridBirthCadenceChain.lean) | `K >= 4*(n+1)+12`; nonnegative link radii; path sum `<=3/20`; `3/10+sigma <= centre <= 2/5-sigma`; errors bounded at every real time | Numeric resource / wire conditions |
| [`HybridPreparedCadenceChainDomain.lean`, `PreparedCadenceChainDomain`](../proof/lean/KernelR/HybridPreparedCadenceChainDomain.lean) | Prepared clock `1599/10`, source dates `160+4*k`, exact READY charge and own prepared gain bands, physical and RAW-valid states | Mixed structural and numeric entry interface |
| [`HybridLocalCadenceBudgetReceiver.lean`, `local_cadence_budget_receiver_exists`](../proof/lean/KernelR/HybridLocalCadenceBudgetReceiver.lean) | `J<=3/20`, tail length `L>=5`, initial `log(3/10)+9/5 +/-1/100000`, first source strictly later, terminal at least last source `+37/10` | Numeric receiver margins |
| [`HybridCadenceChainEnvelope.lean`, `CadencePacketEnvelope.propagate`](../proof/lean/KernelR/HybridCadenceChainEnvelope.lean) | Low latency `[65/100,66/100]`, high latencies `[4/25,13/50]`, first high latency `<=` rest high latency, wire delay `[3/10,2/5]` | Numeric composition envelope |
| [`HybridResponseBounds.lean`](../proof/lean/KernelR/HybridResponseBounds.lean) | `response(9/10)>=5001/10000` and `response(t)<=3/4` on ages `[0,1]` | Direct real proofs, not certificate rows |
| [`HybridFiniteChainDoseCounting.lean`, `terminal_learning_headroom`](../proof/lean/KernelR/HybridFiniteChainDoseCounting.lean) | Final memories remain strictly below their own caps; reserve and monotonicity then supply intermediate gate conditions | Numeric-to-structural discharge |
| [`CrossingChainHeadline.lean`](../proof/lean/KernelR/CrossingChainHeadline.lean) | Reuses the birth, box, source and wire budgets; crossing witnesses and outcomes are conclusions | Model-facing nominal headline |

Exact source fragments and hashes for these selected interfaces are recorded in
the generated catalogue. This is a coverage map, **not an exhaustive transitive
dependency analysis** of every numeric lemma in the universal proof. No list of
historical certificate rows should be presented as such an analysis.

## 4. Reproducible catalogue and validation

Run from the repository root:

```sh
python -B tools/parametric_protocol_conditions.py
python -B tools/parametric_protocol_conditions.py --check
python -B tools/parametric_protocol_conditions.py --check --replay
```

The generator authenticates the current checker/producer sources against each
certificate's source hashes, rejects duplicate names or malformed/non-exact
intervals, and checks all published endpoint comparisons using rational
arithmetic. It records the source expressions that instantiate those comparisons
through helpers and loops. No interval-bound arrays are duplicated in the index.

| Historical certificate layer | Comparisons per box | Enclosures per box | Distinct scope |
|---|---:|---:|---|
| Local prepared feedback | 31 strict | 103 | Two cells from a supplied prepared section |
| Birth entry and composition | 55 strict + 4 closed inclusions | 170 | READY births through the historical horizon 459.9 |
| Staged cadence cascade | 1,030 strict | 2,533 | Historical three-cell cascade through 789.9 |
| Uniform finite-chain composition | 81 strict + 12 separately checked polynomial identities | 176 | Written local packet contract and induction |

The two boxes share **1,201 named comparisons**; there are **2,402 published
comparisons across all eight certificates**. `--replay` invokes the existing
independent integer-arithmetic verifiers, including their authenticated
predecessor checks, rather than executing source expressions from the index.
Both supported boxes have been replayed successfully for all four layers.

Endpoint replay checks the sufficient numerical inequalities and the specified
source/protocol identities. It does not by itself verify the handwritten
hybrid arguments, rebuild Lean, or validate a changed set of family constants.

## 5. Claim supported by this separation

The family results identify which statements depend only on shared
drain/actuation structure, exposure, signs and event-update rules. The tables
above identify additional requirements used to obtain the particular learned
cadence, return windows, packet transformation and terminal horizon.

Accordingly, the defensible extension is: **structural lemmas quantify over a
family of cells; the established cadence theorem remains their nominal
protocol specialization.** A protocol for a nonnominal member requires its own
crossing, headroom, reserve and chronology discharge. Merely checking the
structural order assumptions does not supply that discharge.
