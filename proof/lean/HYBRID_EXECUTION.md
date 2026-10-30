# Physical execution semantics and exact ledgers

The execution-to-abstraction theorem remains open. This change reconstructs the
missing drafts as a checked foundation; it does not claim the learning, cadence,
or arbitrary-chain results are now complete Lean theorems of the physical model.

## Definitions

`KernelR/Hybrid.lean` defines a pulses-only finite network. Its state contains
all q/m/z/b/E coordinates, the main and three auxiliary modes, raw-current
origins and pending delivery tokens. Physical parameters are independent inputs
per cell and port. `PhysicalBox` states the independent ±0.3% or ±10%
fabrication family; `BirthState` states the common time-zero physical birth
family, with an explicit separate obligation to fix the pending source queue.
`field` implements the original equations, including the
complete work expression, energy gates and gain/recovery cap gates. Cap gates
are represented by the discontinuous integral ODE, not by a rounded dose.

A positive-duration `Flow` supplies a continuous path satisfying integral ODEs
on every prefix. Its discrete state is fixed. Strict pre-guard inequalities
prevent advancing past a main or auxiliary section; delivery urgency and raw
support prevent advancing beyond a queued arrival or raw-current end.

`Jump` permits only guarded section changes, delivery of an actual queued token,
or the end of an active raw current. All continuous coordinates and time are
preserved. A firing appends the supplied router's deliveries. An arrival removes
one specified occurrence from the pending list and requires a free receiving
port. The canonical current has half-open support, independently of main mode.
Consequently reopening admission retains any remaining input tail.

External source pulses must be present in the initial pending queue. There is
no external token-insertion event. Delayed routing is supplied by `Router`;
`CausalRouter` expresses causality but is not required by generic algebraic
ledger theorems. A protocol theorem must require it and prove the routing and
port-separation obligations. The current semantics has no staged-birth or
settings-copy operation.

An `Execution` is a finite sequence of flows and zero-time jumps. There is no
total event priority. The checked `simultaneous_fire_mark_orders` theorem
constructs both legal orders for simultaneous main-fire and auxiliary-MARK
guards. This example is not a proof of global confluence or of coverage of all
simultaneous events in the simulator or interval checker.

`CompleteThrough` requires reaching the horizon and discharging all enabled
jumps and due deliveries, including those exactly at the horizon. This is a
definition, not a general progress theorem. A complete, positive-duration silent
execution is constructed for any finite collection of resting cells. This
nonempty example does not establish existence for the training protocols.

## Established implications

`KernelR/Refinement.lean` derives from actual flow equations and jump rules:

- Final log-gain equals initial log-gain plus the integral of actual ERROR
  actuation, telescoped over every finite execution.
- Final recovery equals initial recovery plus the integral of the sum of all
  ports' actual MARK actuations, also telescoped over executions.
- Final queue length plus deliveries equals initial queue length plus issued
  tokens. Each arrival rule additionally consumes an actual list occurrence.
- Time is nondecreasing; jumps preserve every continuous coordinate and add no
  actuation. Emission records are produced only by actual fire jumps.
- Gain-cap, recovery-cap and energy gate closure gives zero corresponding
  instantaneous actuation.
- On an explicitly open ERROR span, the integrated dose is exactly
  `8 * (m_start - m_end)`, including across legal jump interleavings. Full
  endpoints imply `3/5`; partial endpoints remain real-valued.
- On an explicitly open MARK span, including legal jump interleavings, each port's dose is
  `(m_start - m_end)/2`; full endpoints imply `1/10`. Equating that port's dose
  with total recovery requires absence of other-port contributions. The full
  execution ledger retains every port's MARK integral, and total recovery is
  proved equal to their sum.
- A canonical input remains positive until its actual raw end; SLOW reopening
  does not erase it.

`ErrorOpen`, `MarkOpen`, exposure on a span and the full phase endpoints are
explicit premises of the dose consequences. They have **not** been derived
from the certified input calendars. The example `0.36` is an exact partial-dose
calculation, not a constructed reachable training trajectory.

## Connection to finite-chain composition

The emission ledger is now exposed as `Execution.signal`, a `Chain.Signal`
constructed from actual fire jumps. Its count is the exact length of that
cell's filtered emission list. `hasPacket_of_emission_witness` connects this
signal to the interface introduced by PR #6, retaining both exact-count and
all-date obligations. It does not supply the missing leaf or relay witness.
The base includes PR #6's packet induction and both N-cell endpoint certificates.

## Obligations still required for the requested theorem

1. Review and instantiate this semantics with the physical parameter and birth
   families and the actual supplied protocols, including staged births where
   relevant. Relate FAST dynamics and routing to the same canonical output.
2. Derive mode-local solutions and uniqueness from the integral equations, then
   prove first-crossing and phase-endpoint properties.
3. Prove energy and cap invariance, auxiliary separation, port non-collision,
   and all required gate chronologies for those executions.
4. Establish sound enclosure membership for real exp/log expressions and actual
   trajectories. Exact rational endpoint comparisons alone are insufficient.
5. Derive the four physical pulse cases, including combined MARK/ERROR, partial
   and clipped doses, raw tails and absence of extra firings.
6. Prove protocol execution existence, extension/progress, finite-event or
   non-Zeno bounds and horizon saturation for all compatible simultaneous orders.
7. Lift the resulting physical theorem through preparation, the cadence cascade
   and the packet induction for every finite chain.

No theorem in this change assumes a recorded pulse-case word or dose counter.
There is also no theorem asserting the complete physical-to-abstract result.
The existing certificates, manifests, recorded evidence and prototype ZIP are
unchanged, and retain their previous scope and provenance.

## Validation

Use the pinned Lean/Mathlib versions and the standard project workflow:

```sh
lake build
lake env lean Audit.lean
python scripts/check_sources.py
python scripts/generate_evidence.py --check
python scripts/check_negative.py
python scripts/check_hybrid_negative.py
```

The new negative checks first compile physical positive controls, then require
Lean to reject firing below threshold, a nonconsuming arrival, a positive ERROR
actuation at a closed cap or energy gate, rounding a partial dose to a full dose,
and deleting an unfinished raw tail. Build errors cannot count as successful
negative checks unless the corresponding positive control compiles.
