# The physical kernel R

R is a three-input hybrid learning cell. This repository studies how R cells
learn through pulses, exchange responses and transmit an acquired cadence.
The q/m/z/b/E laws below describe one cell; wiring, source schedules, connection
delays, communication windows and optional settings copies are supplied by each
experimental protocol.

## Implementations and reference material

- [Single-cell numerical engine](../experiments/reciprocal/engine.py).
- [Three-cell network simulator](../experiments/reciprocal/simulate.py) and its
  [experimental guide](../experiments/reciprocal/README.md).
- [Finite-chain numerical checks](../experiments/composition/run.py) and the
  [N-cell composition theorem](../proof/reciprocal_composition/THEOREM.md).
- [Robust-chain research](../research/robust/README.md), with separately stated
  drift, disturbance and received-amplitude assumptions.

The [original model](../model/full_model_reference.md) and
[A22 specification snapshot](../model/CURRENT_SPEC.md) retain the upstream
definition and historical network/calendar context. The theorem and experiment
guides define the initial families and protocols used in kernel-R.

## Topologies and sources in this repository

| Setup | Supplied topology and protocol | Scope |
|---|---|---|
| Reciprocal prototype | Three living cells A, B and C; staged teaching and return links; nominal connection delay 0.35; later open exchanges | Numerical scenarios include pulses only and optional external settings copies. The local and cadence proofs cover their declared pulses-only prefixes. |
| Cadence composition | A finite directed leaf-to-root chain; a prepared source schedule and explicit path-jitter budget | The [packet theorem](../proof/reciprocal_composition/THEOREM.md) specifies the preparation, source length and delay assumptions for each N. |
| Robust prepared chains | Directed chains with bounded drift, disturbances and received-amplitude variation | The [robust theorem](../research/robust/THEOREM_N.md) uses its own prepared section and cadence budget; it is separate from the fast period-4 packet protocol. |

The upstream A22 18-by-12 graph and zero-delay contacts are historical network
choices, not properties of an individual R cell or a common topology imposed
on these experiments. Port roles such as local experience, teaching and feedback
are assigned by the bench.

A firing at time F emits the canonical current
p_F(t) = a·e^(−a(t−F)) on [F,F+1), with a = ln 4. The supported protocols require
non-overlapping raw pulses on each port; routing and separation conditions are
part of the individual result.

## Constants

| Fixed constants | Value |
|---|---|
| a | ln 4 |
| κ | 1/2 |
| r (main rest charge) | 1/10 |
| r_m (auxiliary rest charge) | 1/40 |
| main and auxiliary thresholds | 1 |
| actuation factors | 8 (gain), 1/2 (recovery) |
| b_max | 11/10 |
| energy pump | E′ = 10(100 − E) − W |
| nominal initial gains | (3/10, 6/5, 3/10) |
| nominal initial recovery b₀ | 2/25 |

The five **per-port parameters** are chosen independently for each cell and port.
The base local and cadence theorems use fixed-in-time values in their declared
relative boxes, including ±0.3% and ±10%. These parameter boxes are assumptions
of particular results, alongside their state sections, schedules and link
conditions. The robust research module separately defines permitted histories,
disturbances and received-amplitude variation.

| Parameter | Nominal value |
|---|---|
| gain cap C_i | 4 |
| mark rate L_m,i | ln(5/4)/(1/50) |
| silent rate L_s,i | ln 8/(53/50) |
| error rate L_e,i | ln 4/(3/20) |
| auxiliary input gain M_i | (1 − r_m)/h(1/50) |

Here h(u) = a/(a − κ)·(e^(−κu) − e^(−au)) is the response of a READY charge to one canonical
pulse.

## State of a cell

- the main charge q;
- three auxiliary charges m_i and three log-gains z_i, with gains g_i = e^(z_i);
- the recovery variable b and the energy reserve E;
- a main mode P ∈ {READY, FAST, SLOW} and, for each port, an auxiliary mode
  H_i ∈ {READY, MARK, SILENT, ERROR};
- the incoming and outgoing currents still active.

## Main unit

- **READY**, with admission open: q′ = κ(r − q) + Σ_i g_i p_i(t).
- At the first upward crossing of q = 1, q is set to 1, admission closes and **FAST** begins:
  q′ = −a·q. The cell emits p_F for exactly one time unit. FAST ends at q = 1/4, which takes
  exactly 1 time unit.
- **SLOW**: q′ = −b(t)·q, until the downward crossing q = r. READY then resumes with q = r exactly.
  The return date is not prescribed: it follows from b.
- FAST and SLOW have the same admission and actuation gates.

## Auxiliaries and plasticity

Auxiliary i sees the raw current of its port even while the main unit is protected. While READY,
m_i′ = κ(r_m − m_i) + M_i p_i. Its first upward crossing of 1 starts the cycle below. Each section
ends exactly at the stated charge; at r_m the auxiliary is READY again.

| Mode | Equation | Ends at | Useful current |
|---|---|---|---|
| MARK | m_i′ = −L_m,i m_i | 4/5 | v_m,i = L_m,i m_i |
| SILENT | m_i′ = −L_s,i m_i | 1/10 | 0 |
| ERROR | m_i′ = −L_e,i m_i | r_m | v_e,i = L_e,i m_i |

While E > 0, the actuations are

    z_i′ = 8 v_e,i · 1[P = READY] · 1[z_i < ln C_i]
    b′   = ½ Σ_i v_m,i · 1[P ≠ READY] · 1[b < 1.1]

Both are monotone and are projected exactly onto their caps. The full-dose
identities below require the energy gate to remain open and no cap contact:
- A whole ERROR section received while the main unit is READY adds exactly Δz = 8(0.1 − 0.025) = 0.6,
  whatever L_e,i is.
- A whole MARK received under protection adds Δb = (1 − 0.8)/2 = 0.1.
- A partial reception contributes the integral over its true endpoints.

The cell consults no target, counter or software failure flag.

## Energy

E′ = 10(100 − E) − W. The work W is non-negative:
- in the main unit, the admitted current when READY, a·q when FAST, and 1.1 when SLOW;
- the currents admitted by READY auxiliaries;
- the drains of protected auxiliaries;
- the actuation movements.

For a result's admissible parameter and state family, the proof checks a bound
of the form W ≤ (3C + 3M + 1)a + 1.1 + 4.5 L_m + 2.4 L_e < 500.
When that bound holds and E starts in [50,100], this interval is invariant and
the power gates stay open. The bound and any added disturbance assumptions
must be justified for the particular theorem.

## Initial and prepared sections

Initial states are specified by each theorem, rather than by the topology.

The [birth-to-section theorem](../proof/reciprocal_entry/THEOREM.md) uses a READY
birth family: the main unit and all auxiliaries start READY, charges and
log-gains have the stated 1e-5 perturbations, b is near 0.08 and E is in [50,100].
The [cadence](../proof/reciprocal_cadence/THEOREM.md) and
[chain](../proof/reciprocal_composition/THEOREM.md) results state their own birth
calendars and preparation protocols.

The [local feedback theorem](../proof/reciprocal_learning/THEOREM.md) instead
starts from an explicit prepared section with b near 0.18 and no active currents.
Prepared robust chains have their own section and noise assumptions.
Residual initial ERROR phases permitted in the archived A22 family are not
automatically included in the current READY birth theorems.

## Event semantics

- Thresholds are first crossings within the current mode. Continuous states stay continuous at
  external arrivals.
- When enclosures do not fix an order, **every** compatible non-strict order must be covered.
  Equalities may belong to several zero-duration linearizations. No priority comes from a
  floating-point sort.
- Cap contacts are monotone projections.
- Verification programs refuse unresolved roots or exhausted budgets; these are not success cases.

These model conventions and checked interval obligations do not by themselves
close the complete hybrid-execution-to-abstraction proof. The
[Lean coverage guide](../proof/lean/README.md) states the established lemmas and
remaining correspondence obligations.

## Upstream provenance

R's reference laws originate from
[A22](https://github.com/HevisNico/a22-going-further/tree/269483eb2c6227b369cffb2c46f86eaae5272bb8).
[KERNEL_SHA256SUMS](KERNEL_SHA256SUMS) is an identity record for source files in
that upstream engine, not an executable-file inventory for this checkout.
The byte-identical [historical kernel guide](reference/A22_KERNEL_README.txt)
preserves the document used by the local-learning source manifest. Its old
relative paths and network description belong to that archived context.
