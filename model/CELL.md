# The physical kernel R

R is a three-input hybrid learning cell. This repository studies how R cells
learn through pulses, exchange responses and transmit an acquired cadence.
The q/m/z/b/E laws below describe one cell; wiring, source schedules, connection
delays, communication windows and optional settings copies are supplied by each
experimental protocol.

The [finite-chain protocol](CHAIN_PROTOCOL.md) fixes the inputs and routing for the main theorem.
The [experiment guide](../docs/EXPERIMENTS_AND_REPRODUCTION.md) documents the other protocols.

## Canonical pulses

A firing at time F emits the current p_F(t) = a·e^(−a(t−F)) on [F,F+1),
with a = ln 4, and zero otherwise. A raw pulse at an input port uses the
same waveform relative to its arrival time. Routing and separation
conditions belong to each protocol.

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

The [whole-execution counting theorem](../docs/EXACT_DOSE_COUNTING.md) sums
these identities over actual complete exposed sections, conditional on covers
accounting for every learning contribution.

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

Each protocol specifies its admissible states and any active raw pulses.
The auxiliary rest band is 1/40 ± 1/100000. The reusable Lean birth state
allows sensors in that READY band or at the lower end of ERROR. The
[finite-chain headline](CHAIN_PROTOCOL.md#birth-and-fabrication) requires
all sensors initially READY.

## Event semantics

- Thresholds are first crossings within the current mode. Continuous states stay continuous at
  external arrivals.
- When enclosures do not fix an order, **every** compatible non-strict order must be covered.
  Equalities may belong to several zero-duration linearizations. No priority comes from a
  floating-point sort.
- Cap contacts are monotone projections.
- Verification programs refuse unresolved roots or exhausted budgets; these are not success cases.

These model conventions and checked interval obligations do not by themselves
close the complete hybrid-execution-to-abstraction proof. For the constructed
common-birth finite-chain protocol, the
[geometric correspondence](../docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
is proved: model FIRE/MARK use the actual left history and a full-cell right
ODE germ, and every complete model history refines exactly to a complete native
history. The native-to-model converse preserves observations and ordered FIRE
lists. Every finite model prefix also has a history-preserving continuation to
any later finite horizon. These results retain the declared fixed ±0.3%/±10%
fabrication boxes, sources and delays; they do not assert the same correspondence
for arbitrary networks. The [Lean coverage guide](../proof/lean/README.md)
states the remaining obligations.

## Upstream provenance

R's reference laws originate from
[A22](https://github.com/HevisNico/a22-going-further/tree/269483eb2c6227b369cffb2c46f86eaae5272bb8).
[KERNEL_SHA256SUMS](../archive/spec-216-cells/kernel/KERNEL_SHA256SUMS) is an identity record for source files in
that upstream engine, not an executable-file inventory for this checkout.
The byte-identical [historical kernel guide](../archive/spec-216-cells/kernel/reference/A22_KERNEL_README.txt)
preserves the document used by the local-learning source manifest. Its old
relative paths and network description belong to that archived context.
