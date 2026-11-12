# Conditional circuit-to-kernel dose bridge

This package starts the formal connection between the circuit of PR #103
and Kernel R. It imports the existing `KernelR.Doses` theorem
`drain_integral`. It proves a charge-to-dose correspondence and explicit
error budgets. It does **not** prove that the transistor netlist satisfies
the hypotheses, or identify a SPICE run with a kernel execution.

## What is connected

On a write window `[s,t]`, let `Qs` be the sensor charge and `Qm` a storage
coordinate, with balances

```
Qs' = -Is,   Qm' = -Iw.
```

The currents are integrable and the two charge paths satisfy the derivative
contracts in `ChargeWindow`. A positive coefficient `k` converts a decrease
of `Qm` to an increase of log-gain. For a constant feedback capacitor and
an affine calibration `z = z_ref - beta * Vmem`, take `Qm = Cf * Vmem`
and `k = beta / Cf`. The summing node must be fixed for the ideal capacitor
interpretation; its motion and other parasitic effects must be accounted
for in the effective write current or a residual bound. `Qm` is not an
unqualified identification with the signed charge on a particular plate.

The existing kernel integral theorem yields

```
Delta z = k * (Qs(s) - Qs(t)) + k * residual,
residual = integral(Iw) - integral(Is).
```

Consequently:

| Circuit contract | Formal consequence |
|---|---|
| `Iw = Is` throughout the exposed window | The dose depends only on sensor endpoints, not discharge speed |
| `Iw = 0` throughout the protected window | The storage-derived log-gain step is zero |
| Absolute transferred-charge residual at most `eta` | Dose error at most `k * eta` |
| Absolute integrated write current during protection at most `eta` | Protected drift at most `k * eta` |
| Local error bounds on a contiguous log-gain sequence | Total error bounded by the sum of the local budgets |

With `Qs = Cs * Vs`, the exposed dose is
`beta * Cs / Cf * (Ventry - Vexit)`. Projecting the sensor coordinate as
`m = (k/8) * Qs` gives the kernel's observable identity
`Delta z = 8 * (m_entry - m_exit)`.

This projection does not preserve all kernel guards automatically. The
nominal dose `3/5` follows only when the projected endpoint difference is
`1/10 - 1/40`. The current circuit does not have that nominal dose.

The ideal design values `Cs = 400 fF`, `Cf = 30 pF`, a `100 mV` window,
and `31.8 mV` per log-gain unit give `20/477`, approximately `0.04193`.
The package verifies this arithmetic and that it is below `0.05`. These
numbers are an ideal calibration, not certified bounds for the circuit;
the campaign observes about `0.0422` at 27 degrees C and `0.0519` at
-40 degrees C. No all-temperature read theorem follows.

## What is still a circuit obligation

1. Bound the **analog transferred charge**, including leakage, charge
   injection, summing-node movement and finite amplifier settling. The
   campaign's `steered1/2` flags measure a control transition, not this charge.
2. Bound the gain calibration and its variation over the actual stored-voltage,
   temperature and process ranges. The affine log-gain law is an interface
   assumption; a subthreshold mirror is not automatically exact over that range.
3. Establish the ordering of FIRE, protection, ERROR entry and ERROR exit,
   including delays and the absence of extra crossings. The window theorem
   is conditional on the relevant current law over the entire interval.
4. Account for **every** interval in the accumulated-error theorem. A list
   of isolated write windows omitting inter-pulse leakage is insufficient.
5. Bound the admitted-current waveform and main-state trajectory before
   transferring any read-latency or coincidence theorem. An observed timing
   difference is not, by itself, a constant-delay refinement.

The broader omissions in [DESIGN.md](../DESIGN.md) remain: pulse detection
and sequencing sources, learned recovery and MARK, layout parasitics, and
other unmodelled effects. This package does not change campaign verdicts.

## Build and audit

From this directory, with the pinned Lean distribution available:

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.Tactic
lake build
```

`CircuitBridge.lean` contains the bridge. `CircuitAudit.lean` checks every
declaration from that module, including auxiliary declarations, and rejects
dependencies on axioms other than `propext`, `Classical.choice` and
`Quot.sound`. No simulated sample is inserted as an axiom.

The main kernel package and the native network proofs are unchanged. This
is a local charge-balance result, not an end-to-end hardware proof.
