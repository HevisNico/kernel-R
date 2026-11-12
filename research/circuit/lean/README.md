# Conditional circuit-to-kernel bridge

This package starts the formal connection between the circuit of PR #103
and Kernel R. It uses integral charge balances, with an optional constructor
from the existing `KernelR.Doses.drain_integral` theorem. It proves a
charge-to-dose correspondence and explicit
error budgets. It does **not** prove that the transistor netlist satisfies
the hypotheses, or identify a SPICE run with a kernel execution. The
robustness and timing modules extend the connection to calibration error,
admitted-current error and the first scalar threshold contact.

## What is connected

On a write window `[s,t]`, let `Qs` be the sensor charge and `Qm` a storage
coordinate, with balances

```
Qs(s) - Qs(t) = integral_s^t Is,
Qm(s) - Qm(t) = integral_s^t Iw.
```

The currents are interval-integrable; no derivative is required at switching
times. `ChargeWindow` specifies endpoint balances, not the entire interior
charge path. `ofCurrents` constructs such paths by integration, while
`ofDerivatives` recovers the differentiable special case. A nonnegative
coefficient `k` converts a decrease
of `Qm` to an increase of log-gain. For a constant feedback capacitor and
an affine calibration `z = z_ref - beta * Vmem`, take `Qm = Cf * Vmem`
and `k = beta / Cf`. The summing node must be fixed for the ideal capacitor
interpretation; its motion and other parasitic effects must be accounted
for in the effective write current or a residual bound. `Qm` is not an
unqualified identification with the signed charge on a particular plate.

The integral balances yield

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
-40 degrees C. `design_dose_below_read_budget` is a nominal-design fact,
not an all-temperature bound. The wider ideal read results below allow
doses up to `3/50`, but still require their stopped-training hypotheses.

## From window residuals to a common need

[VariableNeedTolerance.lean](../../recursive-learning/native/Search/VariableNeedTolerance.lean)
extends the scalar probe contract to independently varying nonnegative
write doses `dose(j)` with `abs(dose(j) - d0) <= b`. The conclusion is
`NeedAlong level z m`, where `z(n) = z0 + sum_{j<n} dose(j)`: fewer than
`m` writes are silent, and from `m` onwards a read fires throughout the
same allowed rest-charge band as `NeedIs`. Constant doses recover `NeedIs`.
The sufficient budget is unchanged:

```text
a + m * b + (20/17) * ell + 1/8000 < d0/2.
```

The proof bounds cumulative doses between constant ladders and applies
`needIs_of_tolerance`. The general circuit corollary,
`needAlong_of_circuit_tolerances`, composes this with `dose_error`. It allows
sensor-dose error `abs(k * (Qs(start)-Qs(stop)) - d0) <= sigma`, transferred-charge
residual at most `eta`, and additional linkage error `e`, including calibration
or inter-window drift. Use **`b = k * eta + sigma + e`**. The gain increments
must remain nonnegative. `sigma` is a deterministic bound, not a noise
standard deviation. The earlier exact-sensor corollaries remain available as
special cases; exact nominal sensor dose is no longer required by the general result.

This proves a variable-dose **scalar need**. It does not replace the
fixed-dose `Trained`, `Runs` or compiled-network execution constructors.
The campaign's 190 exact counts out of 200 ports are empirical comparisons,
not assumptions or certificates of the theorem's tolerance inequalities.
The [fixed test rule](../NEED_TEST_PROTOCOL.md) and
[retrospective 200-port diagnostic](../NEED_BUDGET.md) distinguish missing
physical bounds from the exploratory peak-based calculation.

## Ideal read windows up to dose 0.06

[WideDoseRead.lean](../../recursive-learning/native/Training/WideDoseRead.lean)
adds separate results for a maximum final increment of `3/50`, preserving
the original `1/20` results and their callers.

| Ideal stopped-training read | Dose at most 0.05 | Dose at most 0.06 | New strict skew bound |
|---|---|---|---|
| Two trained ports read together | `(0.239, 0.256]` | `(0.236, 0.256]` | `< 0.020` |
| One port trained at 2/3 amplitude | `(0.355, 0.385]` | `(0.349, 0.385]` | `< 0.036` |

The wider pair dates still distinguish offsets `0` and `+/-0.3` with the
existing `0.1` stagger and `0.03` differential lag budgets
(`wide_pair_dates_decide_lag`). This is a conditional statement about dates,
not a construction of a delayed circuit execution. The single-port skew
has increased and cannot silently replace a budget of `0.03` in other proofs.
The cold dose around `0.052` fits the new dose bound; the measured latency
around `0.267` still exceeds `0.256`. A full circuit timing refinement
therefore remains necessary.

## From a dose budget to a first contact

`CircuitRobustness.lean` allows bounded error in the affine gain calibration.
The true log-gain step then differs from the sensor-derived dose by at most
`k * eta + epsilon_start + epsilon_end`. Protection has the corresponding
retention bound. A uniform parasitic-current bound `J` gives a charge budget
`J * (t-s)` for a window of duration `t-s`.

The exponential is not linearized: if `abs(z-z_ref) <= epsilon`, then

```
abs(exp(z) - exp(z_ref)) <= exp(z_ref) * (exp(epsilon) - 1).
```

For frozen gains multiplying the same pulse shape, a second theorem turns
this into an L1 admitted-current budget. This is a restricted read contract;
neither equal pulse shapes nor frozen gains are established for the circuit.

`CircuitTiming.lean` then proves the following chain of implications:

1. For two declared scalar leaky responses with the same nonnegative decay
   rate and common rest coordinate, state error is at most initial-state
   error plus the integrated absolute admitted-current error. This step
   uses the response equations, not an assumed time shift. Currents need
   only be interval-integrable, so switching is allowed.
2. Uniform state error `epsilon` and threshold error `delta`, together with
   strict reference margins before an early date and at a deadline, imply
   the existence of an actual first contact between those dates. The proof
   reuses `KernelR.Hybrid.scalar_first_crossing` and excludes earlier contacts.
3. If the reference derivative is at least `speed > 0` on the relevant
   interval, the contact-time error is at most `(epsilon + delta) / speed`.
   `robust_first_crossing_with_latency` proves existence, the strict preguard
   and this bound for the **same** first contact.
4. `current_error_first_crossing` composes the current-to-state estimate
   with the first-contact construction. The current error is bounded on
   every prefix up to the deadline, not only at the end of the pulse.

A formal counterexample shows why contact alone is insufficient: the
reference `-t^2` touches zero at time zero, while `-t^2-epsilon`, uniformly
`epsilon` away for any positive `epsilon`, never reaches zero.

These results concern the uncut scalar paths before a hybrid switch. They
use a continuation of the READY dynamics past the prospective contact,
not the already protected physical trace after the gate has closed. A
refinement must establish agreement with that continuation until the
first event; the protected trace need not satisfy the deadline margin.
The results
do not prove transversality of the actual first contact, a comparator/latch
event, correct switching afterwards, or an entire hybrid execution. The
same-leak assumption is explicit; uncertainty in the leak rate needs a
separate bound. No numerical value of `epsilon`, `delta` or `speed` for
the transistor circuit is certified here.

## What is still a circuit obligation

1. Bound the **analog transferred charge**, including leakage, charge
   injection, summing-node movement and finite amplifier settling. The
   campaign's `steered1/2` flags measure a control transition. The newer
   [complement](../COMPLEMENT.md) measures the signed current integral in
   five simulations through an inserted ammeter. It does not yet supply
   certified whole-range bounds on the effective storage current, numerical
   integration error, or the L1 prefix budgets needed for timing. A small
   signed integral can hide large excursions of opposite signs.
2. Bound the gain calibration and its variation over the actual stored-voltage,
   temperature and process ranges. The affine log-gain law is an interface
   assumption; a subthreshold mirror is not automatically exact over that range.
3. Establish the ordering of FIRE, protection, ERROR entry and ERROR exit,
   including delays and the absence of extra crossings. The window theorem
   is conditional on the relevant current law over the entire interval.
4. Account for **every** interval in the accumulated-error theorem. A list
   of isolated write windows omitting inter-pulse leakage is insufficient.
5. Supply the admitted-current, main-state, threshold and derivative bounds
   required by the timing module, and connect its scalar contact to the
   comparator/latch event before transferring a read-latency or coincidence
   theorem. An observed timing difference is not a constant-delay refinement.

The broader omissions in [DESIGN.md](../DESIGN.md) remain: pulse detection
and sequencing sources, learned recovery and MARK, layout parasitics, and
other unmodelled effects. This package does not change campaign verdicts.

## Build and audit

From this directory, with the pinned Lean distribution available:

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.Tactic
lake build
python3 -B check_negative.py
```

The original bridge has four main result groups: exposed/protected transfer,
dose and retention error bounds, capacitor-to-kernel dose correspondence,
and accumulation of local errors. `calibrated_gain`, `kernel_dose_projection`,
`common_offset_cancels` and `design_dose` are algebraic interface identities
or calibration arithmetic, not four additional scientific contributions.

`CircuitAudit.lean` covers the four circuit modules (`CircuitBridge`,
`CircuitRobustness`, `CircuitTiming`, `CircuitNeed`) and the two new native
modules (`Search.VariableNeedTolerance`, `Training.WideDoseRead`). It checks
every declaration, including generated auxiliaries, and rejects dependencies
on axioms other than `propext`, `Classical.choice` and `Quot.sound`. Declaration
counts report audit coverage, not a count of independent results. No simulated
sample is inserted as an axiom. The native audit also imports both new modules.

The negative controls require rejection of an added project axiom, an
admitted proof, a latency bound with the threshold-error term removed,
a variable-dose budget without its accumulation factor, a circuit budget
without sensor-dose uncertainty, and reuse of the
old pair-window lower date at dose 0.06. They temporarily edit the relevant
Lean modules, restore them in a `finally` block and rebuild the original sources. Run them without concurrent edits or builds
in the same checkout. CI runs the build, audit and these controls.

The main kernel package and existing native network proofs are unchanged;
the new native modules add scalar tolerance and wider ideal read results.
These are conditional results, not an end-to-end hardware proof.
