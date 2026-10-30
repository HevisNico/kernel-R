# Robust local theorem: A learns from B under drift, noise and pulse deformation

This extends the prepared-section theorem `proof/reciprocal_learning/THEOREM.md` (A learns from
B) from fixed parameters to three non-ideal effects. The setting, protocol and conclusions are
the same; only the physical assumptions are weakened.

## Statement

Fix ε, a noise bound ν ≥ 0 and an amplitude deviation α in [0,1), among the certified points:

| ε | (ν, α) |
|---|---|
| 0.003 and 0.1 | (0, 0), (0.002, 0), (0, 0.09), (0.0015, 0.05) |

**Drift.** Each of the five per-port parameters C, Lm, Ls, Le, M of A and B (30 in all) is any
measurable function of time with values in its relative box [1−ε, 1+ε] around nominal. No bound
on the rate of change is assumed. Noise and amplitude histories are also measurable.
A firing triggers a canonical one-unit outgoing pulse; its support is independent
of the noisy FAST duration. Received currents have the multipliers stated below.

**Noise.** The main charge q and every auxiliary charge m receive an additive disturbance w(t),
|w(t)| ≤ ν, in every mode: q' = F(q) + w and m' = F(m) + w, where F is R's unchanged vector field.
The reserve E is not perturbed. Guards keep first-crossing semantics.

**Pulse amplitude.** Every received pulse current is c(t)·a·exp(−a·age) on [0,1), with
c(t) in [1−α, 1+α], at main and auxiliary inputs.

Prepared section, inputs and routing are those of the original theorem: both cells READY,
q in [0.09999, 0.10001], every m in [0.02499, 0.02501], port-2 gain 0.3·exp(η) with |η| ≤ 1e−5,
b in [0.17999, 0.18001], E in [50,100]; 16 pulses to B at 0, 8, …, 120; each B emission reaches A
with a delay independently in [0.3, 0.4]; nothing else.

**Then**, for every admissible drift, disturbance and amplitude history:

1. B emits exactly 13 pulses and A exactly 10.
2. A receives exactly three complete ERROR doses while READY before its first emission, and no
   later dose. Each dose D satisfies |D − 0.6| ≤ 8·ν·T_E, where T_E is the certified ERROR
   duration bound (`gain_log_dose`). Its b is unchanged.
3. log g_A,final = log g_A,initial + D₁ + D₂ + D₃. With ν = 0 the dose is exactly 0.6, as in the
   original theorem, whatever the drift.
4. Both cells are READY with no active currents by 139.9.
5. An isolated standardized-rest copy of A, subject to the same drift, noise and amplitude, with
   plasticity disabled, responds 0 of 8 times to period-20 port-2 pulses before learning and
   exactly once to each of the 8 afterwards.

Each step below names the obligations of `bounds.py` that it uses.

## 0. Comparison tools

**(C1) Linear forcing.** If x' = −κ(x − x*) + u(t) + w(t), with u ≥ 0 and |w| ≤ ν, then
x(t) − x* lies between (x(0) − x*)e^(−κt) + ∫e^(−κ(t−s))u(s)ds ± ν(1 − e^(−κt))/κ, and
ν(1 − e^(−κt))/κ ≤ min(νt, ν/κ).

**(C2) Exit time of a drifting decay.** If x' = −L(t)x + w(t), with L(t) in [L₋, L₊] and |w| ≤ ν,
and 0 < x₁ < x₀ with ν < L₋x₁ (`decay_*_dominates_noise`), then x is strictly decreasing while
x ≥ x₁, and it reaches x₁ from x₀ in a time T with

`(1/L₊)·ln((x₀+ν/L₊)/(x₁+ν/L₊)) ≤ T ≤ (1/L₋)·ln((x₀−ν/L₋)/(x₁−ν/L₋))`.

Indeed −L₊x − ν ≤ x' ≤ −L₋x + ν for x > 0, and the scalar comparison theorem bounds x between the
solutions of the two constant-coefficient equations. Drift of L enters only through L₋ and L₊.

**(C3) Dose identity.** In a phase where m' = −L(t)m + w and an actuator has rate c·L(t)·m, the
total actuation is c·∫L·m dt = c·(m_start − m_end + ∫w dt). Drift of L cancels exactly; the noise
contributes at most c·ν·T.

`h_increases_through_raw_window`: h(t) = a/(a−κ)(e^(−κt) − e^(−at)) peaks at ln(a/κ)/(a−κ) > 1,
so h increases on [0,1].

## 1. Auxiliary first crossing

Between inputs an auxiliary is READY with no raw drive. From the section (±1e−5) or from an
ERROR end (exactly r_m), (C1) keeps |m − r_m| ≤ 1e−5 + ν/κ (`aux_rest_deviation`), below the
threshold (`aux_rest_below_threshold`). At an input, the auxiliary admits
M(t)·c(t)·a·e^(−at) ≥ 0. By (C1) and h increasing:

`r_m − d − νt + M₋(1−α)h(t) ≤ m(t) ≤ r_m + d + νt + M₊(1+α)h(t)`.

The upper bound is below 1 at 0.015 (`aux_below_threshold_until_0.015`), hence on [0, 0.015]; the
lower bound exceeds 1 at 0.03 (`aux_above_threshold_by_0.03`). So the first crossing τ lies in
(0.015, 0.03). M may drift: only its box enters.

## 2. Auxiliary protected cycle

Protected auxiliaries ignore input currents. MARK runs from m = 1 down to 0.8 at rate Lm(t),
SILENT from 0.8 to 0.1 at rate Ls(t), and ERROR from 0.1 to r_m at rate Le(t), each with
disturbance w. (C2) gives `mark_duration`, `silent_duration` and `error_duration`, hence
`mark_end`, `error_start` and `aux_finish` relative to the input. The cycle ends after the raw
pulse (`aux_cycle_ends_after_raw_pulse`) and before the next input
(`aux_cycle_ends_before_next_input`, and `probe_aux_cycle_ends` at period 20). So every input meets
a READY auxiliary, and one cycle runs per input.

## 3. ERROR gain dose

If the main cell stays READY throughout an ERROR, the energy gate is open (Step 8) and the gain
stays below its cap (`learned_gain_below_all_caps`, against the smallest cap C₋ of a drifting C),
then by (C3) with c = 8 the log-gain increases by D = 8·(0.1 − 0.025 + ∫w), and
|∫w| ≤ ν·T_E (`gain_log_dose`). With ν = 0, D = 0.6 exactly.

## 4. Main firing, FAST and SLOW

A firing input meets the main charge with excess in [−(1e−5 + ν/κ), x₊] (Step 5 and 6 give x₊).
FAST runs from q = 1 to 1/4 at rate a, SLOW from 1/4 to r at the current b; (C2) gives
`fast_duration` and `slow_duration`. MARK ends before any firing
(`mark_finishes_before_any_main_firing`), so it never meets a protected main cell and b does not
change. ERROR starts after the latest firing (`main_fires_before_error_begins`) and ends before
the earliest FAST end (`error_finishes_during_main_fast`): it is entirely protected and gives no
gain dose. The return to READY happens after the raw pulse (`main_reopens_after_raw_pulse`), with
q exactly r by the guard, and before the next input (`main_reopens_before_next_input`).
This last obligation sets the noise budget: in SLOW the decay rate b ≈ 0.18 is small, so noise
lengthens the return most.

## 5. The first three inputs are silent

Let x₊ = Q = 0.03 be the input-section excess. Before a hypothetical first crossing on [0,1], with
gain g_j = g₀·exp(D₁ + … + D_j), (C1), h(t) ≤ h(1) and the overlap argument of the original
theorem give

`q(t) − r ≤ Q + g_j,₊(1+α)h(1) + ν + g_j,₊(e^(D₊) − 1)(1+α)·a·e^(−a·e₋)·max(0, 1 − e₋)`,

where e₋ is the lower ERROR start. The last term bounds the extra charge from a gain increase
during a possible ERROR/raw overlap. This `peak_bound_j` is below 1
(`silent_j_no_first_crossing`). After raw end, (C1) gives q − r ≤ max(peak − r, ν/κ), a convex
combination of the two, and ν/κ is below threshold (`silent_j_stays_below_threshold_after_raw_end`).
At the next input, at least G = 7.5 later (`min_input_gap`):

`q − r ≤ (peak − r)·e^(−κ(G−1)) + ν/κ` (`carry_bound_j`) < Q (`silent_j_excess_returns_inside_section`).

The lower excess bound −(1e−5 + ν/κ) is invariant because the drive is non-negative. So the main
cell stays READY through each of the three ERRORs, and each gives a full dose (Step 3).

## 6. Every later input fires exactly once

The fourth input starts from an excess at most carry₂; later inputs start from a return, with
excess at most ν/κ (`rest_noise_inside_section`). Let x₊ be the larger (`learned_start_excess`).
The gain is the learned g₃, constant until ERROR starts (after 0.9). Then:

- `learned_below_threshold_until_0.5`: r + x₊ + g₃,₊(1+α)h(0.5) + 0.5ν < 1, hence q < 1 on [0, 0.5];
- `learned_above_threshold_by_0.9`: r − (1e−5 + ν/κ) + g₃,₋(1−α)h(0.9) − 0.9ν > 1.

So the first crossing lies in (0.5, 0.9]. Step 4 then gives one emission, no dose, b unchanged and
a return to READY before the next input. By induction the regime repeats for every later input.

## 7. Composition and calendar

B's inputs are 8 apart. Steps 1 to 6 give three silent inputs, then 13 emissions at
8j + (0.5, 0.9], j = 3, …, 15. With the delays, A's inputs are at least G = 7.5 apart, and A has no
input before the first. Steps 1 to 6 apply to A: three full doses, then 10 emissions. A's third
dose ends before its first emission (`A_learning_complete_before_first_response`); A and B are
quiescent by 139.9 (`A_quiescent_before_measurement`, `B_quiescent_before_measurement`).

## 8. Energy

The work W is a sum of non-negative terms: admitted currents, FAST and SLOW costs, protected
drains and effective learning rates. Under noise, protected charges still decrease and stay below
their phase maxima, so the drain and learning terms keep their bounds. The admitted currents are
multiplied by at most 1+α. With upper box endpoints, `work_bound` is below 500
(`reserve_gate_stays_open`), so [50,100] is invariant under the pump, and the gate E > 0 stays
open.

## 9. Probes

The probes are isolated standardized-rest copies subject to the same drift, noise and amplitude,
with plasticity disabled. Before learning, the gain is g₀ and Step 5 at period 20 ≥ G shows no
response to any of the 8 pulses (the carry at gap 20 is smaller than at G). After learning,
Step 6 at period 20 (`probe_gap_exceeds_cycle`) gives exactly one response to each.

## Certificates, checks and evidence

`certify.py` evaluates the 36 strict obligations with outward Decimal intervals at 128 digits and
publishes bounds rounded outwards to 40 places. `verify.py` recomputes every enclosure with
70-place integer fixed-point intervals (explicit exp/ln series tails), requires each to lie inside
the published interval, and rechecks every obligation. The formulas in `bounds.py` are shared:
this is arithmetic diversity, not an independent formalization. `tests.py` checks the 8
certificates, refusal beyond each budget (ν = 0.0026, α = 0.1, ν = 0.02), tampered certificates and
`-O` execution.

`simulate_noise.py` and `simulation_evidence.txt` are retained as legacy Euler evidence,
not used to validate doses. Their endpoint overshoot makes some reported doses fall
outside the certified continuous intervals. `simulate_events.py` instead localizes
hybrid transitions; `validate.py` checks individual doses, charge cycles, energy,
latencies, counts and probes, and records tolerance refinement. These remain
floating-point tests, not certified ODE enclosures. Passing a few histories outside
a sufficient budget would not establish a larger universal robustness budget.

## Scope and limits

- This file proves the local prepared-section B→A theorem. `THEOREM_N.md` composes
  that local contract into a finite prepared chain with a depth-dependent source
  period. It does not extend the original fast N-cell protocol or entry from birth.
- The noise is a bounded deterministic disturbance on q and m. It is not a stochastic model:
  unbounded Gaussian noise would need a probabilistic statement. Threshold noise, E noise and
  memory leakage of z and b are not covered.
- The noise budget does not depend on ε: it is set by the slow recovery rate b ≈ 0.18.
- The hybrid argument is written by hand; only its finite inequalities are machine-checked.
