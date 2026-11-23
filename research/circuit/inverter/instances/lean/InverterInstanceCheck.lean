import InverterTarget

/-! The per-instance gate of one transistor-level inverter: the numeric premises of
`inhibited_silence` and `uninhibited_first_crossing` (research/circuit/lean/CircuitInverter.lean)
and of the abstract inverter law `InverterRead` (InverterTarget.lean), stated over `Rat` from the
measured values of one instance, outward rounded.

Development work, not preregistered. This file is free of Mathlib: every premise is a decidable
proposition over `Rat`, checked by `decide +kernel` in the generated file of each instance.

The reference is the help-alone response from rest to the nominal box help `H0` on `[h, h + hl]`,
with leak `a`. On `[h, h + hl]` it equals `H0 (1 - exp (-a (t - h))) / a`; it is zero before `h`
and decreases after `h + hl`. The exponential is bounded by its Taylor polynomials of degree 5
(below) and 6 (above), valid for every argument `x ≥ 0`. `(1 - exp (-a y)) / a` decreases in `a`,
so the upper bound of the reference uses the smaller measured leak and the lower bound the larger.

Not proved here, and so not part of what a passing gate establishes (see README):
* that the Rat premises imply the real-valued hypotheses `before` and `after` of the two theorems
  (the closed form of the reference, its monotonicity, and the two Taylor bounds in `ℝ`);
* that one leak rate serves both the actual response and the reference (`aLo`, `aHi` are the two
  sides of rest; the theorems assume a single `a`): the leak-asymmetry premise is open;
* the direct-rail delay: `FrontEnd` delays the direct rails by exactly `emitEarly`; no tolerance on
  that delay is proved;
* the latch delay is a measured constant of the instance, not a proved bound. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance

open TwoLayer (ReadObservation)

/-- The cell's design, in time units and units of `x`. -/
structure Design where
  tau : Rat
  h : Rat
  hl : Rat
  H0 : Rat
  D : Rat
  level : Rat

/-- The measured values of one instance, rounded outward: leaks `aLo ≤ aHi` (both sides of rest),
the budgets `ε₀, ηH, ηm, ηJ, δ` rounded up, the charge `Q` delivered by `τ` rounded down, the
latch delay (actual-level crossing to latch rise), the emission date with the input absent, and a
certificate `early`: the firing theorem's early date is `h + early`. -/
structure Measures where
  aLo : Rat
  aHi : Rat
  eps0 : Rat
  etaH : Rat
  etaM : Rat
  etaJ : Rat
  delta : Rat
  Q : Rat
  latchLo : Rat
  latchHi : Rat
  emit : Rat
  early : Rat

/-- An allowance added to every budget (`eta`) and to the threshold error (`delta`), and taken
from `Q`: zero for K0 (eligibility), three standard deviations of the frozen cell's noise for K3. -/
structure Allowance where
  delta : Rat
  eta : Rat

def expLo (x : Rat) : Rat := 1 - x + x * x / 2 - x * x * x / 6 + x * x * x * x / 24 - x * x * x * x * x / 120

def expHi (x : Rat) : Rat := expLo x + x * x * x * x * x * x / 720

/-- Upper bound of the reference at `h + y`, `0 ≤ y ≤ hl`. -/
def refUpper (d : Design) (m : Measures) (y : Rat) : Rat := d.H0 * (1 - expLo (m.aLo * y)) / m.aLo

/-- Lower bound of the reference at `h + y`. -/
def refLower (d : Design) (m : Measures) (y : Rat) : Rat := d.H0 * (1 - expHi (m.aHi * y)) / m.aHi

def silenceBudget (m : Measures) (k : Allowance) : Rat := m.eps0 + m.etaH + m.etaM + k.eta

def firingBudget (m : Measures) (k : Allowance) : Rat := m.eps0 + m.etaH + m.etaJ + k.eta

/-- Margins, reported by the generator; the premises below say they are positive. -/
def silenceMargin (d : Design) (m : Measures) (k : Allowance) : Rat :=
  d.level + expLo (m.aHi * d.D) * (m.Q - k.eta) - (refUpper d m d.hl + silenceBudget m k + (m.delta + k.delta))

def firingMargin (d : Design) (m : Measures) (k : Allowance) : Rat :=
  refLower d m d.hl - (d.level + firingBudget m k + (m.delta + k.delta))

/-- The order and sign facts the theorems need. -/
def Order (d : Design) (m : Measures) (k : Allowance) : Prop :=
  0 ≤ d.tau ∧ d.tau ≤ d.h ∧ 0 < d.hl ∧ d.h + d.hl ≤ d.D ∧ 0 < m.aLo ∧ m.aLo ≤ m.aHi ∧
  0 ≤ m.eps0 ∧ 0 ≤ m.etaH ∧ 0 ≤ m.etaM ∧ 0 ≤ m.etaJ ∧ 0 ≤ m.delta ∧ 0 ≤ k.delta ∧ 0 ≤ k.eta ∧
  0 ≤ m.early ∧ m.early < d.hl ∧ 0 ≤ m.latchLo ∧ m.latchLo ≤ m.latchHi

/-- `inhibited_silence`, `before`: the reference is zero on `[0, τ]` since `τ ≤ h`. -/
def SilenceBefore (d : Design) (m : Measures) (k : Allowance) : Prop :=
  silenceBudget m k + (m.delta + k.delta) < d.level

/-- `inhibited_silence`, `after`: the reference is at most its value at `h + hl` on `[τ, D]`. -/
def SilenceAfter (d : Design) (m : Measures) (k : Allowance) : Prop := 0 < silenceMargin d m k

/-- `uninhibited_first_crossing`, `before`, at `early = h + m.early`. -/
def FiringBefore (d : Design) (m : Measures) (k : Allowance) : Prop :=
  refUpper d m m.early + firingBudget m k + (m.delta + k.delta) < d.level

/-- `uninhibited_first_crossing`, `after`, at `deadline = h + hl`. -/
def FiringAfter (d : Design) (m : Measures) (k : Allowance) : Prop := 0 < firingMargin d m k

/-- The campaign's inverter dates: the window is `τ`, and the proved crossing interval
`(h + early, h + hl)`, shifted by the measured latch delay, lies in `(emitEarly, emitLate]`;
the measured emission lies there too. -/
def Timing (d : Design) (m : Measures) (t : InverterTiming) : Prop :=
  0 ≤ t.window ∧ t.window ≤ t.emitEarly ∧ t.emitEarly < t.emitLate ∧ t.window = d.tau ∧
  t.emitEarly ≤ d.h + m.early + m.latchLo ∧ d.h + d.hl + m.latchHi ≤ t.emitLate ∧
  t.emitEarly < m.emit ∧ m.emit ≤ t.emitLate

def Premises (d : Design) (m : Measures) (k : Allowance) (t : InverterTiming) : Prop :=
  Order d m k ∧ SilenceBefore d m k ∧ SilenceAfter d m k ∧ FiringBefore d m k ∧ FiringAfter d m k ∧
  Timing d m t

instance (d : Design) (m : Measures) (k : Allowance) : Decidable (Order d m k) := by
  unfold Order; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (SilenceBefore d m k) := by
  unfold SilenceBefore; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (SilenceAfter d m k) := by
  unfold SilenceAfter; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (FiringBefore d m k) := by
  unfold FiringBefore; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) : Decidable (FiringAfter d m k) := by
  unfold FiringAfter; infer_instance
instance (d : Design) (m : Measures) (t : InverterTiming) : Decidable (Timing d m t) := by
  unfold Timing; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) (t : InverterTiming) :
    Decidable (Premises d m k t) := by
  unfold Premises; infer_instance

/-- The checker. -/
def check (d : Design) (m : Measures) (k : Allowance) (t : InverterTiming) : Bool :=
  decide (Premises d m k t)

theorem check_sound {d : Design} {m : Measures} {k : Allowance} {t : InverterTiming}
    (h : check d m k t = true) : Premises d m k t :=
  of_decide_eq_true h

/-- The two observed reads of one instance: the input absent (one emission at `emit`) and
present (arriving at the start, no emission). -/
def absentRead (m : Measures) : ReadObservation 1 := ⟨0, fun _ => none, [m.emit], 0⟩

def presentRead : ReadObservation 1 := ⟨0, fun _ => some 0, [], 0⟩

/-- The premises give the abstract inverter law `InverterRead` on both observed reads. -/
theorem inverterRead_of_premises {d : Design} {m : Measures} {k : Allowance} {t : InverterTiming}
    (p : Premises d m k t) : InverterRead t (absentRead m) ∧ InverterRead t presentRead := by
  obtain ⟨_, _, _, _, _, w0, we, el, _, _, _, e1, e2⟩ := p
  have valid : t.Valid := ⟨w0, we, el⟩
  refine ⟨⟨valid, ?_, ?_, ?_⟩, ⟨valid, ?_, ?_, ?_⟩⟩
  · intro v hv; simp [absentRead] at hv
  · simp only [absentRead]; constructor
    · show 0 + t.emitEarly < m.emit
      rw [Rat.zero_add]; exact e1
    · show m.emit ≤ 0 + t.emitLate
      rw [Rat.zero_add]; exact e2
  · rfl
  · intro v hv
    simp [presentRead] at hv
    subst hv
    exact ⟨Rat.le_refl, show (0 : Rat) ≤ 0 + t.window by rw [Rat.zero_add]; exact w0⟩
  · simp [presentRead]
  · rfl

end LearnedCoincidence.MonotoneDNF.InverterInstance
