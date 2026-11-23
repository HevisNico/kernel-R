import CircuitInverterGate
import InverterTarget

/-! The abstract layer of the per-instance inverter gate.

The gate's definitions (`Design`, `Measures`, `Allowance`, the margins, `Order`, `SilenceBefore`,
`SilenceAfter`, `FiringBefore`, `FiringAfter`, `StateBound`) have one source:
`research/circuit/lean/CircuitInverterGate.lean`, namespace `KernelR.Circuit.Gate`, the module the Mathlib bridge
`CircuitInverterGateProof.lean` also imports. Nothing here restates them.

This file adds only what needs the abstract inverter law (`InverterTarget.lean`): the campaign dates (`Timing`),
the conjunction `Premises`, its checker and soundness, the front-end fits of `InverterLag.lean`, and
`inverterRead_of_premises`. Free of Mathlib.

Development work, not preregistered. Every verdict stays conditional on the open premises that the generator's
output lists: the leak along the trajectory as a modelling step [I], and the latch delay as a measured constant. -/

namespace LearnedCoincidence.MonotoneDNF.InverterInstance

open TwoLayer (ReadObservation)
open KernelR.Circuit.Gate

/-- The campaign's inverter dates: the window is `τ`; the proved crossing interval `(h + early, h + hl)`,
shifted by the measured latch delay, lies in `(emitEarly, emitLate]`; the measured emission lies there too. -/
def Timing (d : Design) (m : Measures) (t : InverterTiming) : Prop :=
  0 ≤ t.window ∧ t.window ≤ t.emitEarly ∧ t.emitEarly < t.emitLate ∧ t.window = d.tau ∧
  t.emitEarly ≤ d.h + m.early + m.latchLo ∧ d.h + d.hl + m.latchHi ≤ t.emitLate ∧
  t.emitEarly < m.emit ∧ m.emit ≤ t.emitLate

def Premises (d : Design) (m : Measures) (k : Allowance) (t : InverterTiming) : Prop :=
  Order d m k ∧ SilenceBefore d m k ∧ SilenceAfter d m k ∧ FiringBefore d m k ∧ FiringAfter d m k ∧
  Timing d m t

/-- `front_end_lag_window` (InverterLag.lean): `windowFits` and `spreadFits`. Checked only when the campaign
fixes the first layer's skew and the delay tolerance `ε`. -/
def FrontEndFits (t : InverterTiming) (ε skew : Rat) : Prop :=
  0 ≤ ε ∧ t.window + ε ≤ skew ∧ t.emitLate - t.emitEarly ≤ skew

instance (d : Design) (m : Measures) (t : InverterTiming) : Decidable (Timing d m t) := by
  unfold Timing; infer_instance
instance (d : Design) (m : Measures) (k : Allowance) (t : InverterTiming) :
    Decidable (Premises d m k t) := by
  unfold Premises; infer_instance
instance (t : InverterTiming) (ε skew : Rat) : Decidable (FrontEndFits t ε skew) := by
  unfold FrontEndFits; infer_instance

def check (d : Design) (m : Measures) (k : Allowance) (t : InverterTiming) : Bool :=
  decide (Premises d m k t)

theorem check_sound {d : Design} {m : Measures} {k : Allowance} {t : InverterTiming}
    (h : check d m k t = true) : Premises d m k t :=
  of_decide_eq_true h

/-- The two observed reads of one instance: the input absent (one emission at `emit`) and present
(arriving at the start, no emission). -/
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
