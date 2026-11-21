import Inverters
import MonotonePremiseSoundness

/-! A non-vacuity witness for the inverter composition. One input (`M = 1`), the
function NOT, and a concrete admissible cascade on the two rails whose predicted
answer is NOT. Concrete dated observations satisfy every premise of
`inverters_compute` at both input patterns, so its premises can hold together, and
its conclusion then says that the network answers NOT.

`every_function_with_inverters` chooses its cascade by classical choice, so no
concrete instance can be written for that particular cascade. The witness is
therefore for `inverters_compute`, the composition for a given cascade, which
`every_function_with_inverters` applies. -/

namespace LearnedCoincidence.MonotoneDNF.InverterWitness

open TwoLayer (SlotTiming ReadObservation)
open PremiseCheck

/-- First layer: one conjunction, of line 1 alone (the complement rail of input 0).
Second layer: one OR of that line. Predicted answer on the rails: NOT. -/
def cascade : Cascade 1 1 2 where
  first := {
    target := fun _ => pattern [1], tests := [], initialGain := fun _ _ => 0, help := fun _ => 0,
    threshold := fun _ => 2, trainingError := fun _ => 1, testingError := fun _ => 1,
    dose := 4, maxWrites := 1, rail := 5
  }
  second := {
    lines := fun _ _ => true, alwaysFire := fun _ => false,
    initialGain := fun _ _ => 0, help := fun _ => 0, threshold := fun _ => 2,
    trainingError := fun _ => 1, testingError := fun _ => 1,
    dose := 4, maxWrites := 1, rail := 5
  }
  delay := fun _ _ => 1 / 2
  heldOut := []

def timing : SlotTiming := ⟨1 / 2, 3, 4⟩

/-- The inverter: input window 1/4, emission in (1/2, 3/4]. -/
def inverter : InverterTiming := ⟨1 / 4, 1 / 2, 3 / 4⟩

/-- The input pattern's pulse arrives at 60, when the input is present. -/
def external (y : Pattern 1) : Fin 1 → Option Rat := fun _ => if y 0 then some 60 else none

/-- The inverter fires at 60 + 5/8 exactly when its input is absent. -/
def inv (y : Pattern 1) : Fin 1 → ReadObservation 1 := fun _ =>
  ⟨60, fun _ => external y 0, if y 0 then [] else [60 + 5 / 8], 0⟩

def absent : Pattern 1 := fun _ => false
def present : Pattern 1 := fun _ => true

private def read (start : Rat) (x : Pattern M) (score level : Int) : ReadObservation M :=
  datedRead start (Vector.ofFn fun j => if x j then some start else none)
    (if level ≤ score then [start + 1] else []) score

/-- The first-layer read produced by the front end, starting with the delayed rails. -/
private def frontRead (y : Pattern 1) (fires : Bool) : ReadObservation 2 :=
  datedRead (60 + 1 / 2) (Vector.ofFn (frontArrival (1 / 2) (external y) (inv y)))
    (if fires then [62] else []) (if fires then 4 else 0)

private def lessonStart (n : Fin (lessons cascade).length) : Rat := 20 + 10 * n.val

private def pairs (word : Fin 4) : Pattern 2 := fun j => word.val.testBit (1 - j.val)

/-- Training: the conjunction is silent once, then fires; each lesson routes the
line's FIRE to the OR, which is silent once, then fires. Tests: rows 1 and 2 are
the rails of the two input patterns, produced by the front end; rows 0 and 3 are
the other two line patterns, driven directly. -/
def trace : TraceTables cascade where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun _ =>
    read (10 * r.val) (pattern [1]) (if r.val = 0 then 0 else 4) 2
  teach := Vector.ofFn fun n => Vector.ofFn fun _ => read (lessonStart n) (pattern [1]) 4 2
  secondTrain := Vector.ofFn fun n =>
    read (lessonStart n + 3 / 2) (singleton 0) (if n.val = 0 then 0 else 4) 2
  firstTest := Vector.ofFn fun word => Vector.ofFn fun _ =>
    if word.val = 1 then frontRead absent true
    else if word.val = 2 then frontRead present false
    else read (60 + 1 / 2) (pairs word) (if word.val = 3 then 4 else 0) 2
  secondTest := Vector.ofFn fun word => Vector.ofFn fun _ =>
    if word.val = 1 then read (62 + 1 / 2) (fun _ => true) 4 2
    else if word.val = 3 then read (62) (fun _ => true) 4 2
    else read 61 (fun _ => false) 0 2
  scores := Vector.ofFn fun _ => Vector.ofFn fun _ => #v[0, 4]

def checks : Bool :=
  checkCascadeValid cascade &&
  checkCascadeCalibrationOneSided cascade timing timing trace.observations trace.scoreAt

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem accepted : checks = true := by decide +kernel

theorem valid : cascade.Valid := by
  have h := accepted
  unfold checks at h
  exact cascade_valid_checker_sound _ _ _ _ (Bool.and_eq_true_iff.mp h).1

theorem calibration : CascadeCalibrationOneSided cascade timing timing trace.observations trace.scoreAt := by
  have h := accepted
  unfold checks at h
  exact cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ (Bool.and_eq_true_iff.mp h).2

theorem predicted_not (y : Pattern 1) : output cascade 0 (rails y) = !y 0 := by
  have : y = absent ∨ y = present := by
    cases h : y 0
    · exact Or.inl (funext fun j => by rw [Fin.fin_one_eq_zero j, h]; rfl)
    · exact Or.inr (funext fun j => by rw [Fin.fin_one_eq_zero j, h]; rfl)
  rcases this with rfl | rfl <;> decide

private theorem inverter_read (y : Pattern 1) (j : Fin 1) : InverterRead inverter (inv y j) := by
  refine ⟨by simp only [InverterTiming.Valid, inverter]; decide +kernel, ?_, ?_, ?_⟩
  · intro v arrived
    cases h : y 0 <;> simp [inv, external, h] at arrived
    subst arrived
    simp only [inv, inverter]
    decide +kernel
  · cases h : y 0 <;> simp [inv, h, inverter] <;> decide +kernel
  · cases h : y 0 <;> simp [inv, external, h, ReadObservation.fired, ReadObservation.input]

private theorem front_end (y : Pattern 1) (fires : Bool) :
    FrontEnd inverter 60 (external y) (inv y) (frontRead y fires) := by
  refine ⟨fun j => ⟨rfl, rfl, inverter_read y j⟩, by simp [frontRead, datedRead, inverter], ?_⟩
  funext j
  simp [frontRead, datedRead, inverter, Vector.get]
  rfl

/-- Every premise of `inverters_compute` holds for this cascade at each input pattern. -/
theorem premises_hold (y : Pattern 1) :
    inverter.window ≤ timing.skew ∧ inverter.emitLate - inverter.emitEarly ≤ timing.skew ∧
    CascadeTrainingCalibration cascade timing timing trace.observations ∧
    (∀ j, (external y j).isSome = y j) ∧
    InverterFrontRead cascade inverter timing trace.observations y 60 (external y) (inv y) ∧
    (∀ k, SecondTestRead cascade timing trace.observations trace.scoreAt (rails y) k) := by
  have cal := calibration
  have hy : y = absent ∨ y = present := by
    cases h : y 0
    · exact Or.inl (funext fun j => by rw [Fin.fin_one_eq_zero j, h]; rfl)
    · exact Or.inr (funext fun j => by rw [Fin.fin_one_eq_zero j, h]; rfl)
  refine ⟨by simp only [inverter, timing]; decide +kernel, by simp only [inverter, timing]; decide +kernel,
    cal.1, ?_, ?_, fun k => cal.2.2 (rails y) k⟩
  · intro j
    rw [Fin.fin_one_eq_zero j]
    cases h : y 0 <;> simp [external, h]
  · intro a
    have firstRead := cal.2.1 (rails y) a
    obtain ⟨valid', _, _, emission, decoder, residual⟩ := firstRead
    refine ⟨?_, ⟨valid', emission, decoder, residual⟩⟩
    rcases hy with rfl | rfl
    · have index : maskIndex (rails absent) = ⟨1, by decide⟩ := by decide
      have row : trace.observations.firstTest (rails absent) a = frontRead absent true := by
        simp [TraceTables.observations, index, trace, Vector.get, Fin.cast]
      rw [row]
      exact front_end absent true
    · have index : maskIndex (rails present) = ⟨2, by decide⟩ := by decide
      have row : trace.observations.firstTest (rails present) a = frontRead present false := by
        simp [TraceTables.observations, index, trace, Vector.get, Fin.cast]
      rw [row]
      exact front_end present false

/-- The composition, applied to the witness: the network answers NOT at both
input patterns. -/
theorem answers_not (y : Pattern 1) :
    (trace.observations.secondTest (rails y) 0).fired = !y 0 := by
  obtain ⟨windowFits, spreadFits, training, realised, front, second⟩ := premises_hold y
  rw [inverters_compute valid windowFits spreadFits training realised front second 0, predicted_not]

end LearnedCoincidence.MonotoneDNF.InverterWitness
