import InverterTraining
import InverterWitness

/-! A non-vacuity witness for training through the inverters. The cascade, the
inverter timing and the function (NOT on one input) are those of
`InverterWitness.lean`. Here every first-layer read, of training, of teaching
and of test, is produced by the front end: the network only ever sees its one
input line. Every premise of `trained_inverters_compute` holds at both input
patterns, and the trained network answers NOT.

As for `InverterWitness`, the witness is for the composition for a given cascade
(`trained_inverters_compute`), which `every_function_trained_through_inverters`
applies; that theorem's own cascade is chosen by classical choice. -/

namespace LearnedCoincidence.MonotoneDNF.InverterTrainingWitness

open TwoLayer (SlotTiming ReadObservation)
open PremiseCheck
open InverterWitness (cascade timing inverter absent present predicted_not valid)

/-- The input pulse of a slot that starts at `s`. -/
def externalAt (s : Rat) (y : Pattern 1) : Fin 1 → Option Rat := fun _ => if y 0 then some s else none

/-- The inverter of a slot that starts at `s`: it fires at `s + 5/8` when its input is absent. -/
def invAt (s : Rat) (y : Pattern 1) : Fin 1 → ReadObservation 1 := fun _ =>
  ⟨s, fun _ => externalAt s y 0, if y 0 then [] else [s + 5 / 8], 0⟩

private def read (start : Rat) (x : Pattern M) (score level : Int) : ReadObservation M :=
  datedRead start (Vector.ofFn fun j => if x j then some start else none)
    (if level ≤ score then [start + 1] else []) score

/-- A first-layer read produced by the front end, for a slot starting at `s`. -/
def frontReadAt (s : Rat) (y : Pattern 1) (fires : Bool) : ReadObservation 2 :=
  datedRead (s + 1 / 2) (Vector.ofFn (frontArrival (1 / 2) (externalAt s y) (invAt s y)))
    (if fires then [s + 2] else []) (if fires then 4 else 0)

private def pairs (word : Fin 4) : Pattern 2 := fun j => word.val.testBit (1 - j.val)

/-- Training rounds start at 0 and 10, lessons at 20 and 30, tests at 60. The
target of the conjunction, line 1, is the rails of the absent input, so every
training and teaching stimulus is "input absent", seen through the inverter. -/
def trace : TraceTables cascade where
  firstTrain := Vector.ofFn fun r => Vector.ofFn fun _ => frontReadAt (10 * r.val) absent (r.val ≠ 0)
  teach := Vector.ofFn fun n => Vector.ofFn fun _ => frontReadAt (20 + 10 * n.val) absent true
  secondTrain := Vector.ofFn fun n =>
    read (20 + 10 * n.val + 5 / 2) (singleton 0) (if n.val = 0 then 0 else 4) 2
  firstTest := Vector.ofFn fun word => Vector.ofFn fun _ =>
    if word.val = 1 then frontReadAt 60 absent true
    else if word.val = 2 then frontReadAt 60 present false
    else read (60 + 1 / 2) (pairs word) (if word.val = 3 then 4 else 0) 2
  secondTest := Vector.ofFn fun word => Vector.ofFn fun _ =>
    if word.val = 1 then read (62 + 1 / 2) (fun _ => true) 4 2
    else if word.val = 3 then read 62 (fun _ => true) 4 2
    else read 61 (fun _ => false) 0 2
  scores := Vector.ofFn fun _ => Vector.ofFn fun _ => #v[0, 4]

def checks : Bool := checkCascadeCalibrationOneSided cascade timing timing trace.observations trace.scoreAt

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem accepted : checks = true := by decide +kernel

theorem calibration :
    CascadeCalibrationOneSided cascade timing timing trace.observations trace.scoreAt :=
  cascade_calibration_one_sided_checker_sound _ _ _ _ _ _ _ _ accepted

private theorem inverter_read (s : Rat) (y : Pattern 1) (j : Fin 1) :
    InverterRead inverter (invAt s y j) := by
  refine ⟨by simp only [InverterTiming.Valid, inverter]; decide +kernel, ?_, ?_, ?_⟩
  · intro v arrived
    cases h : y 0 <;> simp [invAt, externalAt, h] at arrived
    subst arrived
    simp only [invAt, inverter]
    constructor <;> grind
  · cases h : y 0 <;> simp [invAt, h, inverter] <;> constructor <;> grind
  · cases h : y 0 <;> simp [invAt, externalAt, h, ReadObservation.fired, ReadObservation.input]

theorem front_end (s : Rat) (y : Pattern 1) (fires : Bool) :
    FrontEnd inverter s (externalAt s y) (invAt s y) (frontReadAt s y fires) := by
  refine ⟨fun j => ⟨rfl, rfl, inverter_read s y j⟩, by simp [frontReadAt, datedRead, inverter], ?_⟩
  funext j
  simp [frontReadAt, datedRead, inverter, Vector.get]
  rfl

private theorem absent_rails (s : Rat) :
    rails (fun j => (externalAt s absent j).isSome) = cascade.first.target 0 := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

private theorem target_eq (a : Fin 1) : cascade.first.target a = cascade.first.target 0 := rfl

/-- (d) Every premise of `trained_inverters_compute` holds at each input pattern. -/
theorem premises_hold (y : Pattern 1) :
    inverter.window ≤ timing.skew ∧ inverter.emitLate - inverter.emitEarly ≤ timing.skew ∧
    InverterTrainingCalibration (M := 1) cascade inverter timing timing trace.observations ∧
    (∀ j, (externalAt 60 y j).isSome = y j) ∧
    InverterFrontRead cascade inverter timing trace.observations y 60 (externalAt 60 y) (invAt 60 y) ∧
    (∀ k, SecondTestRead cascade timing trace.observations trace.scoreAt (rails y) k) := by
  have cal := calibration
  have hy : y = absent ∨ y = present := by
    cases h : y 0
    · exact Or.inl (funext fun j => by rw [Fin.fin_one_eq_zero j, h]; rfl)
    · exact Or.inr (funext fun j => by rw [Fin.fin_one_eq_zero j, h]; rfl)
  refine ⟨by simp only [inverter, timing]; decide +kernel, by simp only [inverter, timing]; decide +kernel,
    ⟨?_, ?_⟩, ?_, ?_, fun k => cal.2.2 (rails y) k⟩
  · -- training rounds
    intro r bound a
    obtain ⟨valid', _, _, emission, decoder, residual⟩ := cal.1.1 r bound a
    refine ⟨?_, ⟨valid', emission, decoder, residual⟩⟩
    have small : r < cascade.first.maxWrites + 1 := Nat.lt_succ_of_le bound
    have row : trace.observations.firstTrain r a = frontReadAt (10 * r) absent (r ≠ 0) := by
      simp [TraceTables.observations, small, trace, Vector.get, Fin.cast]
    rw [row]
    exact ⟨10 * r, externalAt (10 * r) absent, invAt (10 * r) absent, front_end _ _ _,
      (absent_rails _).trans (target_eq a).symm⟩
  · -- lessons
    intro n L atIndex
    obtain ⟨teaching, route, second⟩ := cal.1.2 n L atIndex
    refine ⟨fun a => ?_, route, second⟩
    obtain ⟨valid', _, _, emission, decoder, residual⟩ := teaching a
    refine ⟨?_, ⟨valid', emission, decoder, residual⟩⟩
    have small : n < (lessons cascade).length := (List.getElem?_eq_some_iff.mp atIndex).choose
    have row : trace.observations.teach n a = frontReadAt (20 + 10 * n) absent true := by
      simp [TraceTables.observations, small, trace, Vector.get, Fin.cast]
    rw [row]
    exact ⟨20 + 10 * n, externalAt (20 + 10 * n) absent, invAt (20 + 10 * n) absent, front_end _ _ _,
      (absent_rails _).trans (target_eq L.line).symm⟩
  · intro j
    rw [Fin.fin_one_eq_zero j]
    cases h : y 0 <;> simp [externalAt, h]
  · intro a
    obtain ⟨valid', _, _, emission, decoder, residual⟩ := cal.2.1 (rails y) a
    refine ⟨?_, ⟨valid', emission, decoder, residual⟩⟩
    rcases hy with rfl | rfl
    · have index : maskIndex (rails absent) = ⟨1, by decide⟩ := by decide
      have row : trace.observations.firstTest (rails absent) a = frontReadAt 60 absent true := by
        simp [TraceTables.observations, index, trace, Vector.get, Fin.cast]
      rw [row]
      exact front_end 60 absent true
    · have index : maskIndex (rails present) = ⟨2, by decide⟩ := by decide
      have row : trace.observations.firstTest (rails present) a = frontReadAt 60 present false := by
        simp [TraceTables.observations, index, trace, Vector.get, Fin.cast]
      rw [row]
      exact front_end 60 present false

/-- The trained network, trained and tested through the inverter, answers NOT. -/
theorem answers_not (y : Pattern 1) :
    (trace.observations.secondTest (rails y) 0).fired = !y 0 := by
  obtain ⟨windowFits, spreadFits, training, realised, front, second⟩ := premises_hold y
  rw [trained_inverters_compute valid windowFits spreadFits training realised front second 0,
    predicted_not]

end LearnedCoincidence.MonotoneDNF.InverterTrainingWitness
