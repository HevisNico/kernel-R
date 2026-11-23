import InverterSchedule
import InverterTrainingWitness

/-! The training witness on a schedule fixed in advance. The tables are those of
`InverterTrainingWitness.lean`, repeated here so that a negative control can drive
a training read directly instead of through the front end. The schedule names, for
each training round and lesson, the slot start, the input pulse and the inverter;
every premise of `scheduled_inverters_compute` then holds, and the trained network
answers NOT. -/

namespace LearnedCoincidence.MonotoneDNF.InverterScheduleWitness

open TwoLayer (SlotTiming ReadObservation)
open PremiseCheck
open InverterWitness (cascade timing inverter absent present predicted_not valid)
open InverterTrainingWitness (externalAt invAt frontReadAt front_end)

private def read (start : Rat) (x : Pattern M) (score level : Int) : ReadObservation M :=
  datedRead start (Vector.ofFn fun j => if x j then some start else none)
    (if level ≤ score then [start + 1] else []) score

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

/-- The schedule, fixed before the run: training slots at 0 and 10, lessons at 20
and 30, every stimulus "input absent". -/
def schedule : InverterSchedule 1 1 where
  trainStart r _ := 10 * r
  trainExternal r _ := externalAt (10 * r) absent
  trainInv r _ := invAt (10 * r) absent
  teachStart n _ := 20 + 10 * n
  teachExternal n _ := externalAt (20 + 10 * n) absent
  teachInv n _ := invAt (20 + 10 * n) absent

private theorem absent_rails (s : Rat) :
    rails (fun j => (externalAt s absent j).isSome) = cascade.first.target 0 := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Every premise of `scheduled_inverters_compute` holds at each input pattern. -/
theorem premises_hold (y : Pattern 1) :
    inverter.window ≤ timing.skew ∧ inverter.emitLate - inverter.emitEarly ≤ timing.skew ∧
    ScheduledInverterTraining (M := 1) cascade inverter timing timing trace.observations schedule ∧
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
  · intro r bound a
    obtain ⟨valid', _, _, emission, decoder, residual⟩ := cal.1.1 r bound a
    have small : r < cascade.first.maxWrites + 1 := Nat.lt_succ_of_le bound
    have row : trace.observations.firstTrain r a = frontReadAt (10 * r) absent (r ≠ 0) := by
      simp [TraceTables.observations, small, trace, Vector.get, Fin.cast]
    refine ⟨?_, absent_rails (10 * r), ⟨valid', emission, decoder, residual⟩⟩
    rw [row]
    exact front_end _ _ _
  · intro n L atIndex
    obtain ⟨teaching, route, second⟩ := cal.1.2 n L atIndex
    refine ⟨fun a => ?_, route, second⟩
    obtain ⟨valid', _, _, emission, decoder, residual⟩ := teaching a
    have small : n < (lessons cascade).length := (List.getElem?_eq_some_iff.mp atIndex).choose
    have row : trace.observations.teach n a = frontReadAt (20 + 10 * n) absent true := by
      simp [TraceTables.observations, small, trace, Vector.get, Fin.cast]
    refine ⟨?_, absent_rails (20 + 10 * n), ⟨valid', emission, decoder, residual⟩⟩
    rw [row]
    exact front_end _ _ _
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

/-- Trained on the fixed schedule and tested through the inverter, the network answers NOT. -/
theorem answers_not (y : Pattern 1) :
    (trace.observations.secondTest (rails y) 0).fired = !y 0 := by
  obtain ⟨windowFits, spreadFits, training, realised, front, second⟩ := premises_hold y
  rw [scheduled_inverters_compute valid windowFits spreadFits training realised front second 0,
    predicted_not]

end LearnedCoincidence.MonotoneDNF.InverterScheduleWitness
