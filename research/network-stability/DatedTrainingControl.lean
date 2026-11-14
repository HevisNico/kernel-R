import DatedNetwork
import ReciprocalClosure

import Mathlib.Data.Nat.Order.Lemmas
namespace NetworkStability.NativeReciprocal

open AutonomousFeedback.Schedule (Config)
open PhaseAdmission
open KernelR.Hybrid

def trainingCalendar : Calendar 2 Nat Unit where
  cell := fun _ => 0
  secondPort := fun _ => false
  phase := fun _ _ => .ready
  bias := fun _ _ => -5
  recoveryWeight := fun _ _ => 0
  learn := fun _ _ => true
  mark := fun _ _ _ => false
  route := fun _ => []

def trainingProbe (t : Nat) : Occurrence Nat Unit := ⟨t, ()⟩

def trainingSeed : List (Occurrence Nat Unit) :=
  [trainingProbe 0, trainingProbe 8, trainingProbe 16, trainingProbe 24]

def trainingStart : Config 6 (Occurrence Nat Unit) := MarkFeedback.initial 2 trainingSeed

theorem trainingDates_tie_admissible : TieAdmissible trainingCalendar 2 trainingStart := by
  intro s reach p q ep eq ne
  have dates : p.due = q.due := Nat.le_antisymm (ep.2 q eq.1) (eq.2 p ep.1)
  have identical : p = q := by
    cases p
    cases q
    simp_all
  exact (ne identical).elim

def trainingEnd : Config 6 (Occurrence Nat Unit) :=
  MarkFeedback.fifo trainingCalendar.model 2 (fun _ => 0) trainingStart 4

set_option maxRecDepth 2048 in
theorem training_dates_replay :
    Trace trainingCalendar 2 (· ≤ ·) trainingStart
      [(trainingProbe 0, false), (trainingProbe 8, false), (trainingProbe 16, false),
        (trainingProbe 24, true)] trainingEnd := by
  let s1 := MarkFeedback.process trainingCalendar.model 2 trainingStart (trainingProbe 0)
    [trainingProbe 8, trainingProbe 16, trainingProbe 24] 0
  let s2 := MarkFeedback.process trainingCalendar.model 2 s1 (trainingProbe 8)
    [trainingProbe 16, trainingProbe 24] 0
  let s3 := MarkFeedback.process trainingCalendar.model 2 s2 (trainingProbe 16) [trainingProbe 24] 0
  have r0 : RoutedCalendar.HasRoom (MarkFeedback.score trainingCalendar.model 2 trainingStart (trainingProbe 0)) 0 0 :=
    Or.inl ⟨by decide, by decide⟩
  have r1 : RoutedCalendar.HasRoom (MarkFeedback.score trainingCalendar.model 2 s1 (trainingProbe 8)) 0 0 :=
    Or.inl ⟨by decide, by decide⟩
  have r2 : RoutedCalendar.HasRoom (MarkFeedback.score trainingCalendar.model 2 s2 (trainingProbe 16)) 0 0 :=
    Or.inl ⟨by decide, by decide⟩
  have r3 : RoutedCalendar.HasRoom (MarkFeedback.score trainingCalendar.model 2 s3 (trainingProbe 24)) 0 0 :=
    Or.inr ⟨by decide, by decide⟩
  have e0 : Earliest (· ≤ ·) (trainingProbe 0) [trainingProbe 8, trainingProbe 16, trainingProbe 24] := by
    simp [Earliest, trainingProbe]
  have e1 : Earliest (· ≤ ·) (trainingProbe 8) [trainingProbe 16, trainingProbe 24] := by
    simp [Earliest, trainingProbe]
  have e2 : Earliest (· ≤ ·) (trainingProbe 16) [trainingProbe 24] := by
    simp [Earliest, trainingProbe]
  have e3 : Earliest (· ≤ ·) (trainingProbe 24) [] := by simp [Earliest]
  exact .cons _ _ (List.Perm.refl _) e0 0 0 0 ⟨Int.le_refl _, Int.le_refl _⟩ r0
    (.cons _ _ (List.Perm.refl _) e1 0 0 0 ⟨Int.le_refl _, Int.le_refl _⟩ r1
      (.cons _ _ (List.Perm.refl _) e2 0 0 0 ⟨Int.le_refl _, Int.le_refl _⟩ r2
        (.cons _ _ (List.Perm.refl _) e3 0 0 0 ⟨Int.le_refl _, Int.le_refl _⟩ r3 (.nil _))))

theorem training_rejects_global : ¬ MarkFeedback.Admissible trainingCalendar.model 2 trainingStart := by
  intro global
  let M := trainingCalendar.model
  let a := trainingProbe 0
  let b := trainingProbe 8
  let c := trainingProbe 16
  let p := trainingProbe 24
  let s1 := MarkFeedback.process M 2 trainingStart a [b,c,p] 0
  let s2 := MarkFeedback.process M 2 s1 b [c,p] 0
  have reach : MarkFeedback.Path M 2 trainingStart s2 :=
    .cons (.select _ _ _ (List.Perm.refl _)) (.cons (.select _ _ _ (List.Perm.refl _)) (.nil _))
  have perm : s2.pending.Perm (p :: c :: []) := List.Perm.swap _ _ _
  have same := MarkFeedback.read_stable M 2 s2 (global s2 reach) perm
    (show p ≠ c by decide) (tail := [p])
  exact Bool.noConfusion (show true = false from same)


theorem training_causal : Causal trainingCalendar := by
  intro p q h
  simp [trainingCalendar] at h

def trainingReserve : MarkFeedback.Reserve 4 trainingCalendar.model trainingSeed where
  credit := fun _ _ => 1
  pays := by
    intro p fire i
    cases fire <;> simp [MarkFeedback.emitted, MarkFeedback.footprint, Calendar.model,
      trainingCalendar, AutonomousFeedback.mass]
    split <;> decide
  seed_bound := by intro i; decide

/-- A concrete date-24 control. The dated network theorem certifies the
training prefix and its normalized memory. The native comparison is
through the first FIRE and uses its actual preceding physical dose. -/
theorem training_dated_memory :
    (∀ s, MarkFeedback.Path trainingCalendar.model 2 trainingStart s →
      AutonomousFeedback.Schedule.SafeMemory 4 2 0 9 (fun _ => 0) s) ∧
    trainingEnd.pending = [] ∧
    (∀ i : Fin 6, trainingEnd.writes i =
      if i = MarkFeedback.gain trainingCalendar.model (trainingProbe 24) then 3 else 0) ∧
    ∃ witness : KernelR.Hybrid.BirthFirstFire KernelR.FutureControls.parameters
        (fun _ _ => []) nominalStart,
      witness.weak.final.time = (24 : ℝ) ∧
      witness.final.x 0 (.z 0) = nominalStart.x 0 (.z 0) +
        (3 / 5 : ℝ) * trainingEnd.writes (MarkFeedback.gain trainingCalendar.model (trainingProbe 24)) := by
  obtain ⟨safe, _, _, _, _, _, _, _⟩ :=
    dated_network_memory 4 2 0 9 2 1 trainingCalendar trainingSeed trainingReserve
      (fun _ => 0) (fun _ => by decide) (by decide) training_causal trainingDates_tie_admissible
  have counts : ∀ i : Fin 6, trainingEnd.writes i =
      if i = MarkFeedback.gain trainingCalendar.model (trainingProbe 24) then 3 else 0 := by
    decide
  refine ⟨fun s path => (safe s path).1, by decide, counts, ?_⟩
  obtain ⟨witness, date, _, _, _, _, _, _, _, _⟩ := birth_first_strong_native_certificate
  refine ⟨witness, date, ?_⟩
  rw [witness.gain_target, counts]
  norm_num

end NetworkStability.NativeReciprocal
