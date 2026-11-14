import NetworkTheorem
import PerpetualExamples

namespace NetworkStability.AutonomousFeedback.Schedule

open RecirculatingRing

/-- Continuously service the circulating token, leaving the training probe
pending forever. The resulting run is active at every step. -/
def starvedState (k : Nat) : State 2 (Option (Fin 2)) :=
  ⟨[none, some ⟨k % 2, Nat.mod_lt _ (by decide)⟩], fun _ => 0,
    (List.range k).reverse.map (fun j => (some ⟨j % 2, Nat.mod_lt _ (by decide)⟩, true))⟩

private theorem next_cell (k : Nat) :
    successor (⟨k % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
      ⟨(k + 1) % 2, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  change ((k % 2 + 1) % 2) = (k + 1) % 2
  omega

def starved : Execution (model 1) 1 [none, some 0] where
  state := starvedState
  initial := rfl
  next := by
    intro k
    let p : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by decide)⟩
    have stepEq :
        step (model 1) 1 0 { starvedState k with pending := [some p, none] } =
          starvedState (k + 1) := by
      have next := next_cell k
      have fire : fires (model 1) 1
          { starvedState k with pending := [some p, none] } (some p) 0 = true := by
        apply active_fires
        decide
      simp only [step, fire, Bool.true_eq_false, and_false, ite_false, ite_true, Nat.add_zero]
      simp [starvedState, model, List.range_succ, p, next]
    rw [← stepEq]
    refine .cons [none] [] (some p) rfl 0 0 0 (by decide) ?_ (.nil _)
    change (2 < 0 ∧ 2 + 0 < 0) ∨ (0 ≤ (2 : Int) ∧ 0 ≤ 2 + 0)
    decide

theorem starved_frozen : Stable starved (fun _ => 0) :=
  ⟨0, fun _ _ => rfl⟩

theorem starved_keeps_processing (n : Nat) :
    (starved.state n).pending.length = 2 ∧ (starved.state n).log.length = n := by
  simp [starved, starvedState]

theorem starved_is_unfair : ¬ WriteFair starved := by
  intro fair
  let t := process (model 1) 1 (project (starved.state 0)) none [some 0]
  have mv : Move (model 1) 1 (project (starved.state 0)) t :=
    Move.select _ _ _ (List.Perm.refl _)
  obtain ⟨j, _, catches⟩ := fair 0 t (.cons mv (.nil _)) 0
  change 1 ≤ 0 at catches
  omega

/-- A pending training probe still owns its credit. The circulating token
is also preserved by each clean move, so the local room holds throughout. -/
private theorem circulating {s t : Config 2 (Option (Fin 2))}
    (mv : Move (model 1) 1 s t) (live : ∃ p, some p ∈ s.pending) :
    ∃ p, some p ∈ t.pending := by
  cases mv with
  | select p tail available =>
    cases p with
    | none =>
      obtain ⟨q, qmem⟩ := live
      have inTail : some q ∈ tail := by simpa using available.mem_iff.mp qmem
      exact ⟨q, List.mem_append_left _ inTail⟩
    | some p =>
      have fire : read (model 1) 1 s (some p) = true :=
        active_fires 1 p ⟨s.pending, s.writes, []⟩ 0 (by decide)
      refine ⟨successor p, ?_⟩
      change some (successor p) ∈ tail ++ emitted (model 1) (some p) (read (model 1) 1 s (some p))
      rw [fire]
      simp [emitted, model]

theorem starvation_model_has_diamonds (s : Config 2 (Option (Fin 2)))
    (path : Path (model 1) 1 (seedConfig 2 [none, some 0]) s) :
    PairMargins (model 1) 1 s := by
  have live : ∃ p, some p ∈ s.pending := by
    have aux {a b : Config 2 (Option (Fin 2))} (r : Path (model 1) 1 a b)
        (h : ∃ p, some p ∈ a.pending) : ∃ p, some p ∈ b.pending := by
      induction r with
      | nil => exact h
      | cons mv _ ih => exact ih (circulating mv h)
    exact aux path ⟨0, by simp [seedConfig]⟩
  intro p hp q _ _ _
  cases p with
  | none =>
    have credits := path_reserve (certificate 1) path 0
    change s.writes 0 + mass ((certificate 1).reserve 0) s.pending ≤ 2 at credits
    obtain ⟨c, mem⟩ := live
    have enough (xs : List (Option (Fin 2))) (a : none ∈ xs) (b : some c ∈ xs) :
        2 ≤ mass ((certificate 1).reserve 0) xs := by
      induction xs with
      | nil => simp at a
      | cons head tail ih =>
        have length : mass ((certificate 1).reserve 0) (head :: tail) =
            1 + mass ((certificate 1).reserve 0) tail := by cases head <;> rfl
        rw [length]
        cases head with
        | none =>
          have rest : some c ∈ tail := by simpa using b
          obtain ⟨before, after, eq⟩ := List.append_of_mem rest
          rw [eq, mass_append]
          simp [mass, certificate, reserve] <;> omega
        | some d =>
          have rest : none ∈ tail := by simpa using a
          obtain ⟨before, after, eq⟩ := List.append_of_mem rest
          rw [eq, mass_append]
          simp [mass, certificate, reserve] <;> omega
    have := enough s.pending hp mem
    have zero : s.writes 0 = 0 := by omega
    apply Or.inl
    change (-2 + 1 * (s.writes 0 : Int) + 0 < 0) ∧
      (-2 + 1 * (s.writes 0 : Int) + 0 + 1 * 1 + 0 < 0)
    omega
  | some p =>
    apply Or.inr
    change (0 ≤ 2 + 1 * (s.writes p : Int) + 0) ∧
      (0 ≤ 2 + 1 * (s.writes p : Int) + 0 + 0)
    omega

def trainedState (n : Nat) : State 2 (Option (Fin 2)) :=
  match n with
  | 0 => start 2 [none, some 0]
  | k + 1 =>
    trained 1 ⟨k % 2, Nat.mod_lt _ (by decide)⟩
      ((starvedState k).log ++ [(none, false)])

def served : Execution (model 1) 1 [none, some 0] where
  state := trainedState
  initial := rfl
  next := by
    intro k
    cases k with
    | zero =>
      have stepEq : step (model 1) 1 0 (start 2 [none, some 0]) = trainedState 1 :=
        seed_writes 1 0 (by decide)
      rw [← stepEq]
      exact .cons [] [some 0] none rfl 0 0 0 (by decide)
        (Or.inl ⟨by decide, by decide⟩) (.nil _)
    | succ k =>
      let p : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by decide)⟩
      have fire : fires (model 1) 1 (trainedState (k + 1)) (some p) 0 = true :=
        active_fires 1 p _ 0 (by decide)
      have stepEq : step (model 1) 1 0 (trainedState (k + 1)) = trainedState (k + 2) := by
        have queue : (trainedState (k + 1)).pending = [some p] := rfl
        simp only [step, queue, fire, Bool.true_eq_false, and_false, ite_false, ite_true, Nat.add_zero]
        simp [trainedState, trained, starvedState, model, List.range_succ, List.cons_append, p, next_cell k]
      rw [← stepEq]
      refine .cons [] [] (some p) rfl 0 0 0 (by decide) ?_ (.nil _)
      have nonnegative : 0 ≤ score (model 1) 1 (trainedState (k + 1)) (some p) := by
        change 0 ≤ 2 + 1 * ((trainedState (k + 1)).writes p : Int) + 0
        omega
      exact Or.inr ⟨nonnegative, by simpa using nonnegative⟩

theorem served_frozen : Stable served (fun i => if i = 0 then 1 else 0) := by
  refine ⟨1, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n => rfl

theorem served_keeps_processing (n : Nat) :
    (served.state n).pending ≠ [] ∧ (served.state n).log.length = n := by
  cases n with
  | zero => decide
  | succ n => simp [served, trainedState, trained, starvedState]

/-- The failure persists with a finite reserve, strong diamonds and a
nonempty queue at every sample along both executions. -/
theorem different_stable_memories_without_fairness :
    Stable starved (fun _ => 0) ∧ Stable served (fun i => if i = 0 then 1 else 0) ∧
      (∀ n, (starved.state n).pending ≠ [] ∧ (served.state n).pending ≠ []) ∧
      (fun _ : Fin 2 => (0 : Nat)) ≠ (fun i => if i = 0 then 1 else 0) := by
  refine ⟨starved_frozen, served_frozen, fun n => ⟨?_, (served_keeps_processing n).1⟩, ?_⟩
  · simp [starved, starvedState]
  · intro eq
    have h := congrFun eq 0
    change 0 = 1 at h
    omega

end NetworkStability.AutonomousFeedback.Schedule
