import PerpetualFeedback
import FeedbackExamples

namespace NetworkStability.AutonomousFeedback

def loopReserve : LocalReserve 1 loop [()] where
  reserve := fun _ _ => 1
  route := by intro p i; cases p; decide
  write := by intro p; decide
  initial := by intro i; decide

theorem loop_memory_forever (n : Nat) :
    let s := run loop 1 (fun _ => 0) n (start 1 [()])
    s.pending = [()] ∧ s.log.length = n ∧ stored 1 (fun _ => 1) s 0 = 1 := by
  have invariant (s : State 1 Unit) (queue : s.pending = [()]) :
      let t := run loop 1 (fun _ => 0) n s
      t.pending = [()] ∧ t.log.length = s.log.length + n ∧ t.writes = s.writes := by
    induction n generalizing s with
    | zero => exact ⟨queue, by simp [run], rfl⟩
    | succ n ih =>
      have scoreFloor : 0 ≤ score loop 1 s () := by
        change 0 ≤ 1 + 1 * (s.writes 0 : Int) + 0
        omega
      have fire : fires loop 1 s () 0 = true := by simp [fires, scoreFloor]
      have route : loop.route () = [()] := rfl
      have transition : step loop 1 0 s = ⟨[()], s.writes, ((), true) :: s.log⟩ := by
        simp [step, queue, fire, route]
      rw [run, transition]
      obtain ⟨live, log, mem⟩ := ih ⟨[()], s.writes, ((), true) :: s.log⟩ rfl
      exact ⟨live, by simp only [List.length_cons] at log; omega, mem⟩
  obtain ⟨live, log, mem⟩ := invariant (start 1 [()]) rfl
  exact ⟨live, by simpa [start] using log, by unfold stored; rw [mem]; rfl⟩

namespace RecirculatingRing

def successor (p : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(p.val + 1) % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

/-- Negative bias forces the first visit to write. The circulating probe
then stays above its threshold. Its seed is a separate pulse at cell zero. -/
def model (n : Nat) : Model (n + 1) (Option (Fin (n + 1))) where
  cell := fun p => p.getD 0
  bias := fun p => if p.isNone then -2 else 2
  drive := fun _ => 0
  route := fun p => match p with
    | none => []
    | some c => [some (successor c)]

def reserve (n : Nat) (i : Fin (n + 1)) (p : Option (Fin (n + 1))) : Nat :=
  match p with
  | none => if i = 0 then 1 else 0
  | some _ => 1

def certificate (n : Nat) : LocalReserve 2 (model n) [none, some 0] where
  reserve := reserve n
  route := by
    intro p i
    cases p <;> simp [model, reserve, mass]
  write := by
    intro p
    cases p <;> simp [model, reserve]
  initial := by
    intro i
    by_cases h : i = 0 <;> simp [reserve, mass, h]

theorem ring_edges (p : Fin (n + 1)) :
    (model n).cell (some p) = p ∧ (model n).route (some p) = [some (successor p)] := ⟨rfl, rfl⟩

theorem wraps_to_zero (n : Nat) : successor (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = 0 := by
  apply Fin.ext
  simp [successor]

def trained (n : Nat) (p : Fin (n + 1)) (log : List (Option (Fin (n + 1)) × Bool)) :
    State (n + 1) (Option (Fin (n + 1))) :=
  ⟨[some p], fun i => if i = 0 then 1 else 0, log⟩

theorem seed_writes (n : Nat) (e : Int) (within : -1 ≤ e ∧ e ≤ 1) :
    step (model n) 1 e (start (n + 1) [none, some 0]) = trained n 0 [(none, false)] := by
  have fire : fires (model n) 1 (start (n + 1) [none, some 0]) none e = false := by
    unfold fires
    apply decide_eq_false
    change ¬ 0 ≤ -2 + 1 * (0 : Int) + 0 + e
    omega
  let s := start (n + 1) ([none, some 0] : List (Option (Fin (n + 1))))
  change ({ pending := [some 0] ++ (if fires (model n) 1 s none e then (model n).route none else [])
            writes := fun i => 0 + if i = 0 ∧ fires (model n) 1 s none e = false then 1 else 0
            log := [(none, fires (model n) 1 s none e)] } : State (n + 1) _) = _
  have same : fires (model n) 1 s none e = false := fire
  simp [same, trained]

theorem active_fires (n : Nat) (p : Fin (n + 1)) (s : State (n + 1) (Option (Fin (n + 1))))
    (e : Int) (within : -1 ≤ e) : fires (model n) 1 s (some p) e = true := by
  unfold fires
  apply decide_eq_true
  change 0 ≤ 2 + 1 * (s.writes p : Int) + 0 + e
  omega

theorem continuing (n : Nat) (error : Nat → Int) (within : ∀ k, -1 ≤ error k ∧ error k ≤ 1)
    (k : Nat) (p : Fin (n + 1)) (log : List (Option (Fin (n + 1)) × Bool)) :
    let s := run (model n) 1 error k (trained n p log)
    ∃ q, s.pending = [some q] ∧ s.log.length = log.length + k ∧
      s.writes = (trained n p log).writes := by
  induction k generalizing p log with
  | zero => exact ⟨p, rfl, by simp [run, trained], rfl⟩
  | succ k ih =>
    have transition :
        step (model n) 1 (error (trained n p log).log.length) (trained n p log) =
          trained n (successor p) ((some p, true) :: log) := by
      rw [show (trained n p log).log.length = log.length from rfl]
      have queue : (trained n p log).pending = [some p] := rfl
      simp only [step, queue, active_fires n p _ _ (within log.length).1]
      simp [trained, model]
    rw [run, transition]
    obtain ⟨q, live, size, values⟩ := ih (successor p) ((some p, true) :: log)
    exact ⟨q, live, by simp only [List.length_cons] at size; omega, values⟩

/-- There is an actual write at the seed, after which one probe circulates
forever and each successive step adds one FIRE to the log. -/
theorem one_write_then_perpetual (n : Nat) (error : Nat → Int)
    (within : ∀ k, -1 ≤ error k ∧ error k ≤ 1) (k : Nat) :
    let s := run (model n) 1 error (k + 1) (start (n + 1) [none, some 0])
    (∃ q, s.pending = [some q]) ∧ s.log.length = 1 + k ∧
      (∀ i, s.writes i = if i = 0 then 1 else 0) ∧
      ∀ i, stored 1 (fun _ => 1) s i < 4 := by
  have atSeed : run (model n) 1 error (k + 1) (start (n + 1) [none, some 0]) =
      run (model n) 1 error k (trained n 0 [(none, false)]) := by
    rw [run]
    apply congrArg (run (model n) 1 error k)
    exact seed_writes n _ (within 0)
  simp only [atSeed]
  obtain ⟨q, live, size, values⟩ := continuing n error within k 0 [(none, false)]
  refine ⟨⟨q, live⟩, size, fun i => congrFun values i, ?_⟩
  intro i
  unfold stored
  rw [values]
  simp only [trained, Nat.one_mul]
  split <;> decide

end RecirculatingRing
end NetworkStability.AutonomousFeedback
