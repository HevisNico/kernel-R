import AutonomousFeedback

namespace NetworkStability.AutonomousFeedback

open RoutedCalendar (HasRoom)

def loop : Model 1 Unit where
  cell := fun _ => 0
  bias := fun _ => 1
  drive := fun _ => 0
  route := fun _ => [()]

theorem loop_does_not_terminate (n : Nat) (s : State 1 Unit)
    (queue : s.pending = [()]) :
    (run loop 1 (fun _ => 0) n s).pending = [()] := by
  induction n generalizing s with
  | zero => exact queue
  | succ n ih =>
    apply ih
    have nonnegative : 0 ≤ score loop 1 s () := by
      change 0 ≤ 1 + (1 : Int) * s.writes 0 + 0
      omega
    have fired : fires loop 1 s () 0 = true := by simp [fires, nonnegative]
    have route : loop.route () = [()] := rfl
    simp [step, queue, fired, route]

theorem loop_has_no_strict_margin (weight : Unit → Nat) (eta : Nat) (pos : 0 < eta) :
    ¬ (∀ p, mass weight (loop.route p) + eta ≤ weight p) := by
  intro h
  have stepBound := h ()
  simp [loop, mass] at stepBound
  omega

/-- With unit weights and reserves the singleton loop meets all the
numerical budgets except strict positivity of the scalar decrement. -/
theorem loop_accepts_zero_margin :
    (∀ p, mass (fun _ => 1) (loop.route p) + 0 ≤ 1) ∧
    (∀ p, mass (fun _ => 1) (loop.route p) ≤ 1) ∧
    1 ≤ (1 : Nat) ∧ mass (fun _ => 1) [()] ≤ (1 : Nat) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro p
    cases p
    decide
  · intro p
    cases p
    decide

/-- An extra routed contribution can suppress a write through FIRE. -/
theorem drive_disables_write :
    let weak : Model 1 Unit := { loop with bias := fun _ => -1, route := fun _ => [] }
    let strong : Model 1 Unit := { weak with drive := fun _ => 1 }
    (step weak 1 0 (start 1 [()])).writes 0 = 1 ∧
      (step strong 1 0 (start 1 [()])).writes 0 = 0 := by decide

namespace Ring

/-- There are n+1 input probes, then a positive acknowledgement at cell zero.
A false input is silent, writes once and generates no successor. -/
def model (n : Nat) (bits : Fin (n + 1) → Bool) : Model (n + 1) Nat where
  cell p := if h : p < n + 1 then ⟨p, h⟩ else 0
  bias p := if h : p < n + 1 then (if bits ⟨p, h⟩ then 2 else -3) else 2
  drive p := if p = 0 then 0 else 1
  route p := if p < n + 1 then [p + 1] else []

def weight (n p : Nat) : Nat := n + 2 - min p (n + 1)

def reserve (n : Nat) (i : Fin (n + 1)) (p : Nat) : Nat :=
  (if p ≤ i.val then 1 else 0) + (if i = 0 then 1 else 0)

private theorem reserve_step (n : Nat) (bits : Fin (n + 1) → Bool) (p : Nat)
    (i : Fin (n + 1)) :
    mass (reserve n i) ((model n bits).route p) +
      (if i = (model n bits).cell p then 1 else 0) ≤ reserve n i p := by
  by_cases h : p < n + 1
  · have eq : (i = (⟨p, h⟩ : Fin (n + 1))) ↔ i.val = p := Fin.ext_iff
    simp only [model, h, dite_true, ite_true, mass, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, eq, reserve]
    by_cases same : i.val = p
    · simp [same, show ¬ p + 1 ≤ p by omega, Nat.add_comm]
    · by_cases before : p ≤ i.val
      · have after : p + 1 ≤ i.val := by omega
        simp [same, before, after]
      · have after : ¬ p + 1 ≤ i.val := by omega
        simp [same, before, after]
  · have iv := i.isLt
    simp only [model, h, dite_false, ite_false, mass, List.map_nil, List.sum_nil,
      Nat.zero_add, reserve]
    simp [show ¬ p ≤ i.val by omega]

def certificate (n : Nat) (bits : Fin (n + 1) → Bool) :
    Certificate 2 2 1 (model n bits) [0] where
  weight := weight n
  reserve := reserve n
  eta_pos := by decide
  scalar := by
    intro p
    by_cases h : p < n + 1
    · simp [model, h, mass, weight, Nat.min_eq_left (show p ≤ n + 1 by omega),
        Nat.min_eq_left (show p + 1 ≤ n + 1 by omega)]
      omega
    · simp [model, h, mass, weight, Nat.min_eq_right (show n + 1 ≤ p by omega)]
  local_route := by
    intro p i
    have := reserve_step n bits p i
    omega
  local_write := by
    intro p
    have bound := reserve_step n bits p ((model n bits).cell p)
    simp only [ite_true] at bound
    omega
  seed_weight := by simp [mass, weight]; omega
  seed_reserve := by
    intro i
    by_cases h : i = 0 <;> simp [mass, reserve, h]

private theorem clean_score (n : Nat) (bits : Fin (n + 1) → Bool) (p : Nat)
    (s : State (n + 1) Nat) (clean : ∀ i, s.writes i = 0) :
    score (model n bits) 1 s p =
      (if h : p < n + 1 then (if bits ⟨p, h⟩ then 2 else -3) else 2) +
        (if p = 0 then 0 else 1) := by
  unfold score
  rw [clean]
  change (model n bits).bias p + 1 * (0 : Int) + ((model n bits).drive p : Int) = _
  simp only [Int.mul_zero, Int.add_zero]
  change _ + ((if p = 0 then 0 else 1 : Nat) : Int) = _
  by_cases zero : p = 0 <;> simp only [zero, ite_true, ite_false, Int.ofNat_zero, Int.ofNat_one] <;> rfl

private theorem route_at (n : Nat) (bits : Fin (n + 1) → Bool) (p : Nat) :
    (model n bits).route p = if p < n + 1 then [p + 1] else [] := rfl

private theorem polar_score (n : Nat) (bits : Fin (n + 1) → Bool) (p : Nat)
    (s : State (n + 1) Nat) (clean : ∀ i, s.writes i = 0) :
    let expected := if h : p < n + 1 then bits ⟨p, h⟩ else true
    (expected = true ∧ 1 ≤ score (model n bits) 1 s p) ∨
      (expected = false ∧ score (model n bits) 1 s p < -1) := by
  dsimp only
  rw [clean_score n bits p s clean]
  by_cases h : p < n + 1
  · rw [dite_eq_left h, dite_eq_left h]
    cases bits ⟨p, h⟩
    · refine Or.inr ⟨rfl, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      split <;> decide
    · refine Or.inl ⟨rfl, ?_⟩
      simp only [ite_true]
      split <;> decide
  · rw [dite_eq_right h, dite_eq_right h]
    refine Or.inl ⟨rfl, ?_⟩
    split <;> decide

theorem ring_edges (n : Nat) (bits : Fin (n + 1) → Bool) :
    (∀ i : Fin (n + 1), (model n bits).cell i.val = i ∧
      (model n bits).route i.val = [i.val + 1]) ∧
    (model n bits).cell (n + 1) = 0 ∧ (model n bits).route (n + 1) = [] := by
  constructor
  · intro i
    have within := i.isLt
    simp [model, within]
  · simp [model]

private theorem read_at (n : Nat) (bits : Fin (n + 1) → Bool) (p : Nat)
    (s : State (n + 1) Nat) (clean : ∀ i, s.writes i = 0) (e : Int)
    (within : -1 ≤ e ∧ e ≤ 1) :
    fires (model n bits) 1 s p e = (if h : p < n + 1 then bits ⟨p, h⟩ else true) := by
  unfold fires
  rcases polar_score n bits p s clean with ⟨bit, room⟩ | ⟨bit, room⟩
  · rw [bit]
    exact decide_eq_true (by omega)
  · rw [bit]
    exact decide_eq_false (by omega)

private theorem nominal_room (n : Nat) (bits : Fin (n + 1) → Bool) (p : Nat)
    (s : State (n + 1) Nat) (clean : ∀ i, s.writes i = 0) :
    HasRoom (score (model n bits) 1 s p) (-1) 1 := by
  unfold HasRoom
  rcases polar_score n bits p s clean with ⟨_, room⟩ | ⟨_, room⟩
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inl ⟨by omega, by omega⟩

theorem margins (n : Nat) (bits : Fin (n + 1) → Bool) (fuel p : Nat)
    (s : State (n + 1) Nat) (queue : s.pending = [p]) (clean : ∀ i, s.writes i = 0) :
    NominalMargins (model n bits) 1 (fun _ => -1) (fun _ => 1) fuel s := by
  induction fuel generalizing p s with
  | zero => trivial
  | succ fuel ih =>
    simp only [NominalMargins, queue]
    refine ⟨nominal_room n bits p s clean, ?_⟩
    have decision := read_at n bits p s clean 0 (by decide)
    by_cases h : p < n + 1
    · cases bit : bits ⟨p, h⟩
      · have done : (step (model n bits) 1 0 s).pending = [] := by
          simp [step, queue, decision, h, bit]
        cases fuel <;> simp [NominalMargins, done]
      · apply ih (p + 1)
        · simp [step, queue, decision, route_at, h, bit]
        · intro i
          simp [step, queue, decision, h, bit, clean]
    · have done : (step (model n bits) 1 0 s).pending = [] := by
        simp [step, queue, decision, route_at, h]
      cases fuel <;> simp [NominalMargins, done]

/-- Success is the return probe actually firing, rather than just reaching
the last input cell. The suffix assertion allows arbitrary earlier log entries. -/
theorem acknowledgement (n : Nat) (bits : Fin (n + 1) → Bool)
    (error : Nat → Int) (within : ∀ k, -1 ≤ error k ∧ error k ≤ 1)
    (fuel p : Nat) (s : State (n + 1) Nat) (queue : s.pending = [p])
    (clean : ∀ i, s.writes i = 0) (pBound : p ≤ n + 1)
    (enough : n + 2 - p ≤ fuel) (fresh : (n + 1, true) ∉ s.log) :
    (n + 1, true) ∈ (run (model n bits) 1 error fuel s).log ↔
      ∀ i : Fin (n + 1), p ≤ i.val → bits i = true := by
  induction fuel generalizing p s with
  | zero => omega
  | succ fuel ih =>
    have decision := read_at n bits p s (by exact clean) _ (within s.log.length)
    rw [run]
    by_cases h : p < n + 1
    · have different : n + 1 ≠ p := by omega
      cases bit : bits ⟨p, h⟩
      · have done : (step (model n bits) 1 (error s.log.length) s).pending = [] := by
          simp [step, queue, decision, h, bit]
        rw [run_empty _ _ _ _ _ done]
        constructor
        · intro mem
          simp [step, queue, decision, h, bit, fresh] at mem
        · intro all
          have := all ⟨p, h⟩ (Nat.le_refl _)
          simp [bit] at this
      · have nextQueue : (step (model n bits) 1 (error s.log.length) s).pending = [p + 1] := by
          simp [step, queue, decision, route_at, h, bit]
        have nextClean : ∀ i, (step (model n bits) 1 (error s.log.length) s).writes i = 0 := by
          intro i
          simp [step, queue, decision, h, bit, clean]
        have nextFresh : (n + 1, true) ∉ (step (model n bits) 1 (error s.log.length) s).log := by
          simp [step, queue, decision, h, bit, different, fresh]
        rw [ih (p + 1) _ nextQueue nextClean (by omega) (by omega) nextFresh]
        constructor
        · intro all i hi
          by_cases eq : i.val = p
          · have same : i = (⟨p, h⟩ : Fin (n + 1)) := Fin.ext eq
            simpa [same] using bit
          · exact all i (by omega)
        · intro all i hi
          exact all i (by omega)
    · have eq : p = n + 1 := by omega
      have done : (step (model n bits) 1 (error s.log.length) s).pending = [] := by
        simp [step, queue, decision, route_at, h]
      rw [run_empty _ _ _ _ _ done]
      constructor
      · intro _ i hi
        have := i.isLt
        omega
      · intro _
        simp only [step, queue, decision, h, dite_false]
        simp [eq]

/-- The same certificate works at every size. Only the initial probe is
scheduled externally. The final acknowledgement means all input bits are true. -/
theorem uniform_and (n : Nat) (bits : Fin (n + 1) → Bool) (error : Nat → Int)
    (within : ∀ k, -1 ≤ error k ∧ error k ≤ 1) :
    let terminal := run (model n bits) 1 error (2 * (n + 1)) (start (n + 1) [0])
    terminal.pending = [] ∧
      terminal = run (model n bits) 1 (fun _ => 0) (2 * (n + 1)) (start (n + 1) [0]) ∧
      ((n + 1, true) ∈ terminal.log ↔ ∀ i, bits i = true) ∧
      RoutedCalendar.total ⟨terminal.writes, []⟩ ≤ 2 * (n + 1) ∧
      ∀ i, terminal.writes i ≤ 2 ∧ 1 + terminal.writes i < 4 := by
  have certified := certified_feedback 2 1 1 4 2 1 (model n bits) [0] (certificate n bits)
    (fun _ => 1) (fun _ => by decide) (by decide) (fun _ => -1) (fun _ => 1)
    error within (margins n bits _ 0 _ rfl (fun _ => rfl))
  have task := acknowledgement n bits error within (2 * (n + 1)) 0
    (start (n + 1) [0]) rfl (fun _ => rfl) (by omega) (by omega) (by simp [start])
  obtain ⟨done, same, _, bounds⟩ := certified
  have ⟨total, each⟩ := bounds (2 * (n + 1))
  exact ⟨done, same, by simpa using task, total, fun i => ⟨(each i).1, by simpa using (each i).2.2⟩⟩

end Ring
end NetworkStability.AutonomousFeedback
