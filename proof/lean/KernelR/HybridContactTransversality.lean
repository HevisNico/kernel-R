import KernelR.HybridPulseTransversality
import KernelR.HybridExecutionTools

/-! Positive READY fields at actual FIRE and MARK jumps, and the bridge from
the smooth scalar responses to those physical fields before raw expiry. -/
namespace KernelR.Hybrid
open Set

def Jump.ContactTransversal {n route s u} (θ : Fin n → Parameters) :
    @Jump n route s u → Prop
  | .fire _ i _ _ => 0 < field θ s s.x s.time i .q
  | .mark _ i p _ _ => 0 < field θ s s.x s.time i (.m p)
  | _ => True

def Execution.ContactsTransversal {n θ route s u} : @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow _) rest => rest.ContactsTransversal
  | .cons (.jump jump) rest => jump.ContactTransversal θ ∧ rest.ContactsTransversal

@[simp] theorem Execution.contactsTransversal_nil {n θ route} (s : Snapshot n) :
    (@Execution.nil n θ route s).ContactsTransversal := trivial

@[simp] theorem Execution.contactsTransversal_flow {n θ route s u v}
    (flow : @Flow n θ s u) (rest : Execution θ route u v) :
    (Execution.cons (.flow flow) rest).ContactsTransversal ↔ rest.ContactsTransversal := Iff.rfl

@[simp] theorem Execution.contactsTransversal_jump {n θ route s u v}
    (jump : @Jump n route s u) (rest : Execution θ route u v) :
    (Execution.cons (.jump jump) rest).ContactsTransversal ↔
      jump.ContactTransversal θ ∧ rest.ContactsTransversal := Iff.rfl

@[simp] theorem Execution.contactsTransversal_append {n θ route s u v}
    (first : @Execution n θ route s u) (rest : Execution θ route u v) :
    (first.append rest).ContactsTransversal ↔
      first.ContactsTransversal ∧ rest.ContactsTransversal := by
  induction first with
  | nil => simp [Execution.append, Execution.ContactsTransversal]
  | cons move tail ih =>
    cases move <;> simp [Execution.append, Execution.ContactsTransversal, ih, and_assoc]

/-- A READY field observes the actual retained raw origin strictly before
expiry. Other ports may be absent independently of the pending queue. -/
theorem ready_single_pulse_field {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : ℝ) (mode : s.main i = .ready) (active : s.raw i p = some origin)
    (others : ∀ q, q ≠ p → s.raw i q = none)
    (inside : origin ≤ s.time ∧ s.time < origin + 1) :
    field θ s s.x s.time i .q = (1 / 2) * (1 / 10 - s.x i .q) +
      Real.exp (s.x i (.z p)) * a * Real.exp (-a * (s.time - origin)) := by
  classical
  simp only [field, mode]
  congr 1
  unfold drive
  rw [Finset.sum_eq_single p]
  · simp [current, active, pulse, inside.1, inside.2, mul_assoc]
  · intro q _ hq
    simp [current, others q hq]
  · simp

theorem aux_single_pulse_field {n θ} (s : Snapshot n) (i : Fin n) (p : Port)
    (origin : ℝ) (mode : s.aux i p = .ready) (active : s.raw i p = some origin)
    (inside : origin ≤ s.time ∧ s.time < origin + 1) :
    field θ s s.x s.time i (.m p) = (1 / 2) * (1 / 40 - s.x i (.m p)) +
      (θ i).inputGain p * a * Real.exp (-a * (s.time - origin)) := by
  simp [field, mode, current, active, pulse, inside.1, inside.2, mul_assoc]

/-- Exact equality at the incoming endpoint, with the original raw tail and
the gain frozen by absence of ERROR on its port. -/
theorem Flow.ready_contact_field_eq_deriv {n θ s u} (flow : @Flow n θ s u)
    (i : Fin n) (p : Port) (origin : ℝ) (mode : s.main i = .ready)
    (active : s.raw i p = some origin) (others : ∀ q, q ≠ p → s.raw i q = none)
    (noError : s.aux i p ≠ .error) (beforeExpiry : u.time < origin + 1) :
    field θ u u.x u.time i .q = deriv
      (readyPulse (s.x i .q)
        (Real.exp (s.x i (.z p)) * Real.exp (-a * (s.time - origin))) s.time) u.time := by
  have interval : u.time ∈ Icc s.time u.time := ⟨flow.positive.le, le_rfl⟩
  have charge := flow.ready_single_pulse_solution i p origin mode active others noError u.time interval
  have gain := flow.gain_constant_without_error i p noError u.time interval
  rw [flow.final] at charge gain
  have startBound := (flow.raw_support i p origin active).1
  rw [ready_single_pulse_field u i p origin
    (by simpa only [flow.main_fixed] using mode)
    (by simpa only [flow.raw_fixed] using active)
    (by simpa only [flow.raw_fixed] using others)
    ⟨startBound.trans flow.positive.le, beforeExpiry⟩]
  rw [(readyPulse_derivative _ _ _ _).deriv, charge, gain]
  have split : Real.exp (-a * (u.time - origin)) =
      Real.exp (-a * (s.time - origin)) * Real.exp (-a * (u.time - s.time)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [split]
  ring

theorem Flow.aux_contact_field_eq_deriv {n θ s u} (flow : @Flow n θ s u)
    (i : Fin n) (p : Port) (origin : ℝ) (mode : s.aux i p = .ready)
    (active : s.raw i p = some origin) (beforeExpiry : u.time < origin + 1) :
    field θ u u.x u.time i (.m p) = deriv
      (auxPulse (s.x i (.m p))
        ((θ i).inputGain p * Real.exp (-a * (s.time - origin))) s.time) u.time := by
  have interval : u.time ∈ Icc s.time u.time := ⟨flow.positive.le, le_rfl⟩
  have charge := flow.aux_ready_single_pulse_solution i p origin mode active u.time interval
  rw [flow.final] at charge
  have startBound := (flow.raw_support i p origin active).1
  rw [aux_single_pulse_field u i p origin
    (by simpa only [flow.aux_fixed] using mode)
    (by simpa only [flow.raw_fixed] using active)
    ⟨startBound.trans flow.positive.le, beforeExpiry⟩]
  rw [(auxPulse_derivative _ _ _ _).deriv, charge]
  have split : Real.exp (-a * (u.time - origin)) =
      Real.exp (-a * (s.time - origin)) * Real.exp (-a * (u.time - s.time)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [split]
  ring

/-- An input installed at the flow's initial date has unit initial raw
attenuation, so its scalar contact certificate gives the actual MARK field. -/
theorem Flow.aux_contact_field_positive {n θ s u} (flow : @Flow n θ s u)
    (i : Fin n) (p : Port) (mode : s.aux i p = .ready)
    (active : s.raw i p = some s.time) (beforeExpiry : u.time < s.time + 1)
    (slope : 0 < deriv (auxPulse (s.x i (.m p)) ((θ i).inputGain p) s.time) u.time) :
    0 < field θ u u.x u.time i (.m p) := by
  rw [flow.aux_contact_field_eq_deriv i p s.time mode active beforeExpiry]
  simpa only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] using slope

#print axioms Flow.ready_contact_field_eq_deriv
#print axioms Flow.aux_contact_field_eq_deriv

end KernelR.Hybrid
