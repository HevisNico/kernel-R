import SelfCertifyingLearning.Composition
import SelfCertifyingLearning.Deadline

namespace SelfCertifyingLearning.Counterexamples

/-- A bound on corrections does not bound idle or surveillance activity. -/
theorem arbitrary_idle_activity (n : Nat) :
    corrections (List.replicate n Event.idle) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, corrections] using ih

/-- Without availability an incorrect state may have no successor. -/
theorem bad_deadlock : ∃ _s : Unit, ¬ (False : Prop) ∧ ¬ ∃ _t : Unit, False := by
  exact ⟨(), not_false, by simp⟩

/-- Neighbor ratios 4/5, even with pair products 16/25 < 1, do not
provide positive weighted margins for this three-level chain.
This integer certificate rejection needs no spectral calculation. -/
theorem three_level_no_margin (w0 w1 w2 : Nat)
    (left : 4 * w1 + 1 ≤ 5 * w0)
    (middle : 4 * w0 + 4 * w2 + 1 ≤ 5 * w1)
    (right : 4 * w1 + 1 ≤ 5 * w2) : False := by
  omega

/-- Error below half a dose does not fix the count if the nominal
threshold lies on the dose lattice. Scale: ten ticks per dose. -/
theorem half_dose_not_exact_count :
    (1 : Nat) < 10 / 2 ∧ 9 ≤ 10 ∧ ¬ (11 ≤ 10) ∧ 11 ≤ 20 := by decide

/-- Stopping exactly at the threshold provides no downward reserve. -/
theorem threshold_stop_not_robust : (10 : Int) ≥ 10 ∧ ¬ (10 - 1 ≥ 10) := by decide

def reserveTrace (rate k : Nat) : Int := 110 - (rate * k : Nat)

/-- Only the initial probe is visible before the next scheduled probe. -/
def observed (rate k : Nat) : Option Int :=
  if k = 0 then some 110 else if k < 10 then none else some (reserveTrace rate k)

theorem before_probe_identical (k : Nat) (before : k < 10) :
    observed 10 k = observed 22 k := by
  simp [observed, before]

theorem old_rate_safe : SafeUntil (reserveTrace 10) 0 10 := by
  apply constant_rate_deadline (reserveTrace 10) 110 0 10 10
  · intro k _
    exact Int.le_refl _
  · decide

/-- A hidden jump just after the initial observation violates safety
strictly before the next probe, despite identical available observations. -/
theorem jumped_rate_unsafe : ¬ SafeUntil (reserveTrace 22) 0 10 := by
  intro safe
  have bad := safe 6 (by decide)
  simp [reserveTrace] at bad

theorem jump_seen_too_late : 6 < 10 ∧ reserveTrace 22 6 < 0 := by decide

end SelfCertifyingLearning.Counterexamples
