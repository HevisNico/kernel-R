import SelfCertifyingLearning.Composition
import SelfCertifyingLearning.Deadline

namespace SelfCertifyingLearning.Counterexamples

/-- A bound on corrections does not bound idle or surveillance activity. -/
theorem arbitrary_idle_activity (n : Nat) :
    corrections (List.replicate n Event.idle) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, corrections] using ih

/-! A finite transition system with a working repair and a disconnected
invalid state. Strict rank decrease of enabled repairs alone cannot imply
that every initial state reaches validity: availability is indispensable. -/
namespace MissingAvailability

inductive State where
  | stuck
  | pending
  | good
  deriving DecidableEq

def valid (s : State) : Prop := s = .good

def step (s t : State) : Prop := s = .pending ∧ t = .good

def rank : State → Nat
  | .stuck => 1
  | .pending => 1
  | .good => 0

theorem enabled_repairs_decrease {s t : State} (transition : step s t) : rank t < rank s := by
  obtain ⟨rfl, rfl⟩ := transition
  decide

theorem working_repair : RepairPath step .pending 1 .good :=
  .cons ⟨rfl, rfl⟩ (.nil State.good)

theorem stuck_path {n : Nat} {last : State} (path : RepairPath step .stuck n last) :
    n = 0 ∧ last = .stuck := by
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | cons transition _ => have impossible := transition.1; cases impossible

/-- The reachable-state conclusion of repair_exists fails from stuck,
although another state is repairable and every enabled repair decreases rank. -/
theorem no_valid_path : ¬ ∃ last n, RepairPath step .stuck n last ∧ valid last := by
  rintro ⟨last, n, path, good⟩
  have reached := stuck_path path
  rw [reached.2] at good
  cases good

end MissingAvailability

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
