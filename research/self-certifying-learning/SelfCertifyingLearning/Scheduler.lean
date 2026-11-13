import SelfCertifyingLearning.Deadline
import SelfCertifyingLearning.Renewal

/-! A finite executable scheduler. Zero is an internal sentinel; the public
policy returns none when it cannot authorize a positive wait. -/
namespace SelfCertifyingLearning.Scheduler

/-- Largest affordable integer wait up to cap, with zero as fallback. -/
def horizon (initial reserve bound : Nat) : Nat → Nat
  | 0 => 0
  | cap + 1 => if bound * (cap + 1) + reserve ≤ initial then cap + 1
      else horizon initial reserve bound cap

theorem horizon_spec (initial reserve bound cap : Nat) (ready : reserve ≤ initial) :
    horizon initial reserve bound cap ≤ cap ∧
    bound * horizon initial reserve bound cap + reserve ≤ initial ∧
    ∀ delay, delay ≤ cap → bound * delay + reserve ≤ initial →
      delay ≤ horizon initial reserve bound cap := by
  induction cap with
  | zero => simp [horizon]; omega
  | succ cap ih =>
    by_cases fits : bound * (cap + 1) + reserve ≤ initial
    · simp only [horizon, ite_eq_left fits]
      exact ⟨by omega, fits, by intro d hd _; exact hd⟩
    · simp only [horizon, ite_eq_right fits]
      refine ⟨by omega, ih.2.1, ?_⟩
      intro delay within affordable
      apply ih.2.2 delay
      · have different : delay ≠ cap + 1 := by intro equal; subst delay; exact fits affordable
        omega
      · exact affordable

/-- None means repair or abstain; it never means a zero-length service
certificate. The scheduler is deliberately total, including cap = 0. -/
def plan (initial reserve bound cap : Nat) : Option Nat :=
  if reserve ≤ initial then
    let delay := horizon initial reserve bound cap
    if 0 < delay then some delay else none
  else none

theorem plan_spec {initial reserve bound cap delay}
    (accepted : plan initial reserve bound cap = some delay) :
    0 < delay ∧ delay ≤ cap ∧ bound * delay + reserve ≤ initial ∧
    ∀ other, other ≤ cap → bound * other + reserve ≤ initial → other ≤ delay := by
  unfold plan at accepted
  split at accepted
  next ready =>
    dsimp only at accepted
    split at accepted
    next positive =>
      have equal := Option.some.inj accepted
      subst delay
      exact ⟨positive, horizon_spec initial reserve bound cap ready⟩
    next => contradiction
  next => contradiction

/-- Completeness among the policy's admissible positive integer waits. -/
theorem plan_exists {initial reserve bound cap delay} (positive : 0 < delay)
    (within : delay ≤ cap) (affordable : bound * delay + reserve ≤ initial) :
    ∃ chosen, plan initial reserve bound cap = some chosen := by
  have ready : reserve ≤ initial := by omega
  have spec := horizon_spec initial reserve bound cap ready
  have lower := spec.2.2 delay within affordable
  unfold plan
  simp only [ite_eq_left ready]
  have pos : 0 < horizon initial reserve bound cap := by omega
  simp [pos]

/-- Per-tick dynamics imply the full-interval enclosure; safety is not
assumed in the observation. Repairs may add reserve during this interval. -/
theorem enclosure_from_steps (state : Nat → Int) (bound cap : Nat)
    (steps : ∀ k, k < cap → state k - (bound : Int) ≤ state (k + 1)) :
    ∀ k, k ≤ cap → state 0 - (bound * k : Nat) ≤ state k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro within
    have previous := ih (by omega)
    have step := steps k (by omega)
    simp only [Nat.mul_succ, Int.natCast_add]
    omega

/-- An observation lower bound plus an independently valid future loss
bound certifies every time before the selected next observation. -/
theorem plan_safe (state : Nat → Int) {initial reserve bound cap delay : Nat}
    (observed : (initial : Int) ≤ state 0)
    (steps : ∀ k, k < cap → state k - (bound : Int) ≤ state (k + 1))
    (accepted : plan initial reserve bound cap = some delay) :
    SafeUntil state reserve delay := by
  have spec := plan_spec accepted
  apply constant_rate_deadline state initial reserve bound delay
  · intro k hk
    have enclosure := enclosure_from_steps state bound cap steps k (by omega)
    omega
  · exact spec.2.2.1

/-- A known slew limit turns a current interval report into a conservative
rate ceiling over cap ticks. The slew contract is a physical assumption;
it is not inferred from a good past fit. -/
def rateCeiling (report : Renewal.Interval) (slew cap : Nat) : Nat :=
  report.hi + slew * cap

theorem rate_ceiling_sound (report : Renewal.Interval) (truth slew cap : Nat)
    (honest : report.Contains truth) (rate : Nat → Nat)
    (growth : ∀ k, k ≤ cap → rate k ≤ truth + slew * k) :
    ∀ k, k ≤ cap → rate k ≤ rateCeiling report slew cap := by
  intro k hk
  have envelope := growth k hk
  have monotone := Nat.mul_le_mul_left slew hk
  have upper := honest.2
  unfold rateCeiling
  omega

/-- With instantaneous uncapped unit writes, this computable number of
writes restores enough certified reserve for at least one tick. -/
def unitWrites (initial reserve bound : Nat) : Nat := reserve + bound - initial

theorem restored_plan_exists (initial reserve bound cap : Nat) (available : 0 < cap) :
    ∃ chosen, plan (initial + unitWrites initial reserve bound) reserve bound cap = some chosen := by
  apply plan_exists (delay := 1) (by decide) (by omega)
  simp only [Nat.mul_one, unitWrites]
  omega

/-- Executable examples, not an empirical controller comparison. -/
theorem schedule_example : plan 110 10 10 40 = some 10 := by decide

theorem changed_envelope_shortens_wait : plan 110 10 22 40 = some 4 := by decide

theorem insufficient_reserve_refuses_wait : plan 10 10 1 40 = none := by decide

theorem zero_loss_uses_cap : plan 10 10 0 40 = some 40 := by decide

end SelfCertifyingLearning.Scheduler
