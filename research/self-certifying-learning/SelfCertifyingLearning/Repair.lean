import SelfCertifyingLearning.Scheduler

/-! Delayed, saturating repair with a fixed certified loss ceiling. The dose
arrives only at completion. All reserves and costs use integer ticks. -/
namespace SelfCertifyingLearning.Repair

structure Config where
  service : Nat
  bound : Nat
  latency : Nat
  dose : Nat
  capacity : Nat
  maxWait : Nat
  deriving DecidableEq, Repr

def Config.loss (c : Config) : Nat := c.bound * c.latency

def Config.guard (c : Config) : Nat := c.service + c.loss

def Config.target (c : Config) : Nat := c.guard + c.bound

def Config.gain (c : Config) : Nat := c.dose - c.loss

/-- Positive net progress and capacity for a repair buffer plus one tick.
The loss ceiling must remain valid throughout repair, not only an old probe
window. These conditions are explicit and decidable. -/
def Config.Valid (c : Config) : Prop :=
  0 < c.latency ∧ 0 < c.maxWait ∧ c.loss < c.dose ∧ c.target ≤ c.capacity

instance (c : Config) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _))

def Config.Ready (c : Config) (lower : Nat) : Prop := c.guard ≤ lower ∧ lower ≤ c.capacity

instance (c : Config) (lower : Nat) : Decidable (c.Ready lower) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Certified endpoint lower bound: cap the reserve after the delayed dose.
It is used only under Valid; gain truncation cannot authorize a bad config. -/
def pulse (c : Config) (lower : Nat) : Nat := min c.capacity (lower + c.gain)

def pulses (c : Config) : Nat → Nat → Nat
  | 0, lower => lower
  | n + 1, lower => pulses c n (pulse c lower)

theorem gain_positive {c : Config} (valid : c.Valid) : 0 < c.gain := by
  have := valid.2.2.1
  unfold Config.gain
  omega

theorem pulse_ready {c : Config} (valid : c.Valid) {lower : Nat} (ready : c.Ready lower) :
    c.Ready (pulse c lower) := by
  have capacity := valid.2.2.2
  unfold Config.Ready at *
  unfold Config.target at capacity
  unfold pulse
  omega

/-- As long as the endpoint is below the restart target, net gain cannot
be hidden by saturation; the final pulse may reach the capacity instead. -/
theorem pulses_lower {c : Config} (valid : c.Valid) (n lower : Nat) :
    min c.target (lower + n * c.gain) ≤ pulses c n lower := by
  induction n generalizing lower with
  | zero => simp only [pulses, Nat.zero_mul, Nat.add_zero]; omega
  | succ n ih =>
    have next := ih (pulse c lower)
    have capacity := valid.2.2.2
    simp only [pulses, Nat.succ_mul]
    unfold pulse at *
    omega

theorem pulses_ready {c : Config} (valid : c.Valid) (n : Nat) {lower : Nat}
    (ready : c.Ready lower) : c.Ready (pulses c n lower) := by
  induction n generalizing lower with
  | zero => exact ready
  | succ n ih => exact ih (pulse_ready valid ready)

theorem finite_budget_reaches {c : Config} (valid : c.Valid) (budget lower : Nat)
    (enough : c.target ≤ lower + budget * c.gain) :
    c.target ≤ pulses c budget lower := by
  have lowerBound := pulses_lower valid budget lower
  omega

/-- A deliberately simple uniform bound: one pulse per missing tick.
It is not a claim that this bound is optimal. -/
def budget (c : Config) (lower : Nat) : Nat := c.target - lower

theorem budget_suffices {c : Config} (valid : c.Valid) (lower : Nat) :
    c.target ≤ lower + budget c lower * c.gain := by
  have positive := gain_positive valid
  have product := Nat.mul_le_mul_left (budget c lower) positive
  simp only [Nat.mul_one] at product
  unfold budget at *
  omega

/-- Service is preserved before the delayed dose arrives if the entry
reserve includes the complete worst-case repair loss. -/
theorem pulse_interior_safe (c : Config) {lower : Nat} (ready : c.Ready lower)
    (state : Nat → Int) (observed : (lower : Int) ≤ state 0)
    (steps : ∀ k, k < c.latency → state k - (c.bound : Int) ≤ state (k + 1)) :
    SafeUntil state c.service c.latency := by
  apply constant_rate_deadline state lower c.service c.bound c.latency
  · intro k hk
    have enclosure := Scheduler.enclosure_from_steps state c.bound c.latency steps k hk
    omega
  · have := ready.1
    simp only [Config.guard, Config.loss] at this
    omega

/-- The endpoint contract follows from a delayed dose with at least the
configured capacity and dose. It is separate from the per-tick loss bound. -/
theorem pulse_endpoint {c : Config} (valid : c.Valid) {lower : Nat}
    (initial final : Int) (observed : (lower : Int) ≤ initial)
    (delivered : min (c.capacity : Int) (initial - (c.loss : Int) + (c.dose : Int)) ≤ final) :
    (pulse c lower : Int) ≤ final := by
  have positive := valid.2.2.1
  unfold pulse Config.gain
  omega

/-- Endpoint laws for an explicit batch of delayed writes. This may start
below the repair buffer, so it claims restoration, not uninterrupted service. -/
def RecoveryRealizes (c : Config) : Nat → (Nat → Int) → Prop
  | 0, _ => True
  | n + 1, state =>
    min (c.capacity : Int) (state 0 - (c.loss : Int) + (c.dose : Int)) ≤ state c.latency ∧
    RecoveryRealizes c n (fun t => state (c.latency + t))

theorem recovery_endpoint {c : Config} (valid : c.Valid) (n lower : Nat)
    (state : Nat → Int) (observed : (lower : Int) ≤ state 0)
    (realizes : RecoveryRealizes c n state) :
    (pulses c n lower : Int) ≤ state (n * c.latency) := by
  induction n generalizing lower state with
  | zero => simpa only [pulses, Nat.zero_mul] using observed
  | succ n ih =>
    have endpoint := pulse_endpoint valid (state 0) (state c.latency) observed realizes.1
    have tail := ih (pulse c lower) (fun t => state (c.latency + t))
      (by simpa using endpoint) realizes.2
    simpa only [pulses, Nat.succ_mul, Nat.add_comm] using tail

theorem pulses_capacity (c : Config) (n : Nat) {lower : Nat} (bounded : lower ≤ c.capacity) :
    pulses c n lower ≤ c.capacity := by
  induction n generalizing lower with
  | zero => exact bounded
  | succ n ih =>
    apply ih
    unfold pulse
    omega

/-- The finite batch restores both the buffer and the capacity invariant,
even if its initial lower bound is below the service threshold. -/
theorem recovered_ready {c : Config} (valid : c.Valid) {lower : Nat}
    (bounded : lower ≤ c.capacity) : c.Ready (pulses c (budget c lower) lower) := by
  have reached := finite_budget_reaches valid (budget c lower) lower (budget_suffices valid lower)
  have upper := pulses_capacity c (budget c lower) bounded
  unfold Config.Ready Config.target at *
  omega

/-- Explicit finite recovery time, conditional on completing the prescribed
batch under the same loss/dose/capacity contract. Interiors may violate service. -/
theorem recovery_restores {c : Config} (valid : c.Valid) (lower : Nat)
    (state : Nat → Int) (observed : (lower : Int) ≤ state 0)
    (realizes : RecoveryRealizes c (budget c lower) state) :
    (c.target : Int) ≤ state (budget c lower * c.latency) := by
  have endpoint := recovery_endpoint valid (budget c lower) lower state observed realizes
  have reached := finite_budget_reaches valid (budget c lower) lower (budget_suffices valid lower)
  omega

/-- Start a new positive observation window after the repair budget. -/
theorem repaired_plan_exists {c : Config} (valid : c.Valid) (lower : Nat) :
    ∃ delay, Scheduler.plan (pulses c (budget c lower) lower) c.guard c.bound c.maxWait = some delay := by
  apply Scheduler.plan_exists (delay := 1) (by decide) valid.2.1
  have reached := finite_budget_reaches valid (budget c lower) lower (budget_suffices valid lower)
  simp only [Nat.mul_one]
  unfold Config.target at reached
  omega

end SelfCertifyingLearning.Repair
