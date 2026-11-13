import SelfCertifyingLearning.Repair

namespace RefusalRecovery

/-- A signed lower bound is retained even below zero. This is an endpoint
update after one complete period and its delayed dose, never an interior
service assertion. -/
def signedPulse (capacity gain lower : Int) : Int := min capacity (lower + gain)

def signedPulses (capacity gain : Int) : Nat → Int → Int
  | 0, lower => lower
  | n + 1, lower => signedPulses capacity gain n (signedPulse capacity gain lower)

/-- One-period dose/loss laws for continuously commanded recovery. The law
must hold for every period, including periods before the reserve recovers.
No validity of the revoked contract is inferred from these hypotheses. -/
def SignedRecoveryRealizes (capacity gain : Int) : Nat → (Nat → Int) → Prop
  | 0, _ => True
  | n + 1, state =>
    min capacity (state 0 + gain) ≤ state 1 ∧
    SignedRecoveryRealizes capacity gain n (fun t => state (1 + t))

theorem signed_pulse_monotone (capacity gain : Int) {lower actual : Int}
    (observed : lower ≤ actual) :
    signedPulse capacity gain lower ≤ signedPulse capacity gain actual := by
  unfold signedPulse
  omega

/-- Propagate a fresh signed lower bound through exactly n delayed writes.
This remains sound even if gain is nonpositive, but promises no restoration. -/
theorem signed_recovery_endpoint (capacity gain : Int) (n : Nat) (lower : Int)
    (state : Nat → Int) (observed : lower ≤ state 0)
    (realizes : SignedRecoveryRealizes capacity gain n state) :
    signedPulses capacity gain n lower ≤ state n := by
  induction n generalizing lower state with
  | zero => exact observed
  | succ n ih =>
    have first := signed_pulse_monotone capacity gain observed
    have delivered := realizes.1
    have next : signedPulse capacity gain lower ≤ state 1 := by
      unfold signedPulse at first ⊢
      omega
    have last := ih (signedPulse capacity gain lower) (fun t => state (1 + t)) next realizes.2
    simpa [signedPulses, Nat.add_comm] using last

/-- Saturation does not prevent progress to a target inside capacity. -/
theorem signed_pulses_lower (capacity gain target : Int)
    (nonnegative : 0 ≤ gain) (room : target ≤ capacity) (n : Nat) (lower : Int) :
    min target (lower + (n : Int) * gain) ≤ signedPulses capacity gain n lower := by
  induction n generalizing lower with
  | zero => simp only [signedPulses, Int.natCast_zero, Int.zero_mul, Int.add_zero]; omega
  | succ n ih =>
    have next := ih (signedPulse capacity gain lower)
    have paid := Int.mul_nonneg (show 0 ≤ (n : Int) by omega) nonnegative
    simp only [signedPulses, Int.natCast_succ, Int.add_mul, Int.one_mul]
    unfold signedPulse at next ⊢
    omega

theorem signed_budget_reaches (capacity gain target : Int)
    (nonnegative : 0 ≤ gain) (room : target ≤ capacity) (n : Nat) (lower : Int)
    (enough : target ≤ lower + (n : Int) * gain) :
    target ≤ signedPulses capacity gain n lower := by
  have bounded := signed_pulses_lower capacity gain target nonnegative room n lower
  omega

/-- A conservative uniform count: one write per missing reserve tick.
Converting the nonnegative deficit to Nat never clips the reserve itself. -/
def signedRecoveryBudget (target lower : Int) : Nat := (target - lower).toNat

theorem signed_budget_suffices (gain target lower : Int) (positive : 0 < gain) :
    target ≤ lower + (signedRecoveryBudget target lower : Int) * gain := by
  have unit : (1 : Int) ≤ gain := by omega
  have count : 0 ≤ (signedRecoveryBudget target lower : Int) := by omega
  have paid := Int.mul_le_mul_of_nonneg_left unit count
  simp only [Int.mul_one] at paid
  unfold signedRecoveryBudget at *
  omega

/-- A finite endpoint restoration theorem, conditional on positive net gain,
capacity, and all actual delayed deliveries. It permits unsafe interiors. -/
theorem signed_recovery_restores (capacity gain target lower : Int)
    (positive : 0 < gain) (room : target ≤ capacity)
    (state : Nat → Int) (observed : lower ≤ state 0)
    (realizes : SignedRecoveryRealizes capacity gain (signedRecoveryBudget target lower) state) :
    target ≤ state (signedRecoveryBudget target lower) := by
  have endpoint := signed_recovery_endpoint capacity gain _ lower state observed realizes
  have reached := signed_budget_reaches capacity gain target (by omega) room
    (signedRecoveryBudget target lower) lower (signed_budget_suffices gain target lower positive)
  omega

/-- Relate the signed endpoint law to an actual loss bound and delivered dose.
No Ready hypothesis is required; recovery may start below service or zero. -/
theorem signed_delivery_from_physics (capacity dose loss initial final : Int)
    (delivered : min capacity (initial - loss + dose) ≤ final) :
    signedPulse capacity (dose - loss) initial ≤ final := by
  unfold signedPulse
  omega

/-- The v3 fresh lower -64 is not replaced by zero. With a newly justified
loss ceiling 150 and dose 220, five delayed doses give lower 286. This is
an arithmetic example, not evidence that a future ceiling is physically true. -/
theorem signed_negative_entry_example :
    (List.range 6).map (fun n => signedPulses 660 (220 - 150) n (-64)) =
      [-64, 6, 76, 146, 216, 286] := by decide

theorem signed_five_writes_reach_guard :
    250 ≤ signedPulses 660 (220 - 150) 5 (-64) := by decide

theorem signed_negative_entry_not_safe : signedPulses 660 70 0 (-64) < 100 := by decide

theorem signed_zero_gain_persists (capacity lower : Int) (bounded : lower ≤ capacity) (n : Nat) :
    signedPulses capacity 0 n lower = lower := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have capped : min capacity lower = lower := by omega
    simpa [signedPulses, signedPulse, capped] using ih

theorem signed_zero_gain_does_not_restore : signedPulses 660 0 100 (-64) = -64 :=
  signed_zero_gain_persists 660 (-64) (by decide) 100

end RefusalRecovery
