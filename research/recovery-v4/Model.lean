import RefusalRecovery.Runtime
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace RecoveryV4
open SelfCertifyingLearning

def leakage (time : Nat) : Nat := if time < 661 then 10 else 140

theorem root_ceiling_from_registered_plant (now k : Nat) (issued : 666 ≤ now) :
    leakage (now + k) ≤ 150 := by
  have afterJump : ¬ now + k < 661 := by omega
  simp [leakage, afterJump]

theorem root_covers_declared_interval (time : Nat) (issued : 666 ≤ time)
    (_unexpired : time ≤ 1640) : leakage time ≤ 150 := by
  simpa using root_ceiling_from_registered_plant time 0 issued

def rootConfig : Repair.Config := ⟨100, 150, 1, 220, 660, 40⟩

theorem root_valid : rootConfig.Valid := by decide

theorem authorized_entry_ready : rootConfig.Ready 259 := by decide

theorem root_matches_runtime (generation issued expires decisions : Nat) :
    RefusalRecovery.config RefusalRecovery.Runtime.hardware
      ⟨generation, issued, expires, 150, decisions⟩ = rootConfig := rfl

def reserveError (time : Nat) : Int := (((7 * time + 1) % 5 : Nat) : Int) - 2
def rateError (time : Nat) : Int := (((5 * time + 2) % 3 : Nat) : Int) - 1

theorem reserve_error_bounds (time : Nat) : -2 ≤ reserveError time ∧ reserveError time ≤ 2 := by
  have bounded := Nat.mod_lt (7 * time + 1) (by decide : 0 < 5)
  unfold reserveError
  omega

theorem rate_error_bounds (time : Nat) : -1 ≤ rateError time ∧ rateError time ≤ 1 := by
  have bounded := Nat.mod_lt (5 * time + 2) (by decide : 0 < 3)
  unfold rateError
  omega

def postDelivery (pre : Int) (delivered : Bool) : Int :=
  if delivered then min 660 (pre + 220) else pre

def freshLower (pre error : Int) (delivered : Bool) : Int :=
  if delivered then min 660 (pre + error - 2 + 220) else pre + error - 2

theorem fresh_lower_bounds (pre error : Int) (delivered : Bool)
    (noise : -2 ≤ error ∧ error ≤ 2) :
    postDelivery pre delivered - 4 ≤ freshLower pre error delivered ∧
    freshLower pre error delivered ≤ postDelivery pre delivered := by
  cases delivered <;> simp only [postDelivery, freshLower, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem sampled_pre_claim_sound (pre error : Int) (noise : error ≤ 2)
    (claimed : 100 ≤ pre + error - 2) : 100 ≤ pre := by omega

theorem fresh_entry_ready {post lower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post) :
    rootConfig.Ready lower.toNat := by
  simp only [Repair.Config.Ready, Repair.Config.guard, Repair.Config.loss, rootConfig]
  omega

theorem actual_decision_shape {post lower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post) :
    ClosedLoop.choose rootConfig lower.toNat =
      if 400 ≤ lower then .wait 1 else .write := by
  have spec := ClosedLoop.choose_spec root_valid (fresh_entry_ready range fresh)
  cases chosen : ClosedLoop.choose rootConfig lower.toNat with
  | wait ticks =>
    rw [chosen] at spec
    simp only [rootConfig, Repair.Config.guard, Repair.Config.loss] at spec
    have ticksOne : ticks = 1 := by omega
    have high : 400 ≤ lower := by omega
    simp [high, ticksOne]
  | write =>
    rw [chosen] at spec
    simp only [rootConfig, Repair.Config.target, Repair.Config.guard, Repair.Config.loss] at spec
    have low : ¬ 400 ≤ lower := by omega
    simp [low]
  | refuse => rw [chosen] at spec; contradiction

def activePost (post lower : Int) : Int :=
  if 400 ≤ lower then post - 140 else min 660 (post - 140 + 220)

theorem active_post_invariant {post lower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post) :
    260 ≤ activePost post lower ∧ activePost post lower ≤ 483 := by
  unfold activePost
  split <;> omega

theorem active_write_not_saturated {post : Int}
    (range : 260 ≤ post ∧ post ≤ 483) : min 660 (post - 140 + 220) = post + 80 := by omega

theorem next_fresh_guard {post lower nextLower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post)
    (nextFresh : activePost post lower - 4 ≤ nextLower ∧ nextLower ≤ activePost post lower) :
    250 ≤ nextLower ∧ nextLower ≤ 660 := by
  have preserved := active_post_invariant range fresh
  omega

theorem next_pre_delivery_safe (post : Int) (ready : 260 ≤ post) : 100 ≤ post - 140 := by omega

theorem authorized_actions_have_one_period {post lower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post) :
    ClosedLoop.duration rootConfig (ClosedLoop.choose rootConfig lower.toNat) = 1 := by
  rw [actual_decision_shape range fresh]
  split <;> rfl

def actionEndpoint (post : Int) : ClosedLoop.Action → Int
  | .wait ticks => post - 140 * (ticks : Int)
  | .write => min 660 (post - 140 + 220)
  | .refuse => post

theorem actual_endpoint_eq {post lower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post) :
    actionEndpoint post (ClosedLoop.choose rootConfig lower.toNat) = activePost post lower := by
  rw [actual_decision_shape range fresh]
  unfold activePost
  split <;> simp [actionEndpoint]

theorem actual_endpoint_invariant {post lower : Int}
    (range : 260 ≤ post ∧ post ≤ 483) (fresh : post - 4 ≤ lower ∧ lower ≤ post) :
    260 ≤ actionEndpoint post (ClosedLoop.choose rootConfig lower.toNat) ∧
    actionEndpoint post (ClosedLoop.choose rootConfig lower.toNat) ≤ 483 := by
  rw [actual_endpoint_eq range fresh]
  exact active_post_invariant range fresh

theorem root_activation_boundary :
    (40 : Int) < 100 ∧ postDelivery 40 true = 260 ∧
    freshLower 40 (reserveError 666) true = 259 := by decide

theorem signed_recovery_endpoints :
    (List.range 5).map (fun (n : Nat) => (-60 : Int) + 80 * (n : Int)) =
      [-60, 20, 100, 180, 260] := by decide

theorem first_recovered_sample : (120 : Int) + reserveError 667 - 2 = 116 := by decide

theorem conservation_forces_registered_write_count (writes : Nat) (finalPost : Int)
    (conservation : finalPost = -91300 + 220 * (writes : Int))
    (range : 260 ≤ finalPost ∧ finalPost ≤ 483) : writes = 417 ∧ finalPost = 440 := by omega

theorem registered_cost_arithmetic :
    29 + 4 + 417 = 450 ∧ 179 + (1320 - 662 + 1) = 838 ∧
    (654 + 7) / 8 = 82 ∧ 838 + 10 * 450 = 5338 ∧ 5338 + 1 + 82 = 5421 := by decide

end RecoveryV4

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`RecoveryV4).isPrefixOf (privateToUserName name) then
      if info.isAxiom then throwError "Unexpected model axiom {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
      if info.isTheorem then theorems := theorems + 1
  if theorems < 18 then throwError "Incomplete v4 model theorem audit"
  logInfo m!"RecoveryV4 model audit: {checked} declarations, {theorems} theorems."
