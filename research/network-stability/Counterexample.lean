import ChipFiring
import GuardedFeedback

namespace NetworkStability.Control

open ChipFiring SelfCertifyingLearning

def reciprocal (initial : Fin 2 → Nat) : Model 2 where
  spill j i := if j = i then 0 else 1
  initial := initial

def critical : Model 2 := reciprocal (fun i => if i = 0 then 1 else 0)

def subcritical : Model 2 := reciprocal (fun _ => 2)

theorem positive_fixture :
    (∀ i, (compute subcritical 2 4 (start subcritical)).work i = 1) ∧
    (∀ i, (compute subcritical 2 4 (start subcritical)).writes i = 1) := by decide

theorem critical_nonstrict :
    (∀ i, tally (critical.spill i) ≤ 1) ∧
    (∀ i, tally (fun j => critical.spill j i) ≤ 1) := by decide

theorem no_positive_margin (w : Fin 2 → Nat) (eta : Nat) (pos : 0 < eta) :
    ¬ ∀ i, eta + weighted w (fun j => critical.spill j i) (List.finRange 2) ≤ w i := by
  intro h
  have hl := h 0
  have hr := h 1
  change eta + (w 0 * 0 + (w 1 * 1 + 0)) ≤ w 0 at hl
  change eta + (w 0 * 1 + (w 1 * 0 + 0)) ≤ w 1 at hr
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at hl hr
  omega

private theorem work_eq {n s} (r : Reach critical 1 n s) : s.work 0 + s.work 1 = 1 := by
  have left := balance r 0
  have right := balance r 1
  change s.work 0 + 1 * s.writes 0 = 1 + (0 * s.writes 0 + (1 * s.writes 1 + 0)) at left
  change s.work 1 + 1 * s.writes 1 = 0 + (1 * s.writes 0 + (0 * s.writes 1 + 0)) at right
  simp only [Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at left right
  omega

theorem no_reachable_terminal {n s} (r : Reach critical 1 n s) : ¬ Terminal 1 s := by
  intro h
  have left := h 0
  have right := h 1
  have := work_eq r
  omega

theorem writes_at_every_length (n : Nat) : ∃ s, Reach critical 1 n s := by
  induction n with
  | zero => exact ⟨_, Reach.start⟩
  | succ n ih =>
    obtain ⟨s, r⟩ := ih
    have hw := work_eq r
    by_cases left : 1 ≤ s.work 0
    · exact ⟨_, r.fire 0 left⟩
    · exact ⟨_, r.fire 1 (by omega)⟩

theorem exceeds_any_ceiling (ceiling : Nat) :
    ∃ n s, Reach critical 1 n s ∧ (ceiling < s.writes 0 ∨ ceiling < s.writes 1) := by
  obtain ⟨s, r⟩ := writes_at_every_length (2 * ceiling + 1)
  have h := count_eq r
  change 1 * s.writes 0 + (1 * s.writes 1 + 0) = 2 * ceiling + 1 at h
  simp only [Nat.one_mul, Nat.add_zero] at h
  exact ⟨_, s, r, by omega⟩

def oneWay : Model 2 where
  initial := fun _ => 2
  spill j i := if i = 0 ∧ j = 1 then 1 else 0

theorem one_way_spill : (fire oneWay 2 (start oneWay) 0).work 1 = 3 := by decide

end NetworkStability.Control
