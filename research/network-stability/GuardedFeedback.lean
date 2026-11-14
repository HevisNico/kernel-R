import Std

namespace NetworkStability.GuardedFeedback

/-- One active pulse at a ready probe. A coincident routed FIRE raises
the charge score. A FIRE protects the memory; silence writes one dose. -/
def pulse (writes : Nat) (incoming : Bool) (error : Int) : Nat × Bool :=
  if (2 : Int) ≤ 1 + (writes : Int) + (if incoming then 1 else 0) + error then
    (writes, true)
  else
    (writes + 1, false)

/-- Three separated probes in a finite training window. Both routed
edges can carry a FIRE. The final probe is outside the forward gate. -/
def episode (errorA errorB errorReturn : Int) : Nat × Nat :=
  let a := pulse 0 false errorA
  let b := pulse 0 a.2 errorB
  let aReturn := pulse a.1 b.2 errorReturn
  (aReturn.1, b.1)

def Admissible (radius : Nat) (a b aReturn : Int) : Prop :=
  a.natAbs ≤ radius ∧ b.natAbs ≤ radius ∧ aReturn.natAbs ≤ radius

theorem routed_fire_disables_write :
    pulse 0 false 0 = (1, false) ∧ pulse 0 true 0 = (0, true) := by decide

theorem both_edges_used :
    (pulse 0 false 1).2 = true ∧
    (pulse 0 (pulse 0 false 1).2 0).2 = true := by decide

theorem nominal_terminal : episode 0 0 0 = (1, 1) := by decide

theorem perturbed_terminal : episode 1 0 0 = (0, 0) := by decide

def HasRoom (writes : Nat) (incoming : Bool) (lo hi : Int) : Prop :=
  let score := (1 : Int) + (writes : Int) + (if incoming then 1 else 0)
  (score < 2 ∧ score + hi < 2) ∨ (2 ≤ score ∧ 2 ≤ score + lo)

/-- A clean local score with enough one-sided room is unchanged by every
error in the envelope. -/
theorem pulse_eq_of_margin (writes : Nat) (incoming : Bool) (error lo hi : Int)
    (within : lo ≤ error ∧ error ≤ hi) (room : HasRoom writes incoming lo hi) :
    pulse writes incoming error = pulse writes incoming 0 := by
  dsimp [HasRoom] at room
  unfold pulse
  rcases room with ⟨clean, upper⟩ | ⟨clean, lower⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]

/-- Checking margins on the nominal slots suffices. Equality of earlier
FIRE decisions makes each routed contribution identical at the next slot. -/
theorem episode_eq_of_margins (lo hi : Fin 3 → Int) (errorA errorB errorReturn : Int)
    (eA : lo 0 ≤ errorA ∧ errorA ≤ hi 0)
    (eB : lo 1 ≤ errorB ∧ errorB ≤ hi 1)
    (eReturn : lo 2 ≤ errorReturn ∧ errorReturn ≤ hi 2)
    (mA : HasRoom 0 false (lo 0) (hi 0))
    (mB : HasRoom 0 (pulse 0 false 0).2 (lo 1) (hi 1))
    (mReturn : HasRoom (pulse 0 false 0).1 (pulse 0 (pulse 0 false 0).2 0).2 (lo 2) (hi 2)) :
    episode errorA errorB errorReturn = episode 0 0 0 := by
  unfold episode
  simp only [pulse_eq_of_margin _ _ _ _ _ eA mA,
    pulse_eq_of_margin _ _ _ _ _ eB mB, pulse_eq_of_margin _ _ _ _ _ eReturn mReturn]

theorem directional_envelope (a b ret : Int)
    (ha : -1 ≤ a ∧ a ≤ 0) (hb : -1 ≤ b ∧ b ≤ 0) (hr : 0 ≤ ret ∧ ret ≤ 1) :
    episode a b ret = (1, 1) := by
  rw [← nominal_terminal]
  exact episode_eq_of_margins (fun i => if i = 2 then 0 else -1)
    (fun i => if i = 2 then 1 else 0) a b ret ha hb hr
    (by unfold HasRoom; decide) (by unfold HasRoom; decide) (by unfold HasRoom; decide)

/-- The order and routing policy are fixed. A bounded change of read
error alone changes the terminal write vector. -/
theorem different_terminal_needs :
    Admissible 1 0 0 0 ∧ Admissible 1 1 0 0 ∧ episode 0 0 0 ≠ episode 1 0 0 := by
  exact ⟨by unfold Admissible; decide, by unfold Admissible; decide, by rw [nominal_terminal, perturbed_terminal]; decide⟩

end NetworkStability.GuardedFeedback
