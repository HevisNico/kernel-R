import RoutedCalendar
import GuardedFeedback

namespace NetworkStability.RoutedCalendar

/-- The original three probes, with threshold 2 absorbed into the offset. -/
def earlierEpisode : List (Slot 2) :=
  [⟨0, -1, []⟩, ⟨1, -1, [⟨0, 1⟩]⟩, ⟨0, -1, [⟨1, 1⟩]⟩]

def threeErrors (a b ret : Int) (k : Nat) : Int :=
  if k = 0 then a else if k = 1 then b else ret

theorem recovers_three_probe_model (a b ret : Int) :
    let s := run 1 (threeErrors a b ret) (start 2) earlierEpisode
    (s.writes 0, s.writes 1) = GuardedFeedback.episode a b ret := by
  have aTest : (2 ≤ 1 + a) = (0 ≤ -1 + a) := propext (by omega)
  have bFire : (2 ≤ 2 + b) = (0 ≤ b) := propext (by omega)
  have bSilent : (2 ≤ 1 + b) = (0 ≤ -1 + b) := propext (by omega)
  simp only [earlierEpisode, run, start, cleanScore, decision, advance, load,
    threeErrors, GuardedFeedback.episode, GuardedFeedback.pulse]
  by_cases ha : 0 ≤ -1 + a <;> by_cases hb : 0 ≤ b <;> by_cases hb' : 0 ≤ -1 + b <;>
    simp [aTest, bFire, bSilent, ha, hb, hb'] <;>
    repeat' (first | split | omega | rfl)

/-- A sends its input bit to B. B reports conjunction with its local bit.
A receives the result back and changes its third-slot write decision. -/
def handshake (a b : Bool) : List (Slot 2) :=
  [⟨0, if a then 3 else -3, []⟩,
   ⟨1, if b then -3 else -9, [⟨0, 6⟩]⟩,
   ⟨0, -5, [⟨1, 6⟩]⟩]

def planned (a b : Bool) (k : Nat) : Bool :=
  if k = 0 then a else a && b

def window (a b : Bool) (k : Nat) : Nat × Nat :=
  let incoming := if k = 1 then a else k = 2 && (a && b)
  if incoming then (6, 6) else (0, 0)

theorem handshake_causal (a b : Bool) : CausalFrom 0 (handshake a b) := by
  simp [handshake, CausalFrom]

theorem handshake_certificate (a b : Bool) :
    Structural 2 1 6 (planned a b) (window a b) (start 2) (handshake a b) ∧
    ∀ i, offers i (handshake a b) ≤ 2 := by
  cases a <;> cases b <;> unfold handshake planned window <;>
    simp [Structural, offers, start, advance, load] <;> decide

theorem nominal_handshake (a b : Bool) :
    let s := run 2 (fun _ => 0) (start 2) (handshake a b)
    s.fires = [a, a && b, a && b] ∧
    s.writes 0 = (if a then 0 else 1) + (if a && b then 0 else 1) ∧
    s.writes 1 = (if a && b then 0 else 1) := by
  cases a <;> cases b <;> decide

/-- All four input pairs are certified with the same positive noise and
headroom constants. The report at B and the return acknowledgement at A
are observable, and the return also changes A's stored write count. -/
theorem handshake_correct (a b : Bool) (error : Nat → Int)
    (within : ∀ k, -1 ≤ error k ∧ error k ≤ 1) :
    let s := run 2 error (start 2) (handshake a b)
    s.fires = [a, a && b, a && b] ∧
    s.writes 0 = (if a then 0 else 1) + (if a && b then 0 else 1) ∧
    s.writes 1 = (if a && b then 0 else 1) ∧
    total s ≤ 4 ∧ ∀ i, memory 2 (fun _ => 1) s i < 6 := by
  obtain ⟨cert, budget⟩ := handshake_certificate a b
  have result := structural_episode 2 2 1 6 1 6 (handshake a b) (fun _ => 1) error
    (planned a b) (window a b) (fun _ => by decide) (by decide) budget within cert
    (handshake a b) [] (by simp)
  have nominal := nominal_handshake a b
  dsimp only at result nominal ⊢
  obtain ⟨same, bound, memoryBound⟩ := result
  have output := same.symm ▸ nominal
  exact ⟨output.1, output.2.1, output.2.2, bound, fun i => (memoryBound i).2.2.2⟩

theorem removing_return_changes_memory :
    let intact := run 2 (fun _ => 0) (start 2) (handshake true true)
    let cut := run 2 (fun _ => 0) (start 2)
      [⟨0, 3, []⟩, ⟨1, -3, [⟨0, 6⟩]⟩, ⟨0, -5, []⟩]
    intact.fires = [true, true, true] ∧ cut.fires = [true, true, false] ∧
      intact.writes 0 = 0 ∧ cut.writes 0 = 1 := by decide

end NetworkStability.RoutedCalendar
