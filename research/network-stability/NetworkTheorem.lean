import FairMemory

namespace NetworkStability.AutonomousFeedback.Schedule

def SafeMemory (Q d B rail : Nat) (base : Fin N → Nat) (s : Config N P) : Prop :=
  RoutedCalendar.total ⟨s.writes, []⟩ ≤ Q * N ∧
  ∀ i, s.writes i ≤ Q ∧ base i ≤ base i + d * s.writes i ∧
    base i + d * s.writes i ≤ B + d * Q ∧ base i + d * s.writes i < rail

def Exhausted (r : Execution M d seed) (n : Nat) : Prop := (r.state n).pending = []

/-- Headline theorem for guarded learning. The scalar certificate is needed
only for drainage. Local reserves and the strong diamond also support
perpetual traffic, with continuation fairness for equality of limits. -/
theorem network_memory (Q d B rail W eta : Nat) {N : Nat} {P : Type}
    (M : Model N P) (seed : List P) (reserve : LocalReserve Q M seed)
    (base : Fin N → Nat) (initial : ∀ i, base i ≤ B) (headroom : B + d * Q < rail)
    (independent : ∀ s, Path M d (seedConfig N seed) s → Exclusive M s ∨ PairMargins M d s)
    (lo hi : Nat → Int) :
    (∀ s, Path M d (seedConfig N seed) s → SafeMemory Q d B rail base s) ∧
    (∀ n error, (∀ k, lo k ≤ error k ∧ error k ≤ hi k) →
      NominalMargins M d lo hi n (start N seed) →
      run M d error n (start N seed) = run M d (fun _ => 0) n (start N seed)) ∧
    (∀ r : Execution M d seed, ∃ counts, Stable r counts) ∧
    (∀ a b : Execution M d seed, WriteFair a → WriteFair b →
      ∃ counts, Stable a counts ∧ Stable b counts) ∧
    (Certificate Q W eta M seed →
      (∀ error, (run M d error (W * N) (start N seed)).pending = []) ∧
      (∀ s, Path M d (seedConfig N seed) s → ∃ t, Path M d s t ∧ t.pending = []) ∧
      (∀ a b : Execution M d seed, ∀ n m, Exhausted a n → Exhausted b m →
        (a.state n).writes = (b.state m).writes ∧ stored d base (a.state n) = stored d base (b.state m))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s path
    have counts := reachable_bound Q d reserve path
    refine ⟨RoutedCalendar.total_le Q _ counts, fun i => ⟨counts i, ?_, ?_, ?_⟩⟩
    · omega
    · exact Nat.add_le_add (initial i) (Nat.mul_le_mul_left d (counts i))
    · exact Nat.lt_of_le_of_lt (Nat.add_le_add (initial i) (Nat.mul_le_mul_left d (counts i))) headroom
  · intro n error within margins
    exact run_eq_of_margins M d lo hi error within n (start N seed) margins
  · intro r
    exact execution_stabilizes Q d reserve r
  · intro a b fa fb
    obtain ⟨x, sx⟩ := execution_stabilizes Q d reserve a
    obtain ⟨y, sy⟩ := execution_stabilizes Q d reserve b
    have eq := fair_limit_unique M d seed independent a b fa fb sx sy
    exact ⟨x, sx, eq.symm ▸ sy⟩
  · intro cert
    refine ⟨?_, fun s _ => reaches_empty eta M d cert.weight cert.eta_pos cert.scalar s, ?_⟩
    · intro error
      have fuel := Nat.mul_le_mul_right (W * N) (show 1 ≤ eta from cert.eta_pos)
      rw [Nat.one_mul] at fuel
      exact terminal_by_budget M d eta cert.weight cert.eta_pos cert.scalar error
        (W * N) (start N seed) (Nat.le_trans cert.seed_weight fuel)
    · intro a b n m ha hb
      exact terminal_memory_unique Q W eta d M seed cert independent
        (reaches a n) (reaches b m) ha hb base

end NetworkStability.AutonomousFeedback.Schedule
