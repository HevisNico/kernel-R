import KernelR.Chain.Refinement

/-! Prepared slow-input packets. The advanced first output is removed among the
three silent inputs. A latency radius is measured about the actual learned cell's
fixed reference latency, not about a nominal gain. -/
namespace KernelR.Robust

structure Packet (L : ℕ) (T J : ℝ) where
  origin : ℝ
  advance : ℝ
  phase : ℕ → ℝ
  advance_nonneg : 0 ≤ advance
  jitter_nonneg : 0 ≤ J
  phase_bounds : ∀ i, -J ≤ phase i ∧ phase i ≤ J

noncomputable def Packet.actual {L T J} (p : Packet L T J) (i : ℕ) : ℝ :=
  p.origin + T * i - (if i = 0 then p.advance else 0) + p.phase i

theorem Packet.gap {L T J} (p : Packet L T J) (i : ℕ) :
    T - 2 * J ≤ p.actual (i + 1) - p.actual i := by
  have hn : i + 1 ≠ 0 := by omega
  simp only [Packet.actual, hn, ite_false, Nat.cast_add, Nat.cast_one, sub_zero]
  split_ifs <;> nlinarith [p.advance_nonneg, (p.phase_bounds i).2, (p.phase_bounds (i+1)).1]

theorem first_latency_decomposition (reference first : ℝ) :
    first = reference - max (reference - first) 0 + max (first - reference) 0 := by
  by_cases h : reference ≤ first
  · rw [max_eq_right (by linarith : reference - first ≤ 0), max_eq_left (by linarith : 0 ≤ first-reference)]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ reference-first), max_eq_right (by linarith : first-reference ≤ 0)]
    ring

noncomputable def Packet.cell {L T J} (p : Packet L T J)
    (reference δ : ℝ) (hδ : 0 ≤ δ) (latency : ℕ → ℝ)
    (first : latency 0 ≤ reference + δ)
    (regular : ∀ i, i ≠ 0 → -δ ≤ latency i-reference ∧ latency i-reference ≤ δ) :
    Packet (L-3) T (J+δ) where
  origin := p.origin + 3*T + reference
  advance := max (reference-latency 0) 0
  phase i := p.phase (i+3) + if i=0 then max (latency 0-reference) 0 else latency i-reference
  advance_nonneg := le_max_right _ _
  jitter_nonneg := add_nonneg p.jitter_nonneg hδ
  phase_bounds i := by
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      have h1 : 0 ≤ max (latency 0-reference) 0 := le_max_right _ _
      have h2 : max (latency 0-reference) 0 ≤ δ := max_le (by linarith) hδ
      constructor <;> linarith [(p.phase_bounds 3).1, (p.phase_bounds 3).2]
    · simp only [hi, ite_false]
      constructor <;> linarith [(p.phase_bounds (i+3)).1, (p.phase_bounds (i+3)).2,
        (regular i hi).1, (regular i hi).2]

theorem Packet.cell_actual {L T J} (p : Packet L T J)
    (reference δ : ℝ) (hδ : 0 ≤ δ) (latency : ℕ → ℝ) (first) (regular) (i : ℕ) :
    (p.cell reference δ hδ latency first regular).actual i = p.actual (i+3) + latency i := by
  have hn : i+3 ≠ 0 := by omega
  by_cases hi : i=0
  · subst i
    simp only [Packet.actual, Packet.cell, ite_true, Nat.cast_zero, mul_zero, add_zero,
      show (0+3 : ℕ) ≠ 0 by omega, ite_false, sub_zero, Nat.zero_add, Nat.cast_ofNat]
    linarith [first_latency_decomposition reference (latency 0)]
  · simp only [Packet.actual, Packet.cell, hi, hn, ite_false, sub_zero, Nat.cast_add, Nat.cast_ofNat]
    ring

noncomputable def Packet.wire {L T J} (p : Packet L T J) (center σ : ℝ)
    (hσ : 0 ≤ σ) (error : ℕ → ℝ) (he : ∀ i, -σ ≤ error i ∧ error i ≤ σ) :
    Packet L T (J+σ) where
  origin := p.origin + center
  advance := p.advance
  phase i := p.phase i + error i
  advance_nonneg := p.advance_nonneg
  jitter_nonneg := add_nonneg p.jitter_nonneg hσ
  phase_bounds i := by
    constructor <;> linarith [(p.phase_bounds i).1, (p.phase_bounds i).2, (he i).1, (he i).2]

theorem Packet.wire_actual {L T J} (p : Packet L T J) (center σ : ℝ)
    (hσ : 0 ≤ σ) (error : ℕ → ℝ) (he) (i : ℕ) :
    (p.wire center σ hσ error he).actual i = p.actual i + center + error i := by
  simp only [Packet.actual, Packet.wire]
  ring

theorem Packet.zero_jitter_periodic_tail {L T} (p : Packet L T 0) {i : ℕ} (hi : i ≠ 0) :
    p.actual (i+1) - p.actual i = T := by
  have hn : i+1 ≠ 0 := by omega
  have h0 : p.phase i = 0 := by linarith [(p.phase_bounds i).1, (p.phase_bounds i).2]
  have h1 : p.phase (i+1) = 0 := by linarith [(p.phase_bounds (i+1)).1, (p.phase_bounds (i+1)).2]
  simp [Packet.actual, hi, h0, h1, Nat.cast_add]
  ring

end KernelR.Robust
