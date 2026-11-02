import KernelR.HybridCadencePacketGaps

/-! Actual input gaps at the full written packet budget. These statements
retain all phase errors. They do not extend any physical receiver contract. -/
namespace KernelR.Chain

theorem Packet.finite_prefix_gap {m L J} (p : Packet m L J)
    (i : ℕ) (hi : i + 1 < m) :
    37 / 5 - 2 * J ≤ p.actual (i + 1) - p.actual i ∧
      p.actual (i + 1) - p.actual i ≤ 83 / 10 + 2 * J := by
  have hi0 : i < m := by omega
  have h := p.prefix_gap i hi
  have he := p.phase_bounds i
  have hf := p.phase_bounds (i + 1)
  simp only [Packet.actual,Packet.ideal,ite_eq_left hi,ite_eq_left hi0]
  constructor <;> linarith [h.1,h.2,he.1,he.2,hf.1,hf.2]

theorem Packet.finite_transition_gap {m L J} (p : Packet m L J) :
    4 - 2 * J ≤ p.actual m - p.actual (m - 1) ∧
      p.actual m - p.actual (m - 1) ≤ 41 / 10 + 2 * J := by
  have hm : m - 1 < m := by have h := p.prefix_pos; omega
  have he := p.phase_bounds (m - 1)
  have hf := p.phase_bounds m
  have hs := p.settle_bounds
  simp only [Packet.actual,Packet.ideal,lt_self_iff_false,ite_false,ite_eq_left hm,
    Nat.sub_self,Nat.cast_zero,mul_zero,add_zero]
  constructor <;> linarith [hs.1,hs.2,he.1,he.2,hf.1,hf.2]

theorem Packet.finite_tail_gap {m L J} (p : Packet m L J)
    (i : ℕ) (hi : m ≤ i) :
    4 - 2 * J ≤ p.actual (i + 1) - p.actual i ∧
      p.actual (i + 1) - p.actual i ≤ 4 + 2 * J := by
  have hi0 : ¬i < m := by omega
  have hi1 : ¬i + 1 < m := by omega
  have hnext : i + 1 - m = (i - m) + 1 := by omega
  have he := p.phase_bounds i
  have hf := p.phase_bounds (i + 1)
  simp only [Packet.actual,Packet.ideal,ite_eq_right hi0,ite_eq_right hi1,hnext,Nat.cast_add,Nat.cast_one]
  constructor <;> nlinarith [he.1,he.2,hf.1,hf.2]

theorem Packet.full_budget_prefix_gap {m L J} (p : Packet m L J) (hJ : J ≤ 3 / 20)
    (i : ℕ) (hi : i + 1 < m) :
    71 / 10 ≤ p.actual (i + 1) - p.actual i ∧
      p.actual (i + 1) - p.actual i ≤ 43 / 5 := by
  have h := p.finite_prefix_gap i hi
  constructor <;> linarith [h.1,h.2]

theorem Packet.full_budget_transition_gap {m L J} (p : Packet m L J) (hJ : J ≤ 3 / 20) :
    37 / 10 ≤ p.actual m - p.actual (m - 1) ∧
      p.actual m - p.actual (m - 1) ≤ 22 / 5 := by
  have h := p.finite_transition_gap
  constructor <;> linarith [h.1,h.2]

theorem Packet.full_budget_tail_gap {m L J} (p : Packet m L J) (hJ : J ≤ 3 / 20)
    (i : ℕ) (hi : m ≤ i) :
    37 / 10 ≤ p.actual (i + 1) - p.actual i ∧
      p.actual (i + 1) - p.actual i ≤ 43 / 10 := by
  have h := p.finite_tail_gap i hi
  constructor <;> linarith [h.1,h.2]

theorem Packet.full_budget_actual_gap {m L J} (p : Packet m L J) (hJ : J ≤ 3 / 20)
    (i : ℕ) : 37 / 10 ≤ p.actual (i + 1) - p.actual i := by
  by_cases hprefix : i + 1 < m
  · linarith [(p.full_budget_prefix_gap hJ i hprefix).1]
  · by_cases hi : i < m
    · have heq : i = m - 1 := by omega
      have hm : (m - 1) + 1 = m := by have h := p.prefix_pos; omega
      subst i
      simpa only [hm] using (p.full_budget_transition_gap hJ).1
    · exact (p.full_budget_tail_gap hJ i (by omega)).1

theorem Packet.full_budget_strict_mono {m L J} (p : Packet m L J) (hJ : J ≤ 3 / 20) :
    StrictMono p.actual := by
  apply strictMono_nat_of_lt_succ
  intro i
  linarith [p.full_budget_actual_gap hJ i]

end KernelR.Chain
