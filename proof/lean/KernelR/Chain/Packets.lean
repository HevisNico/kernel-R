import Mathlib.Tactic

/-! Existential ideal-date packet witnesses. These definitions do not retime
physical pulses. Relating a hybrid cell's output to the relay transform is a
separate local dynamical contract. -/
namespace KernelR.Chain

structure Packet (m L : ℕ) (J : ℝ) where
  slowDate : ℕ → ℝ
  settle : ℝ
  phase : ℕ → ℝ
  prefix_pos : 1 ≤ m
  tail_pos : 1 ≤ L
  jitter_nonneg : 0 ≤ J
  prefix_gap : ∀ i, i + 1 < m →
    (37 / 5 : ℝ) ≤ slowDate (i + 1) - slowDate i ∧
    slowDate (i + 1) - slowDate i ≤ 83 / 10
  settle_bounds : 4 ≤ settle ∧ settle ≤ 41 / 10
  phase_bounds : ∀ i, -J ≤ phase i ∧ phase i ≤ J

noncomputable def Packet.ideal {m L J} (p : Packet m L J) (i : ℕ) : ℝ :=
  if i < m then p.slowDate i else p.slowDate (m - 1) + p.settle + 4 * (i - m : ℕ)

noncomputable def Packet.actual {m L J} (p : Packet m L J) (i : ℕ) : ℝ :=
  p.ideal i + p.phase i

theorem actual_gap {u v e f J : ℝ}
    (hgap : 4 ≤ v - u) (he : -J ≤ e ∧ e ≤ J)
    (hf : -J ≤ f ∧ f ≤ J) (hJ : J ≤ 3 / 20) :
    (37 / 10 : ℝ) ≤ (v + f) - (u + e) := by
  linarith [he.2, hf.1]

theorem slow_actual_gap {u v e f J : ℝ}
    (hgap : (37 / 5 : ℝ) ≤ v - u) (he : -J ≤ e ∧ e ≤ J)
    (hf : -J ≤ f ∧ f ≤ J) (hJ : J ≤ 3 / 20) :
    (71 / 10 : ℝ) ≤ (v + f) - (u + e) := by
  linarith [he.2, hf.1]

theorem width_one_disjoint {s t : ℝ} (h : (37 / 10 : ℝ) ≤ t - s) :
    s + 1 < t := by linarith

/-- A fixed wire centre shifts ideal dates; only its errors increase the budget. -/
noncomputable def Packet.wire {m L J} (p : Packet m L J)
    (d σ : ℝ) (hσ : 0 ≤ σ) (e : ℕ → ℝ)
    (he : ∀ i, -σ ≤ e i ∧ e i ≤ σ) : Packet m L (J + σ) where
  slowDate i := p.slowDate i + d
  settle := p.settle
  phase i := p.phase i + e i
  prefix_pos := p.prefix_pos
  tail_pos := p.tail_pos
  jitter_nonneg := add_nonneg p.jitter_nonneg hσ
  prefix_gap i hi := by
    simpa only [add_sub_add_right_eq_sub] using p.prefix_gap i hi
  settle_bounds := p.settle_bounds
  phase_bounds i := by
    constructor <;> linarith [(p.phase_bounds i).1, (p.phase_bounds i).2, (he i).1, (he i).2]

theorem wire_actual {m L J} (p : Packet m L J) (d σ : ℝ) (hσ : 0 ≤ σ)
    (e : ℕ → ℝ) (he : ∀ i, -σ ≤ e i ∧ e i ≤ σ) (i : ℕ) :
    (p.wire d σ hσ e he).actual i = p.actual i + d + e i := by
  simp only [Packet.actual, Packet.ideal, Packet.wire]
  split_ifs <;> ring

theorem wire_delay_bounds {d σ e : ℝ}
    (hd : 3 / 10 + σ ≤ d ∧ d ≤ 2 / 5 - σ)
    (he : -σ ≤ e ∧ e ≤ σ) :
    (3 / 10 : ℝ) ≤ d + e ∧ d + e ≤ 2 / 5 := by
  constructor <;> linarith [hd.1, hd.2, he.1, he.2]

/-- Input indices retained by a relay: exactly tail inputs t1 and t3 are omitted. -/
def relayIndex (m i : ℕ) : ℕ :=
  if i < m then i else if i = m then m + 1 else i + 2

/-- The local output-date contract closes at exactly the same phase budget J.
The latency of the first high-gain firing may depend on the realized errors. -/
noncomputable def Packet.relay {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ)
    (h₀ : 65 / 100 ≤ l₀ ∧ l₀ ≤ 66 / 100)
    (h₁ : 20 / 100 ≤ l₁ ∧ l₁ ≤ 25 / 100)
    (h₂ : 24 / 100 ≤ l₂ ∧ l₂ ≤ 25 / 100)
    (horder : l₁ ≤ l₂) : Packet (m + 2) (L - 4) J where
  slowDate i := if i < m then p.slowDate i + l₀
    else if i = m then p.slowDate (m - 1) + p.settle + 4 + l₀
    else p.slowDate (m - 1) + p.settle + 12 + l₁
  settle := 4 + l₂ - l₁
  phase i := p.phase (relayIndex m i)
  prefix_pos := by omega
  tail_pos := by omega
  jitter_nonneg := p.jitter_nonneg
  prefix_gap i hi := by
    by_cases hn : i + 1 < m
    · have h : i < m := by omega
      simp only [hn, h, if_true]
      simpa only [add_sub_add_right_eq_sub] using p.prefix_gap i hn
    · by_cases h : i < m
      · have hn' : i + 1 = m := by omega
        have hi' : i = m - 1 := by omega
        simp only [hn, h, hn', Nat.lt_irrefl, if_false, if_true]
        rw [hi']
        constructor <;> linarith [p.settle_bounds.1, p.settle_bounds.2]
      · have hi' : i = m := by omega
        subst i
        have hn' : ¬ m + 1 < m := by omega
        have he' : m + 1 ≠ m := by omega
        simp only [Nat.lt_irrefl, hn', he', if_false, if_true]
        constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]
  settle_bounds := by constructor <;> linarith [h₁.1, h₂.2]
  phase_bounds i := p.phase_bounds (relayIndex m i)

theorem relay_output_count {m L : ℕ} (hL : 5 ≤ L) :
    (m + 2) + (L - 4) = m + L - 2 := by omega

theorem relay_retains_prefix_phase {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ) (h₀) (h₁) (h₂) (ho) {i : ℕ} (hi : i < m) :
    (p.relay hL l₀ l₁ l₂ h₀ h₁ h₂ ho).phase i = p.phase i := by
  simp [Packet.relay, relayIndex, hi]

theorem relay_retains_tail_phase {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ) (h₀) (h₁) (h₂) (ho) {i : ℕ} (hi : m + 2 ≤ i) :
    (p.relay hL l₀ l₁ l₂ h₀ h₁ h₂ ho).phase i = p.phase (i + 2) := by
  have h : ¬ i < m := by omega
  have hn : i ≠ m := by omega
  simp [Packet.relay, relayIndex, h, hn]

/-- Leaf output witness for K exact source pulses after the supplied local firing cases. -/
noncomputable def leafPacket (K : ℕ) (hK : 9 ≤ K) (start a l₀ l₁ l₂ : ℝ)
    (ha : 4 / 10 ≤ a ∧ a ≤ 66 / 100)
    (h₀ : 65 / 100 ≤ l₀ ∧ l₀ ≤ 66 / 100)
    (h₁ : 20 / 100 ≤ l₁ ∧ l₁ ≤ 25 / 100)
    (h₂ : 24 / 100 ≤ l₂ ∧ l₂ ≤ 25 / 100)
    (ho : l₁ ≤ l₂) : Packet 3 (K - 8) 0 where
  slowDate i := if i = 0 then start + 12 + a
    else if i = 1 then start + 20 + l₀ else start + 28 + l₁
  settle := 4 + l₂ - l₁
  phase _ := 0
  prefix_pos := by norm_num
  tail_pos := by omega
  jitter_nonneg := by norm_num
  prefix_gap i hi := by
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl <;> norm_num <;>
      constructor <;> linarith [ha.1, ha.2, h₀.1, h₀.2, h₁.1, h₁.2]
  settle_bounds := by constructor <;> linarith [h₁.1, h₂.2]
  phase_bounds _ := by norm_num

/-- Exact event correspondence for the slowDate retained by the relay. -/
theorem relay_actual_prefix {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ) (h₀) (h₁) (h₂) (ho) {i : ℕ} (hi : i < m) :
    (p.relay hL l₀ l₁ l₂ h₀ h₁ h₂ ho).actual i = p.actual i + l₀ := by
  have hi' : i < m + 2 := by omega
  simp [Packet.actual, Packet.ideal, Packet.relay, relayIndex, hi, hi']
  ring

theorem relay_actual_second_fire {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ) (h₀) (h₁) (h₂) (ho) :
    (p.relay hL l₀ l₁ l₂ h₀ h₁ h₂ ho).actual m = p.actual (m + 1) + l₀ := by
  have h : m < m + 2 := by omega
  have h' : ¬ m + 1 < m := by omega
  simp [Packet.actual, Packet.ideal, Packet.relay, relayIndex, h, h']
  ring

theorem relay_actual_first_high {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ) (h₀) (h₁) (h₂) (ho) :
    (p.relay hL l₀ l₁ l₂ h₀ h₁ h₂ ho).actual (m + 1) = p.actual (m + 3) + l₁ := by
  have h : m + 1 < m + 2 := by omega
  have h' : ¬ m + 1 < m := by omega
  have h'' : ¬ m + 3 < m := by omega
  have hn : m + 1 ≠ m := by omega
  simp [Packet.actual, Packet.ideal, Packet.relay, relayIndex, h, h', h'', hn, Nat.add_assoc]
  ring

theorem relay_actual_regular_tail {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (l₀ l₁ l₂ : ℝ) (h₀) (h₁) (h₂) (ho) {i : ℕ} (hi : m + 2 ≤ i) :
    (p.relay hL l₀ l₁ l₂ h₀ h₁ h₂ ho).actual i = p.actual (i + 2) + l₂ := by
  have h₁' : ¬ i < m + 2 := by omega
  have h₂' : ¬ i < m := by omega
  have h₃' : i ≠ m := by omega
  have h₄' : ¬ i + 2 < m := by omega
  have h₅' : ¬ m + 1 < m := by omega
  have h₆' : m + 1 ≠ m := by omega
  have hs : m + 2 - 1 = m + 1 := by omega
  have hd : i + 2 - m = (i - (m + 2)) + 4 := by omega
  simp [Packet.actual, Packet.ideal, Packet.relay, relayIndex,
    h₁', h₂', h₃', h₄', h₅', h₆', hs, hd, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem Packet.ideal_gap {m L J} (p : Packet m L J) (i : ℕ) :
    4 ≤ p.ideal (i + 1) - p.ideal i := by
  by_cases hn : i + 1 < m
  · have hi : i < m := by omega
    simp only [Packet.ideal, hn, hi, if_true]
    linarith [(p.prefix_gap i hn).1]
  · by_cases hi : i < m
    · have he : i + 1 = m := by omega
      have he' : i = m - 1 := by omega
      simp only [Packet.ideal, hn, hi, if_false, if_true]
      rw [he, he']
      simp only [Nat.sub_self, Nat.cast_zero, mul_zero, add_zero]
      linarith [p.settle_bounds.1]
    · have hs : i + 1 - m = (i - m) + 1 := by omega
      simp only [Packet.ideal, hn, hi, if_false, hs, Nat.cast_add, Nat.cast_one]
      linarith

theorem Packet.actual_gap {m L J} (p : Packet m L J) (hJ : J ≤ 3 / 20) (i : ℕ) :
    (37 / 10 : ℝ) ≤ p.actual (i + 1) - p.actual i := by
  exact KernelR.Chain.actual_gap (p.ideal_gap i) (p.phase_bounds i) (p.phase_bounds (i + 1)) hJ

end KernelR.Chain
