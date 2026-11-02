import KernelR.HybridCadencePacketGaps

/-! Packet closure with the directly proved residual high timing margins.
The existing narrower RelayWitness interface is retained independently. -/
namespace KernelR.Chain

noncomputable def Packet.relayCadence {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (low firstHigh restHigh : ℝ)
    (hlow : 65 / 100 ≤ low ∧ low ≤ 66 / 100)
    (hfirst : 4 / 25 ≤ firstHigh ∧ firstHigh ≤ 13 / 50)
    (hrest : 4 / 25 ≤ restHigh ∧ restHigh ≤ 13 / 50)
    (horder : firstHigh ≤ restHigh) : Packet (m + 2) (L - 4) J where
  slowDate i := if i < m then p.slowDate i + low
    else if i = m then p.slowDate (m - 1) + p.settle + 4 + low
    else p.slowDate (m - 1) + p.settle + 12 + firstHigh
  settle := 4 + restHigh - firstHigh
  phase i := p.phase (relayIndex m i)
  prefix_pos := by omega
  tail_pos := by omega
  jitter_nonneg := p.jitter_nonneg
  prefix_gap i hi := by
    by_cases hn : i + 1 < m
    · have h : i < m := by omega
      simp only [hn,h,ite_true]
      simpa only [add_sub_add_right_eq_sub] using p.prefix_gap i hn
    · by_cases h : i < m
      · have hn' : i + 1 = m := by omega
        have hi' : i = m - 1 := by omega
        simp only [h,hn',Nat.lt_irrefl,ite_false,ite_true]
        rw [hi']
        constructor <;> linarith [p.settle_bounds.1,p.settle_bounds.2]
      · have hi' : i = m := by omega
        subst i
        have hn' : ¬m + 1 < m := by omega
        have he' : m + 1 ≠ m := by omega
        simp only [Nat.lt_irrefl,hn',he',ite_false,ite_true]
        constructor <;> linarith [hlow.1,hlow.2,hfirst.1,hfirst.2]
  settle_bounds := by constructor <;> linarith [hfirst.1,hrest.2]
  phase_bounds i := p.phase_bounds (relayIndex m i)

theorem relay_cadence_actual_prefix {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (low firstHigh restHigh : ℝ) (hlow) (hfirst) (hrest) (horder)
    {i : ℕ} (hi : i < m) :
    (p.relayCadence hL low firstHigh restHigh hlow hfirst hrest horder).actual i =
      p.actual i + low := by
  have hi' : i < m + 2 := by omega
  simp [Packet.actual,Packet.ideal,Packet.relayCadence,relayIndex,hi,hi']
  ring

theorem relay_cadence_actual_second {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (low firstHigh restHigh : ℝ) (hlow) (hfirst) (hrest) (horder) :
    (p.relayCadence hL low firstHigh restHigh hlow hfirst hrest horder).actual m =
      p.actual (m + 1) + low := by
  have hi : m < m + 2 := by omega
  have hn : ¬m + 1 < m := by omega
  simp [Packet.actual,Packet.ideal,Packet.relayCadence,relayIndex,hi,hn]
  ring

theorem relay_cadence_actual_first_high {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (low firstHigh restHigh : ℝ) (hlow) (hfirst) (hrest) (horder) :
    (p.relayCadence hL low firstHigh restHigh hlow hfirst hrest horder).actual (m + 1) =
      p.actual (m + 3) + firstHigh := by
  have hi : m + 1 < m + 2 := by omega
  have hn : ¬m + 1 < m := by omega
  have hn' : ¬m + 3 < m := by omega
  simp [Packet.actual,Packet.ideal,Packet.relayCadence,relayIndex,hi,hn,hn',Nat.add_assoc]
  ring

theorem relay_cadence_actual_tail {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (low firstHigh restHigh : ℝ) (hlow) (hfirst) (hrest) (horder)
    {i : ℕ} (hi : m + 2 ≤ i) :
    (p.relayCadence hL low firstHigh restHigh hlow hfirst hrest horder).actual i =
      p.actual (i + 2) + restHigh := by
  have h₁ : ¬i < m + 2 := by omega
  have h₂ : ¬i < m := by omega
  have h₃ : i ≠ m := by omega
  have h₄ : ¬i + 2 < m := by omega
  have h₅ : ¬m + 1 < m := by omega
  have hs : m + 2 - 1 = m + 1 := by omega
  have hd : i + 2 - m = (i - (m + 2)) + 4 := by omega
  simp [Packet.actual,Packet.ideal,Packet.relayCadence,relayIndex,
    h₁,h₂,h₃,h₄,h₅,hs,hd,Nat.cast_add,Nat.cast_ofNat]
  ring

/-- Every output has a retained actual input occurrence and one of the
constructed physical response delays. Padding dates are excluded. -/
theorem relay_cadence_input_origin {m L J} (p : Packet m L J) (hL : 5 ≤ L)
    (low firstHigh restHigh : ℝ) (hlow) (hfirst) (hrest) (horder)
    (i : Fin ((m + 2) + (L - 4))) :
    ∃ k : Fin (m + L), ∃ latency : ℝ,
      4 / 25 ≤ latency ∧ latency ≤ 33 / 50 ∧
      (p.relayCadence hL low firstHigh restHigh hlow hfirst hrest horder).actual i.val =
        p.actual k.val + latency := by
  by_cases hp : i.val < m
  · refine ⟨⟨i.val,by have hi := i.isLt; omega⟩,low,?_,?_,?_⟩
    · linarith [hlow.1]
    · linarith [hlow.2]
    · exact relay_cadence_actual_prefix p hL low firstHigh restHigh hlow hfirst hrest horder hp
  by_cases hs : i.val = m
  · refine ⟨⟨m + 1,by omega⟩,low,?_,?_,?_⟩
    · linarith [hlow.1]
    · linarith [hlow.2]
    · simpa only [hs] using relay_cadence_actual_second p hL low firstHigh restHigh hlow hfirst hrest horder
  by_cases hh : i.val = m + 1
  · refine ⟨⟨m + 3,by omega⟩,firstHigh,hfirst.1,?_,?_⟩
    · linarith [hfirst.2]
    · simpa only [hh] using relay_cadence_actual_first_high p hL low firstHigh restHigh hlow hfirst hrest horder
  refine ⟨⟨i.val + 2,by have hi := i.isLt; omega⟩,restHigh,hrest.1,?_,?_⟩
  · linarith [hrest.2]
  · exact relay_cadence_actual_tail p hL low firstHigh restHigh hlow hfirst hrest horder (by omega)

end KernelR.Chain
