import KernelR.HybridProtectedMainFlowExistence
import KernelR.HybridFirstCycleSchedule

namespace KernelR.Hybrid
open Set

/-- The real carried charge stays above the SLOW guard through both remaining
auxiliary phases, using the actual post-MARK recovery. -/
theorem slow_aux_charge_bounds {Q B S t : ℝ}
    (hq : 17 / 125 ≤ Q ∧ Q ≤ 4 / 25)
    (hb : 17999 / 100000 ≤ B ∧ B ≤ 18001 / 100000)
    (ht : S ≤ t) (hu : t ≤ S + 41 / 30) :
    41 / 400 < Q * Real.exp (-B * (t - S)) ∧ Q * Real.exp (-B * (t - S)) ≤ 4 / 25 := by
  have hd : 0 ≤ t - S := sub_nonneg.mpr ht
  have hp : B * (t - S) ≤ (18001 / 100000 : ℝ) * (41 / 30) := by nlinarith [hb.2]
  have he := Real.add_one_le_exp (-B * (t - S))
  have hm := mul_le_mul_of_nonneg_right hq.1 (Real.exp_pos (-B * (t - S))).le
  have heUpper : Real.exp (-B * (t - S)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hb.1])
  have hmUpper := mul_le_mul_of_nonneg_left heUpper (show 0 ≤ Q by linarith [hq.1])
  constructor <;> nlinarith [hq.2]

noncomputable def slowAuxFloor (mode : AuxMode) : ℝ := if mode = .silent then 1 / 10 else 1 / 40

structure SlowAuxLeg (θ : Fin 1 → Parameters) (s : Snapshot 1) (mode : AuxMode)
    (origin : Option ℝ) (T B Q S P initial : ℝ) where
  flow : Flow θ s (protectedMainEnd θ s 0 0 .slow mode origin T)
  main_solution : (protectedMainEnd θ s 0 0 .slow mode origin T).x 0 .q = Q * Real.exp (-B * (T - S))
  sensor_solution : (protectedMainEnd θ s 0 0 .slow mode origin T).x 0 (.m 0) =
    initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (T - P))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ 0 →
    (protectedMainEnd θ s 0 0 .slow mode origin T).x j (.m q) < 1

theorem slow_aux_leg_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (mode : AuxMode) (origin : Option ℝ) (T B Q S P initial : ℝ)
    (hmode : mode = .silent ∨ mode = .error)
    (hT : s.time < T) (hmain : s.main 0 = .slow) (haux : s.aux 0 0 = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.aux j q = .ready)
    (hr : s.raw 0 0 = origin) (ho : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.raw j q = none)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hother : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.x j (.m q) < 1)
    (hclock : s.x 0 .q = Q * Real.exp (-B * (s.time - S))) (hB : s.x 0 .b = B)
    (hsensor : s.x 0 (.m 0) = initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (s.time - P)))
    (hstart : P ≤ s.time) (hS : S ≤ s.time) (hfinish : T ≤ S + 41 / 30)
    (hQ : 17 / 125 ≤ Q ∧ Q ≤ 4 / 25) (hBrange : 17999 / 100000 ≤ B ∧ B ≤ 18001 / 100000)
    (hi : slowAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / slowAuxFloor mode) / protectedReadyRate (θ 0) 0 mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (SlowAuxLeg θ s mode origin T B Q S P initial) := by
  have hn : mode ≠ .ready := by rcases hmode with rfl | rfl <;> decide
  have hrpos : 0 < protectedReadyRate (θ 0) 0 mode := by
    rcases hmode with rfl | rfl
    · exact (hb.rates_positive 0 0).2.1
    · exact (hb.rates_positive 0 0).2.2
  have hfloor : 0 < slowAuxFloor mode := by rcases hmode with rfl | rfl <;> norm_num [slowAuxFloor]
  have hdecay := protected_decay_schedule hfloor hi hrpos
  have hmain_clock (t : ℝ) : s.x 0 .q * Real.exp (-B * (t - s.time)) = Q * Real.exp (-B * (t - S)) := by
    rw [hclock,mul_assoc,attenuation_split]
  have hsensor_clock (t : ℝ) : s.x 0 (.m 0) * Real.exp (-protectedReadyRate (θ 0) 0 mode * (t - s.time)) =
      initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (t - P)) := by
    rw [hsensor,mul_assoc,attenuation_split]
  let flow := protectedMainFlow s 0 0 .slow mode origin hT (Or.inr rfl)
    (by rcases hmode with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl))
    hmain (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) haux hao hr ho hsupport
    (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) hother
    (by intro t ht
        simp only [reduceCtorEq,ite_false,protectedMainRate,hB]
        rw [hmain_clock]
        linarith [(slow_aux_charge_bounds hQ hBrange (hS.trans ht.1) (ht.2.le.trans hfinish)).1])
    (by intro t ht
        simp only [hn,ite_false]
        rw [hsensor_clock]
        exact hdecay.2.2 (t - P) (by linarith [ht.1]) (by linarith [ht.2])) hp
  refine ⟨⟨flow,?_,?_,?_⟩⟩
  · simpa [protectedMainEnd,protectedMainValues,protectedMainRate,hB] using hmain_clock T
  · simpa [protectedMainEnd,protectedMainValues,hn] using hsensor_clock T
  · intro j q h
    have hne : ¬(j = 0 ∧ q = 0) := by tauto
    simpa [protectedMainEnd,protectedMainValues,hne] using
      relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hother j q h) (by norm_num : (1 / 40 : ℝ) < 1)

end KernelR.Hybrid
