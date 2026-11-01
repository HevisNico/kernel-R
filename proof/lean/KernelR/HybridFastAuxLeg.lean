import KernelR.HybridProtectedMainFlowExistence
import KernelR.HybridFirstFireSchedule

namespace KernelR.Hybrid
open Set

noncomputable def fastAuxFloor (mode : AuxMode) : ℝ := if mode = .silent then 1 / 10 else 1 / 40

structure FastAuxLeg (θ : Fin 1 → Parameters) (s : Snapshot 1) (mode : AuxMode)
    (origin : Option ℝ) (T fireTime phaseStart initial : ℝ) where
  flow : Flow θ s (protectedMainEnd θ s 0 0 .fast mode origin T)
  main_solution : (protectedMainEnd θ s 0 0 .fast mode origin T).x 0 .q =
    Real.exp (-a * (T - fireTime))
  sensor_solution : (protectedMainEnd θ s 0 0 .fast mode origin T).x 0 (.m 0) =
    initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (T - phaseStart))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ 0 →
    (protectedMainEnd θ s 0 0 .fast mode origin T).x j (.m q) < 1

/-- Cut a real FAST segment at the next auxiliary guard or raw expiry,
retaining the global decay clocks through either kind of cut. -/
theorem fast_aux_leg_exists {θ ε} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (mode : AuxMode) (origin : Option ℝ) (T fireTime phaseStart initial : ℝ)
    (hmode : mode = .silent ∨ mode = .error)
    (hT : s.time < T) (hmain : s.main 0 = .fast) (haux : s.aux 0 0 = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.aux j q = .ready)
    (hr : s.raw 0 0 = origin) (ho : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.raw j q = none)
    (hsupport : ∀ o, origin = some o → o ≤ s.time ∧ T ≤ o + 1)
    (hother : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.x j (.m q) < 1)
    (hclock : s.x 0 .q = Real.exp (-a * (s.time - fireTime)))
    (hsensor : s.x 0 (.m 0) = initial *
      Real.exp (-protectedReadyRate (θ 0) 0 mode * (s.time - phaseStart)))
    (hstart : phaseStart ≤ s.time) (hfast : T ≤ fireTime + 1)
    (hi : fastAuxFloor mode < initial)
    (hphase : T ≤ phaseStart + Real.log (initial / fastAuxFloor mode) / protectedReadyRate (θ 0) 0 mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (FastAuxLeg θ s mode origin T fireTime phaseStart initial) := by
  have hn : mode ≠ .ready := by rcases hmode with rfl | rfl <;> decide
  have hrpos : 0 < protectedReadyRate (θ 0) 0 mode := by
    rcases hmode with rfl | rfl
    · exact (hb.rates_positive 0 0).2.1
    · exact (hb.rates_positive 0 0).2.2
  have hfloor : 0 < fastAuxFloor mode := by rcases hmode with rfl | rfl <;> norm_num [fastAuxFloor]
  have hdecay := protected_decay_schedule hfloor hi hrpos
  have hmain_clock (t : ℝ) : s.x 0 .q * Real.exp (-a * (t - s.time)) =
      Real.exp (-a * (t - fireTime)) := by rw [hclock,attenuation_split]
  have hsensor_clock (t : ℝ) : s.x 0 (.m 0) *
      Real.exp (-protectedReadyRate (θ 0) 0 mode * (t - s.time)) =
      initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (t - phaseStart)) := by
    rw [hsensor,mul_assoc,attenuation_split]
  have hq : ∀ t ∈ Ico s.time T, (1 / 4 : ℝ) < s.x 0 .q * Real.exp (-a * (t - s.time)) := by
    intro t ht
    rw [hmain_clock]
    have he : Real.exp (-a * ((fireTime + 1) - fireTime)) = (1 / 4 : ℝ) := by
      norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    rw [← he]
    apply Real.exp_lt_exp.mpr
    have ha := a_coarse_bounds.1
    nlinarith [ht.2]
  have hx : ∀ t ∈ Ico s.time T, fastAuxFloor mode < s.x 0 (.m 0) *
      Real.exp (-protectedReadyRate (θ 0) 0 mode * (t - s.time)) := by
    intro t ht
    rw [hsensor_clock]
    exact hdecay.2.2 (t - phaseStart) (by linarith [ht.1]) (by linarith [ht.2])
  let flow := protectedMainFlow s 0 0 .fast mode origin hT (Or.inl rfl)
    (by rcases hmode with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl))
    hmain (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) haux hao hr ho hsupport
    (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) hother
    (by simpa only [ite_true,protectedMainRate] using hq)
    (by simpa only [hn,ite_false,fastAuxFloor] using hx) hp
  refine ⟨⟨flow,?_,?_,?_⟩⟩
  · simpa [protectedMainEnd,protectedMainValues,protectedMainRate] using hmain_clock T
  · simpa [protectedMainEnd,protectedMainValues,hn] using hsensor_clock T
  · intro j q h
    have hne : ¬ (j = 0 ∧ q = 0) := by tauto
    simpa [protectedMainEnd,protectedMainValues,hne] using
      relax_lt (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (hother j q h) (by norm_num : (1 / 40 : ℝ) < 1)

end KernelR.Hybrid
