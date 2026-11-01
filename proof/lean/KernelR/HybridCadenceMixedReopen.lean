import KernelR.HybridCadenceMixedPrefix

/-! The mixed input's real SLOW logarithmic return happens during SILENT,
with the original RAW still active. No READY charge or energy is substituted. -/
namespace KernelR.Hybrid
open Set

structure CadenceMixedReopen {θ route s p} (m : CadenceMixedPrefix θ route s p) where
  final : Snapshot 1
  execution : Execution θ route m.final final
  date : final.time = m.final.time + slowReopenDuration m.final 0
  window : s.time + 1 / 2 < final.time ∧ final.time < s.time + 99 / 100
  main_ready : final.main 0 = .ready
  charge : final.x 0 .q = 1 / 10
  aux_silent : final.aux 0 p = .silent
  sensor_clock : final.x 0 (.m p) = (4 / 5 : ℝ) *
    Real.exp (-(θ 0).ls p * (final.time - m.final.time))
  sensor_above : 1 / 10 < final.x 0 (.m p)
  auxiliary_other : ∀ q, q ≠ p → final.aux 0 q = .ready ∧ RestBand (final.x 0 (.m q))
  raw_active : final.raw 0 p = some s.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = m.final.pending
  gains : ∀ q, final.x 0 (.z q) = m.final.x 0 (.z q)
  recovery : final.x 0 .b = m.final.x 0 .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

theorem cadence_mixed_reopen_exists {θ ε route s p}
    (m : CadenceMixedPrefix θ route s p) (hb : PhysicalBox θ ε)
    (hq : 61 / 500 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 7 / 50)
    (hB : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (CadenceMixedReopen m) := by
  let B := s.x 0 .b + 1 / 10
  let T := m.final.time + slowReopenDuration m.final 0
  have hbM : m.final.x 0 .b = B := m.recovery_gain
  have hbpos : 0 < B := by dsimp [B]; linarith [hB.1]
  have hqM : 1 / 10 < m.final.x 0 .q := by linarith [m.charge.1]
  have hqpos : 0 < s.x 0 .q := by linarith [hq.1]
  have hT : m.final.time < T := by
    dsimp [T,slowReopenDuration]
    exact lt_add_of_pos_right _ (div_pos
      (Real.log_pos ((lt_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 10)).mpr (by linarith)))
      (by rw [hbM]; exact hbpos))
  have hBudget := m.execution.recovery_upper_of_end hb 0 B (by rw [m.recovery_gain])
  have hI := m.execution.accumulatedRecovery_of_upper 0 B hBudget.2
  have hsol := m.execution.slow_solution 0 m.main_flows
  have hlog : Real.log (m.final.x 0 .q / (1 / 10)) =
      Real.log (s.x 0 .q / (1 / 10)) - m.execution.accumulatedRecovery 0 := by
    rw [hsol,Real.log_div (mul_ne_zero (ne_of_gt hqpos) (Real.exp_ne_zero _)) (by norm_num),
      Real.log_mul (ne_of_gt hqpos) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_div (ne_of_gt hqpos) (by norm_num)]
    ring
  have hTclock : T * B = m.final.time * B + Real.log (s.x 0 .q / (1 / 10)) - m.execution.accumulatedRecovery 0 := by
    dsimp [T,slowReopenDuration]
    rw [hbM,hlog]
    field_simp [ne_of_gt hbpos]
    ring
  have hlogLo : (22 / 111 : ℝ) ≤ Real.log (s.x 0 .q / (1 / 10)) := by
    have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 50)
    norm_num at h
    apply h.trans (Real.log_le_log (by norm_num) ?_)
    linarith [hq.1]
  have hLo : s.time + 1 / 2 < T := by
    by_contra hn
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hbpos.le
    dsimp [B] at hTclock hI hmul
    nlinarith [hB.1,hB.2]
  have hlogHi : Real.log (m.final.x 0 .q / (1 / 10)) < 7 / 20 := by
    have hbound : Real.log (7 / 5 : ℝ) < 7 / 20 := by
      apply (Real.log_lt_iff_lt_exp (by norm_num)).2
      have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 20)
      norm_num at h ⊢
      linarith
    apply lt_of_le_of_lt (Real.log_le_log (by positivity) ?_) hbound
    linarith [m.charge.2]
  have hquot : Real.log (m.final.x 0 .q / (1 / 10)) / B < 94 / 100 := by
    apply (div_lt_iff₀ hbpos).mpr
    dsimp [B]
    nlinarith [hB.1]
  have hHi : T < s.time + 99 / 100 := by
    dsimp [T,slowReopenDuration]
    rw [hbM]
    linarith [m.deadline]
  have hsensor : ∀ time ∈ Icc m.final.time T,
      1 / 10 < (4 / 5 : ℝ) * Real.exp (-(θ 0).ls p * (time - m.final.time)) := by
    intro time ht
    apply (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 10)
      (by norm_num : (1 / 10 : ℝ) < 4 / 5) (hb.rates_positive 0 p).2.1).2.2
    · linarith [ht.1]
    · norm_num
      linarith [m.error_lower,ht.2]
  let flow : Flow θ m.final (protectedMainEnd θ m.final 0 p .slow .silent (some s.time) T) :=
    protectedMainFlow m.final 0 p .slow .silent (some s.time) hT (Or.inr rfl) (Or.inr (Or.inl rfl))
      m.main_slow (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) m.aux_silent
      (by intro j q h; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact (m.auxiliary_other q (by simpa using h)).1)
      m.raw_active (by intro j q h; have hj : j = 0 := Subsingleton.elim _ _; subst j; exact m.raw_other q (by simpa using h))
      (by intro origin he; cases Option.some.inj he; exact ⟨by linarith [m.early],by linarith⟩)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j q h; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(m.auxiliary_other q (by simpa using h)).2.2])
      (by intro time ht; simpa [protectedMainRate,T] using slowReopen_preguard m.final 0 hqM (by rw [hbM]; exact hbpos) ht.2)
      (by intro time ht; simpa [protectedReadyRate,m.sensor_charge] using hsensor time ⟨ht.1,ht.2.le⟩)
      (by intro d hd; rw [m.pending] at hd; linarith [hp d hd])
  let before := protectedMainEnd θ m.final 0 p .slow .silent (some s.time) T
  have hthreshold : before.x 0 .q = 1 / 10 := by
    simpa [before,protectedMainEnd,protectedMainValues,protectedMainRate,T] using
      slowReopen_root m.final 0 hqM (by rw [hbM]; exact hbpos)
  let final := setMain before 0 .ready
  let execution : Execution θ route m.final final :=
    .cons (.flow flow) (.cons (.jump (.reopen before 0 m.main_slow hthreshold)) (.nil _))
  refine ⟨{
    final := final, execution := execution, date := rfl, window := ⟨hLo,hHi⟩
    main_ready := by simp [final,setMain], charge := hthreshold, aux_silent := m.aux_silent
    sensor_clock := ?_, sensor_above := ?_, auxiliary_other := ?_
    raw_active := m.raw_active, raw_other := m.raw_other, pending := rfl
    gains := fun _ => rfl, recovery := rfl, emissions := rfl, deliveries := rfl
    physical := execution.physical_invariant hb m.physical, raw_valid := execution.raw_valid m.raw_valid
  }⟩
  · simp [final,setMain,before,protectedMainEnd,protectedMainValues,protectedReadyRate,m.sensor_charge]
  · simpa [final,setMain,before,protectedMainEnd,protectedMainValues,protectedReadyRate,m.sensor_charge] using hsensor T ⟨hT.le,le_rfl⟩
  · intro q hq
    exact (execution.aux_no_input_rest_band 0 q (m.auxiliary_other q hq).1 (m.auxiliary_other q hq).2
      (m.raw_other q hq) (by simp [NoArrivalAt,execution,Execution.deliveries,Move.deliveries,Jump.deliveries])).1

end KernelR.Hybrid
