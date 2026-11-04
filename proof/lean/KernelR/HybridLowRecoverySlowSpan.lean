import KernelR.HybridVariableGapSlowSource

/-! Neutral low-recovery SLOW continuation. The next contact is never inserted
into the queue or delivered by this constructor. -/
namespace KernelR.Hybrid
open Set

structure LowRecoverySlowSpan {θ : Fin 1 → Parameters} {s : Snapshot 1} {p : Port}
    {f : FirstLearnedFire θ (fun _ _ => []) s 0 p} (fast : MidLearnedFastEnd f) (T : ℝ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) fast.final final
  contacts_transversal : execution.ContactsTransversal
  date : final.time = T
  main_slow : final.main 0 = .slow
  auxiliary : ∀ j q, final.aux j q = .ready
  rest : ∀ q, RestBand (final.x 0 (.m q))
  trained_rest : final.x 0 (.m p) = 1 / 40
  raw_none : ∀ j q, final.raw j q = none
  charge : 1 / 10 < final.x 0 .q ∧ final.x 0 .q ≤ 1 / 4
  charge_clock : final.x 0 .q = (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (T - (s.time + f.latency + 1)))
  pending : final.pending = fast.final.pending
  gains : ∀ j q, final.x j (.z q) = fast.final.x j (.z q)
  recovery : ∀ j, final.x j .b = fast.final.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  initial_low_b : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000
  firing_bounds : 2 / 5 < f.latency ∧ f.latency < 9 / 10
  horizon_upper : T ≤ s.time + 81 / 10

/-- The stronger endpoint band is available only for a genuinely late cut. -/
theorem LowRecoverySlowSpan.near_charge {θ s p f fast T}
    (c : @LowRecoverySlowSpan θ s p f fast T) (hnear : s.time + 79 / 10 ≤ T) :
    7 / 50 < c.final.x 0 .q ∧ c.final.x 0 .q < 4 / 25 := by
  rw [c.charge_clock]
  exact variable_gap_first_slow_charge c.initial_low_b c.firing_bounds ⟨hnear,c.horizon_upper⟩

/-- Continue a real low-recovery FAST endpoint without scheduling an arrival.
The endpoint may equal FASTend, in which case the actual execution is empty. -/
theorem FirstLearnedFire.low_recovery_slow_span_exists {θ ε} {s : Snapshot 1} {p : Port}
    (f : FirstLearnedFire θ (fun _ _ => []) s 0 p) (hb : PhysicalBox θ ε)
    (fast : MidLearnedFastEnd f) (hs : ReadyCoordinates s 0)
    (hg : Real.exp (s.x 0 (.z p)) ≤ 11 / 5)
    (hB : 7999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 8001 / 100000)
    (T : ℝ) (hstart : fast.final.time ≤ T) (hend : T ≤ s.time + 81 / 10)
    (hp : ∀ d ∈ fast.final.pending, T ≤ d.due) :
    Nonempty (LowRecoverySlowSpan fast T) := by
  have hlat : 2 / 5 < f.latency ∧ f.latency < 9 / 10 := by
    have h := readyPulse_mid_root_after_four_tenths hs.charge.2 hg
      (by linarith [f.early] : s.time ≤ s.time + f.latency) f.response_root
    exact ⟨by linarith,f.deadline⟩
  have hbfast : fast.final.x 0 .b = s.x 0 .b := by rw [fast.recovery,f.recovery_preserved]
  have hclock : fast.final.time = s.time + f.latency + 1 := by rw [fast.date,f.date]
  have hguards : ∀ t ∈ Icc (s.time + f.latency + 1) (s.time + 81 / 10),
      1 / 10 < (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (t - (s.time + f.latency + 1))) ∧
        (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (t - (s.time + f.latency + 1))) ≤ 1 / 4 :=
    variable_gap_first_slow_guards hB hlat ⟨by linarith,le_rfl⟩
  by_cases heq : T = fast.final.time
  · refine ⟨{
      final := fast.final
      execution := .nil _
      contacts_transversal := trivial
      date := heq.symm
      main_slow := fast.main_slow
      auxiliary := fast.auxiliary
      rest := fast.rest
      trained_rest := fast.sensor_charge
      raw_none := fast.raw_none
      charge := by rw [fast.charge]; constructor <;> norm_num
      charge_clock := by rw [heq,hclock,sub_self,mul_zero,Real.exp_zero,mul_one,fast.charge]
      pending := rfl
      gains := fun _ _ => rfl
      recovery := fun _ => rfl
      emissions := rfl
      deliveries := rfl
      physical := fast.physical
      raw_valid := fast.raw_valid
      initial_low_b := hB
      firing_bounds := hlat
      horizon_upper := hend
    }⟩
  · have hT : fast.final.time < T := lt_of_le_of_ne hstart (Ne.symm heq)
    let flow : Flow θ fast.final (protectedMainEnd θ fast.final 0 p .slow .ready none T) :=
      protectedMainFlow fast.final 0 p .slow .ready none hT (Or.inr rfl) (Or.inl rfl)
        fast.main_slow (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (fast.auxiliary 0 p)
        (fun j q _ => fast.auxiliary j q) (fast.raw_none 0 p) (fun j q _ => fast.raw_none j q)
        (by intros; contradiction) (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
        (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(fast.rest q).2])
        (by intro t ht
            simpa [protectedMainRate,fast.charge,hbfast,hclock] using
              (hguards t ⟨by linarith [ht.1],ht.2.le.trans hend⟩).1)
        (by intro t ht
            simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
            exact relax_lt (by norm_num) ht.1 (by rw [fast.sensor_charge]; norm_num) (by norm_num)) hp
    let final := protectedMainEnd θ fast.final 0 p .slow .ready none T
    let e : Execution θ (fun _ _ => []) fast.final final := .cons (.flow flow) (.nil _)
    have hformula : final.x 0 .q = (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (T - (s.time + f.latency + 1))) := by
      simp [final,protectedMainEnd,protectedMainValues,protectedMainRate,fast.charge,hbfast,hclock]
    have hrest : ∀ q, RestBand (final.x 0 (.m q)) := by
      intro q
      have hband := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (fast.rest q)
        (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
      by_cases hq : q = p
      · subst q
        simpa [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hband
      · simpa [final,protectedMainEnd,protectedMainValues,hq,RestBand] using hband
    refine ⟨{
      final := final
      execution := e
      contacts_transversal := trivial
      date := rfl
      main_slow := fast.main_slow
      auxiliary := fast.auxiliary
      rest := hrest
      trained_rest := by simp [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,relax,fast.sensor_charge]
      raw_none := fast.raw_none
      charge := by rw [hformula]; exact hguards T ⟨by linarith, hend⟩
      charge_clock := hformula
      pending := rfl
      gains := fun _ _ => rfl
      recovery := fun _ => rfl
      emissions := rfl
      deliveries := rfl
      physical := e.physical_invariant hb fast.physical
      raw_valid := e.raw_valid fast.raw_valid
      initial_low_b := hB
      firing_bounds := hlat
      horizon_upper := hend
    }⟩

end KernelR.Hybrid
