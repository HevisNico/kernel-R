import KernelR.HybridLowRecoverySlowContinuation

/-! Expose the single actual SLOW flow extending an already constructed span.
The new energy path starts at the carried endpoint, without reinitialization. -/
namespace KernelR.Hybrid
open Set

/-- Extend the same actual low-recovery execution by one positive flow.
The explicit flow lets callers retain cuts at either endpoint or in its
interior, rather than replacing an opaque continuation with another path. -/
theorem LowRecoverySlowSpan.flow_continuation_exists {θ ε} {s : Snapshot 1} {p : Port}
    {f : FirstLearnedFire θ (fun _ _ => []) s 0 p} {fast : MidLearnedFastEnd f} {T1 : ℝ}
    (c : LowRecoverySlowSpan fast T1) (hb : PhysicalBox θ ε) (T2 : ℝ)
    (hC : T1 < T2) (hend : T2 ≤ s.time + 81 / 10)
    (hp : ∀ d ∈ c.final.pending, T2 ≤ d.due) :
    ∃ full : LowRecoverySlowSpan fast T2,
      ∃ nextFlow : Flow θ c.final full.final,
        full.execution = c.execution.append (.cons (.flow nextFlow) (.nil _)) := by
  have hT : c.final.time < T2 := by rw [c.date]; exact hC
  have hbcurrent : c.final.x 0 .b = s.x 0 .b :=
    (c.recovery 0).trans ((fast.recovery 0).trans (f.recovery_preserved 0))
  have hfastClock : fast.final.time = s.time + f.latency + 1 := by rw [fast.date,f.date]
  have hglobalStart : s.time + f.latency + 1 ≤ c.final.time := by
    rw [← hfastClock]
    exact c.execution.time_monotone
  have hrestart (t : ℝ) : c.final.x 0 .q * Real.exp (-c.final.x 0 .b * (t - c.final.time)) =
      (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (t - (s.time + f.latency + 1))) := by
    rw [hbcurrent,c.charge_clock,c.date,mul_assoc,attenuation_split]
  have hguards : ∀ t ∈ Icc (s.time + f.latency + 1) (s.time + 81 / 10),
      1 / 10 < (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (t - (s.time + f.latency + 1))) ∧
        (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (t - (s.time + f.latency + 1))) ≤ 1 / 4 :=
    variable_gap_first_slow_guards c.initial_low_b c.firing_bounds ⟨by linarith,le_rfl⟩
  let flow : Flow θ c.final (protectedMainEnd θ c.final 0 p .slow .ready none T2) :=
    protectedMainFlow c.final 0 p .slow .ready none hT (Or.inr rfl) (Or.inl rfl)
      c.main_slow (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (c.auxiliary 0 p)
      (fun j q _ => c.auxiliary j q) (c.raw_none 0 p) (fun j q _ => c.raw_none j q)
      (by intros; contradiction) (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(c.rest q).2])
      (by intro t ht
          simp only [reduceCtorEq,ite_false,protectedMainRate]
          rw [hrestart]
          exact (hguards t ⟨hglobalStart.trans ht.1,ht.2.le.trans hend⟩).1)
      (by intro t ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by rw [c.trained_rest]; norm_num) (by norm_num)) hp
  let final := protectedMainEnd θ c.final 0 p .slow .ready none T2
  let tail : Execution θ (fun _ _ => []) c.final final := .cons (.flow flow) (.nil _)
  let e := c.execution.append tail
  have hformula : final.x 0 .q = (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (T2 - (s.time + f.latency + 1))) := by
    change c.final.x 0 .q * Real.exp (-c.final.x 0 .b * (T2 - c.final.time)) = _
    exact hrestart T2
  have hrest : ∀ q, RestBand (final.x 0 (.m q)) := by
    intro q
    have hband := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hT.le (c.rest q)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases hq : q = p
    · subst q
      simpa [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,RestBand] using hband
    · simpa [final,protectedMainEnd,protectedMainValues,hq,RestBand] using hband
  let d : LowRecoverySlowSpan fast T2 := {
    final := final
    execution := e
    date := rfl
    main_slow := c.main_slow
    auxiliary := c.auxiliary
    rest := hrest
    trained_rest := by simp [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,relax,c.trained_rest]
    raw_none := c.raw_none
    charge := by rw [hformula]; exact hguards T2 ⟨hglobalStart.trans hT.le,hend⟩
    charge_clock := hformula
    pending := c.pending
    gains := c.gains
    recovery := c.recovery
    emissions := by rw [Execution.emissions_append,c.emissions]; rfl
    deliveries := by rw [Execution.deliveries_append,c.deliveries]; rfl
    physical := tail.physical_invariant hb c.physical
    raw_valid := tail.raw_valid c.raw_valid
    initial_low_b := c.initial_low_b
    firing_bounds := c.firing_bounds
    horizon_upper := hend
  }
  exact ⟨d,flow,rfl⟩

end KernelR.Hybrid
