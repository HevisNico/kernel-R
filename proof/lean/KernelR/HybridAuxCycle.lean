import KernelR.HybridPhases

/-! The autonomous auxiliary cycle is extracted from a sufficiently long actual
execution. Its chronology and real duration are conclusions, not case labels. -/
namespace KernelR.Hybrid

theorem AuxDeparture.after_charge {n θ route s u i p mode} {e : @Execution n θ route s u}
    (d : AuxDeparture e i p mode) : d.afterExit.x i (.m p) = protectedFloor mode := by
  rw [d.exit.physical_continuous, d.charge]

theorem AuxDeparture.after_time {n θ route s u i p mode} {e : @Execution n θ route s u}
    (d : AuxDeparture e i p mode) : d.afterExit.time = s.time + auxRemaining θ s i p mode := by
  rw [d.exit.time_unchanged, d.date]

noncomputable def auxCycleDuration (θ : Parameters) (p : Port) : ℝ :=
  Real.log (5 / 4) / θ.lm p + Real.log 8 / θ.ls p + Real.log 4 / θ.le p

theorem PhysicalBox.aux_durations_positive {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    0 < Real.log (5 / 4) / (θ i).lm p ∧ 0 < Real.log 8 / (θ i).ls p ∧
      0 < Real.log 4 / (θ i).le p :=
  ⟨div_pos (Real.log_pos (by norm_num)) (hb.rates_positive i p).1,
   div_pos (Real.log_pos (by norm_num)) (hb.rates_positive i p).2.1,
   div_pos (Real.log_pos (by norm_num)) (hb.rates_positive i p).2.2⟩

structure AuxCycle {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) where
  markPhase : AuxDeparture e i p .mark
  silentPhase : AuxDeparture markPhase.rest i p .silent
  errorPhase : AuxDeparture silentPhase.rest i p .error
  completion_date : errorPhase.afterExit.time = s.time + auxCycleDuration (θ i) p

theorem AuxCycle.ready_mode {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : AuxCycle e i p) : cycle.errorPhase.afterExit.aux i p = .ready :=
  cycle.errorPhase.mode_after

/-- All three phases, their actual jumps, and the final READY state are
obtained from e. Other-cell events and all legal simultaneous orders remain. -/
theorem Execution.aux_cycle_completion {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hs : s.aux i p = .mark)
    (hq : s.x i (.m p) = 1) (ht : s.time + auxCycleDuration (θ i) p < u.time) :
    Nonempty (AuxCycle e i p) := by
  rcases hb.aux_durations_positive i p with ⟨hd₁, hd₂, hd₃⟩
  have hfirst : auxRemaining θ s i p .mark = Real.log (5 / 4) / (θ i).lm p := by
    norm_num [auxRemaining, protectedFloor, auxRate, hq]
  obtain ⟨mark⟩ := e.aux_phase_completion hb i p .mark (by decide) hs
    (by norm_num [protectedFloor, hq]) (by rw [hfirst]; dsimp [auxCycleDuration] at ht; linarith)
  have hsecond : auxRemaining θ mark.afterExit i p .silent = Real.log 8 / (θ i).ls p := by
    norm_num [auxRemaining, protectedFloor, auxRate, mark.after_charge]
  obtain ⟨silent⟩ := mark.rest.aux_phase_completion hb i p .silent (by decide)
    mark.mode_after (by norm_num [mark.after_charge, protectedFloor]) (by
      rw [mark.after_time, hfirst, hsecond]
      dsimp [auxCycleDuration] at ht
      linarith)
  have hthird : auxRemaining θ silent.afterExit i p .error = Real.log 4 / (θ i).le p := by
    norm_num [auxRemaining, protectedFloor, auxRate, silent.after_charge]
  obtain ⟨error⟩ := silent.rest.aux_phase_completion hb i p .error (by decide)
    silent.mode_after (by norm_num [silent.after_charge, protectedFloor]) (by
      rw [silent.after_time, mark.after_time, hfirst, hsecond, hthird]
      dsimp [auxCycleDuration] at ht
      linarith)
  refine ⟨⟨mark, silent, error, ?_⟩⟩
  rw [error.after_time, silent.after_time, mark.after_time, hfirst, hsecond, hthird]
  dsimp [auxCycleDuration]
  ring

theorem protected_duration_upper {ε base nominal rate : ℝ}
    (he : ε ≤ 1 / 10) (hb : 0 < base) (hn : 0 < nominal)
    (h : InRelativeBox ε (nominal / base) rate) : nominal / rate ≤ base * (10 / 9) := by
  have hr : 0 < rate := by
    have hp : 0 < nominal / base * (1 - ε) := mul_pos (div_pos hn hb) (by linarith)
    exact hp.trans_le h.1
  apply (div_le_iff₀ hr).mpr
  have hl : nominal / base * (9 / 10) ≤ rate := by nlinarith [h.1]
  have hm := mul_le_mul_of_nonneg_left hl hb.le
  have heq : base * (nominal / base * (9 / 10)) = nominal * (9 / 10) := by
    field_simp
  rw [heq] at hm
  nlinarith

/-- Actual independent fabrication rates imply the entire protected cycle is
at most 41/30. No stored interval membership is used. -/
theorem PhysicalBox.aux_cycle_duration_upper {n θ ε} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : auxCycleDuration (θ i) p ≤ 41 / 30 := by
  have hm := protected_duration_upper hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 1 / 50)
    (Real.log_pos (by norm_num : (1 : ℝ) < 5 / 4)) (hb.2 i p).2.1
  have hs := protected_duration_upper hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 53 / 50)
    (Real.log_pos (by norm_num : (1 : ℝ) < 8)) (hb.2 i p).2.2.1
  have he := protected_duration_upper hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 3 / 20)
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (hb.2 i p).2.2.2.1
  dsimp [auxCycleDuration, a] at *
  linarith

theorem protected_duration_lower {ε base nominal rate : ℝ}
    (he : ε ≤ 1 / 10) (hb : 0 < base) (hn : 0 < nominal)
    (h : InRelativeBox ε (nominal / base) rate) : base * (10 / 11) ≤ nominal / rate := by
  have hr : 0 < rate := by
    have hp : 0 < nominal / base * (1 - ε) := mul_pos (div_pos hn hb) (by linarith)
    exact hp.trans_le h.1
  apply (le_div_iff₀ hr).mpr
  have hu : rate ≤ nominal / base * (11 / 10) := h.2.trans
    (mul_le_mul_of_nonneg_left (show 1 + ε ≤ (11 / 10 : ℝ) by linarith) (div_pos hn hb).le)
  have hm := mul_le_mul_of_nonneg_left hu hb.le
  have heq : base * (nominal / base * (11 / 10)) = nominal * (11 / 10) := by field_simp
  rw [heq] at hm
  nlinarith

theorem PhysicalBox.aux_durations_lower {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    (1 / 55 : ℝ) ≤ Real.log (5 / 4) / (θ i).lm p ∧
    (53 / 55 : ℝ) ≤ Real.log 8 / (θ i).ls p ∧ (3 / 22 : ℝ) ≤ Real.log 4 / (θ i).le p := by
  have hm := protected_duration_lower hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 1 / 50)
    (Real.log_pos (by norm_num : (1 : ℝ) < 5 / 4)) (hb.2 i p).2.1
  have hs := protected_duration_lower hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 53 / 50)
    (Real.log_pos (by norm_num : (1 : ℝ) < 8)) (hb.2 i p).2.2.1
  have he := protected_duration_lower hb.epsilon_bounds.2 (by norm_num : (0 : ℝ) < 3 / 20)
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (hb.2 i p).2.2.2.1
  norm_num at hm hs he
  exact ⟨hm, hs, he⟩

theorem PhysicalBox.aux_cycle_duration_lower {n θ ε} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : (123 / 110 : ℝ) ≤ auxCycleDuration (θ i) p := by
  rcases hb.aux_durations_lower i p with ⟨hm, hs, he⟩
  dsimp [auxCycleDuration]
  linarith

end KernelR.Hybrid
