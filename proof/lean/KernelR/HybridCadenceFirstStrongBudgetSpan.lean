import KernelR.HybridCadenceFirstStrongJitterSpan

/-! Full3/20 packet budgets require a first received gap through4.4. The
source is exact rest, so its own three-dose latency is(.65,.66); the broader
carried-charge latency>.4 alone would not preserve the MARK charge band. -/
namespace KernelR.Hybrid
open Set

theorem cadence_first_strong_full_budget_charge_bounds {B S latency time : ℝ}
    (hB : 17999 / 100000 ≤ B ∧ B ≤ 18001 / 100000)
    (hlat : 13 / 20 < latency ∧ latency < 33 / 50)
    (ht : S + latency + 1 ≤ time) (hu : time ≤ S + 22 / 5) :
    37 / 250 < (1 / 4 : ℝ) * Real.exp (-B * (time - (S + latency + 1))) ∧
      (1 / 4 : ℝ) * Real.exp (-B * (time - (S + latency + 1))) ≤ 1 / 4 := by
  have hd : 0 ≤ time - (S + latency + 1) ∧ time - (S + latency + 1) < 11 / 4 := by
    constructor <;> linarith [hlat.1]
  have hI : 0 ≤ B * (time - (S + latency + 1)) ∧ B * (time - (S + latency + 1)) < 1 / 2 := by
    constructor <;> nlinarith [hB.1,hB.2]
  have he : (3 / 5 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have h := Real.exp_bound (x := -(1 / 2 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hlo := Real.exp_le_exp.mpr (show -(1 / 2 : ℝ) ≤ -B * (time - (S + latency + 1)) by nlinarith [hI.2])
  have hhi := Real.exp_le_one_iff.mpr (show -B * (time - (S + latency + 1)) ≤ 0 by nlinarith [hI.1])
  constructor <;> linarith

theorem FirstLearnedFire.cadence_first_strong_full_budget_span_exists {θ ε} {s : Snapshot 1} {p : Port}
    (fire : FirstLearnedFire θ (fun _ _ => []) s 0 p) (hb : PhysicalBox θ ε)
    (fast : PortFastCompletion θ (fun _ _ => []) fire.final p) (T : ℝ)
    (hgap : s.time + 37 / 10 ≤ T ∧ T ≤ s.time + 22 / 5)
    (hq : s.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hB : 17999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 18001 / 100000)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    Nonempty (CadenceFirstStrongJitterSpan fast T) := by
  have hg := cadence_three_dose_gain_bounds hz
  have hroot : readyPulse (1 / 10) (Real.exp (s.x 0 (.z p))) 0 fire.latency = 1 := by
    simpa only [readyPulse,hq,add_sub_cancel_left,sub_zero] using fire.response_root
  have heq := restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
    ⟨by linarith [fire.early],fire.deadline.le⟩ hroot
  have hlat : 13 / 20 < fire.latency ∧ fire.latency < 33 / 50 := by
    rw [heq]
    exact restLatency_three_doses_bounds hz.1 hz.2
  have hbfast : fast.final.x 0 .b = s.x 0 .b := by rw [fast.recovery,fire.recovery_preserved]
  have hclock : fast.final.time = s.time + fire.latency + 1 := by rw [fast.date,fire.date]
  have hT : fast.final.time < T := by rw [hclock]; linarith [hlat.2,hgap.1]
  have hguards : ∀ time ∈ Icc fast.final.time T,
      37 / 250 < (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (time - (s.time + fire.latency + 1))) ∧
        (1 / 4 : ℝ) * Real.exp (-s.x 0 .b * (time - (s.time + fire.latency + 1))) ≤ 1 / 4 := by
    intro time ht
    exact cadence_first_strong_full_budget_charge_bounds hB hlat (by rw [← hclock]; exact ht.1) (ht.2.trans hgap.2)
  have hpending : ∀ d ∈ fast.final.pending, T ≤ d.due := by
    intro d hd
    rw [fast.pending,fire.pending,List.append_nil] at hd
    exact hp d hd
  let flow : Flow θ fast.final (protectedMainEnd θ fast.final 0 p .slow .ready none T) :=
    protectedMainFlow fast.final 0 p .slow .ready none hT (Or.inr rfl) (Or.inl rfl)
      fast.main_slow (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (fast.auxiliary 0 p)
      (fun j q _ => fast.auxiliary j q) (fast.raw_none 0 p) (fun j q _ => fast.raw_none j q)
      (by intros; contradiction) (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim)
      (by intro j q _; have hj : j = 0 := Subsingleton.elim _ _; subst j; linarith [(fast.rest q).2])
      (by intro time ht
          have h := (hguards time ⟨ht.1,ht.2.le⟩).1
          simp only [reduceCtorEq,ite_false,protectedMainRate,fast.charge,hbfast,hclock]
          linarith)
      (by intro time ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by rw [fast.sensor_charge]; norm_num) (by norm_num)) hpending
  let final := protectedMainEnd θ fast.final 0 p .slow .ready none T
  let execution : Execution θ (fun _ _ => []) fast.final final := .cons (.flow flow) (.nil _)
  have hformula : final.x 0 .q = (1 / 4 : ℝ) *
      Real.exp (-s.x 0 .b * (T - (s.time + fire.latency + 1))) := by
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
    final := final, flow := flow, execution := execution, reconstruct := rfl, final_state := rfl
    date := rfl, main_slow := fast.main_slow, auxiliary := fast.auxiliary, rest := hrest
    trained_rest := ?_, raw_none := fast.raw_none, charge := ?_, charge_clock := hformula
    energy_clock := rfl, pending := rfl, gains := fun _ _ => rfl, recovery := fun _ => rfl
    emissions := rfl, deliveries := rfl
    physical := execution.physical_invariant hb fast.physical, raw_valid := execution.raw_valid fast.raw_valid
  }⟩
  · simp [final,protectedMainEnd,protectedMainValues,rawInputScale,auxPulse_zero_eq_relax,relax,fast.sensor_charge]
  · rw [hformula]
    have h := hguards T ⟨hT.le,le_rfl⟩
    exact ⟨h.1.le,h.2⟩

end KernelR.Hybrid
