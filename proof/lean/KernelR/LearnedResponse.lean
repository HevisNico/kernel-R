import KernelR.HybridReady
import KernelR.HybridRegion
import KernelR.HybridResponseBounds
import CommutationE
import FirstCrossing
import FutureWave

/-! Real bounds for a learned, noiseless R response. These refer to the actual
exp/log expressions, not to stored certificate endpoints. They do not construct
the complete hybrid pulse cycle or assert its reachability from birth. -/
namespace KernelR.Hybrid
open Set

theorem response_linear_upper {t : ℝ} (ht : 0 ≤ t) : response t ≤ a * t := by
  simpa [response, A22.LemmaE.h] using
    A22.LemmaE.h_le_linear (A := a) (K := 1/2) (by norm_num)
      (by linarith [a_coarse_bounds.1]) ht

theorem exp_neg_nine_twentieths_lower : (637/1000:ℝ) ≤ Real.exp (-(9/20:ℝ)) := by
  have h := Real.exp_approx_end 5 6 (-(9/20:ℝ)) rfl (by norm_num)
  norm_num [Real.expNear, Finset.sum_range_succ] at h
  have hh := (abs_le.mp h).1
  linarith

theorem response_nine_tenths_lower : (1/2:ℝ) < response (9/10) := by
  have ha : (4/3:ℝ) ≤ a := by
    dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have had : 0 < a - 1/2 := by linarith
  have hfactor : (14/9:ℝ) ≤ a / (a-1/2) :=
    (le_div_iff₀ had).mpr (by linarith [a_coarse_bounds.2])
  have hex : (16/5:ℝ) ≤ Real.exp (6/5) := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 6/5 by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hbig : (16/5:ℝ) ≤ Real.exp (a*(9/10)) :=
    hex.trans (Real.exp_le_exp.mpr (by linarith))
  have hp := Real.exp_pos (-(a*(9/10)))
  have hid : Real.exp (a*(9/10)) * Real.exp (-(a*(9/10))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsmall : Real.exp (-a*(9/10)) ≤ (5/16:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hbig hp.le
    rw [hid] at hm
    simpa only [neg_mul] using (show Real.exp (-(a*(9/10))) ≤ (5/16:ℝ) by linarith)
  have hdiff : (637/1000:ℝ) - 5/16 ≤
      Real.exp (-(1/2:ℝ)*(9/10)) - Real.exp (-a*(9/10)) := by
    have h := exp_neg_nine_twentieths_lower
    norm_num [neg_mul] at h hsmall ⊢
    linarith
  have hm := mul_le_mul hfactor hdiff (by norm_num : (0:ℝ) ≤ 637/1000-5/16)
    (le_trans (by norm_num : (0:ℝ) ≤ 14/9) hfactor)
  dsimp [response]
  linarith

noncomputable def learnedHead (gain t : ℝ) : ℝ := 1/10 + gain * response t

/-- The three exact ERROR doses of the existing slow protocol produce a gain
inside the new learned section, for the entire stated birth perturbation. -/
theorem three_dose_gain_in_section {eta : ℝ} (heta : |eta| ≤ 1/100000) :
    9/5 ≤ (3/10:ℝ) * Real.exp (9/5+eta) ∧
      (3/10:ℝ) * Real.exp (9/5+eta) ≤ 19/10 := by
  have hlow : (49/20:ℝ) ≤ Real.exp (899/1000) := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 899/1000 by norm_num) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhigh : Real.exp (901/1000:ℝ) ≤ 5/2 := by
    have h := Real.exp_approx_end 5 6 (901/1000:ℝ) rfl (by norm_num)
    norm_num [Real.expNear, Finset.sum_range_succ] at h
    linarith [(abs_le.mp h).2]
  have hb := abs_le.mp heta
  have hlo : (49/20:ℝ) ≤ Real.exp ((9/5+eta)/2) :=
    hlow.trans (Real.exp_le_exp.mpr (by linarith))
  have hhi : Real.exp ((9/5+eta)/2) ≤ (5/2:ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : (9/5+eta)/2 ≤ 901/1000)).trans hhigh
  have hsplit : Real.exp (9/5+eta) = Real.exp ((9/5+eta)/2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  have hslo := mul_le_mul hlo hlo (by norm_num : (0:ℝ) ≤ 49/20) (by linarith :
    0 ≤ Real.exp ((9/5+eta)/2))
  have hshi := mul_le_mul hhi hhi (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 5/2)
  constructor <;> nlinarith

theorem prepared_recovery_in_section {birth : ℝ}
    (hb : (7999/100000:ℝ) ≤ birth ∧ birth ≤ 8001/100000) :
    17/100 ≤ birth + 1/10 ∧ birth + 1/10 ≤ 1/5 := by constructor <;> linarith

theorem learned_head_early {gain t : ℝ} (hg : 9/5 ≤ gain ∧ gain ≤ 19/10)
    (ht : 0 ≤ t ∧ t ≤ 3/10) : learnedHead gain t < 1 := by
  have hr := response_linear_upper ht.1
  have hp := response_nonnegative ht.1
  have hat := mul_le_mul_of_nonneg_right a_coarse_bounds.2.le ht.1
  have hu : response t ≤ (21/50:ℝ) := by linarith
  have hm := mul_le_mul hg.2 hu hp (by norm_num : (0:ℝ) ≤ 19/10)
  dsimp [learnedHead]
  linarith

theorem learned_head_late {gain : ℝ} (hg : 9/5 ≤ gain ∧ gain ≤ 19/10) :
    1 < learnedHead gain (9/10) := by
  have hp := response_nine_tenths_lower
  have hm := mul_le_mul_of_nonneg_right hg.1 (le_trans (by norm_num) hp.le)
  have hstrict := mul_lt_mul_of_pos_left hp (show (0:ℝ) < 9/5 by norm_num)
  dsimp [learnedHead]
  linarith

/-- The reference latency exists uniquely and reaches exactly the threshold.
The gain interval includes the slow protocol's learned active gain. -/
theorem learned_latency_exists {gain : ℝ} (hg : 9/5 ≤ gain ∧ gain ≤ 19/10) :
    ∃ f, 3/10 < f ∧ f ≤ 9/10 ∧ learnedHead gain f = 1 ∧
      A22.Crossing.IsFirstCrossing (learnedHead gain) 0 f := by
  have hc : Continuous (learnedHead gain) := by unfold learnedHead response; fun_prop
  obtain ⟨f, hf, hupper⟩ := A22.Crossing.first_crossing_exists
    (a := 0) (b := 9/10) (by norm_num) hc.continuousOn (learned_head_late hg).le
  have hlower : (3/10:ℝ) < f := by
    by_contra hn
    have h := learned_head_early hg ⟨hf.1, le_of_not_gt hn⟩
    linarith [hf.2.1]
  have hbound := continuous_bound_from_Ico (show (0:ℝ) < f by linarith)
    hc.continuousOn (fun t ht => (hf.2.2 t ht).le) f ⟨hf.1, le_rfl⟩
  exact ⟨f, hlower, hupper, le_antisymm hbound hf.2.1, hf⟩

theorem learned_latency_unique {gain f g : ℝ}
    (hf : A22.Crossing.IsFirstCrossing (learnedHead gain) 0 f)
    (hg : A22.Crossing.IsFirstCrossing (learnedHead gain) 0 g) : f = g :=
  A22.Crossing.first_crossing_unique hf hg

/-- The response composes across auxiliary-mode and other-cell events. -/
theorem readyPulse_compose (initial gain start middle finish : ℝ) :
    readyPulse (readyPulse initial gain start middle)
      (gain * Real.exp (-a*(middle-start))) middle finish =
      readyPulse initial gain start finish := by
  have split (rate : ℝ) : Real.exp (-rate*(finish-start)) =
      Real.exp (-rate*(middle-start)) * Real.exp (-rate*(finish-middle)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [readyPulse, response]
  rw [split (1/2), split a]
  ring

/-- The READY physical span may contain actual auxiliary jumps and arbitrary
other-cell interleavings. No prescribed auxiliary event word is assumed. -/
def Execution.ReadyInput {n θ route s u} (i : Fin n) (p : Port) (origin : ℝ) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest =>
    f.mainIs i .ready ∧ s.raw i p = some origin ∧
      (∀ j, j ≠ p → s.raw i j = none) ∧ s.aux i p ≠ .error ∧ rest.ReadyInput i p origin
  | .cons (.jump _) rest => rest.ReadyInput i p origin

theorem Execution.ready_input_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hw : e.ReadyInput i p origin) :
    u.x i .q = readyPulse (s.x i .q)
      (Real.exp (s.x i (.z p)) * Real.exp (-a*(s.time-origin))) s.time u.time := by
  induction e with
  | nil => simp [readyPulse_initial]
  | @cons s middle u step rest ih =>
    cases step with
    | flow f =>
      have hf := f.ready_single_pulse_solution i p origin hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
        middle.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hf
      have hz := f.gain_constant_without_error i p hw.2.2.2.1 middle.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hz
      have ht := ih hw.2.2.2.2
      have amp : Real.exp (s.x i (.z p)) * Real.exp (-a*(middle.time-origin)) =
          (Real.exp (s.x i (.z p)) * Real.exp (-a*(s.time-origin))) *
            Real.exp (-a*(middle.time-s.time)) := by
        have split : Real.exp (-a*(middle.time-origin)) =
            Real.exp (-a*(s.time-origin)) * Real.exp (-a*(middle.time-s.time)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [split, mul_assoc]
      rw [hz, amp, hf] at ht
      exact ht.trans (readyPulse_compose _ _ _ _ _)
    | jump j =>
      simpa only [j.physical_continuous, j.time_unchanged] using ih hw

theorem learned_head_strictMono {gain : ℝ} (hg : 0 < gain) :
    StrictMonoOn (learnedHead gain) (Icc 0 1) := by
  have ha : (4/3:ℝ) < a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  have he : Real.exp (-(1/2:ℝ)) ≤ 2/3 := by
    have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1/2:ℝ))
      (Real.exp_pos (-(1/2:ℝ))).le
    have hid : Real.exp (1/2:ℝ) * Real.exp (-(1/2:ℝ)) = 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hid] at hm
    linarith
  have hea : Real.exp (-a) = (1/4:ℝ) := by
    rw [a, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 4)]; norm_num
  have hm := A22.Future.h_strictMonoOn (A := a) (K := 1/2) (by norm_num)
    (by linarith) (by rw [hea]; nlinarith)
  intro x hx y hy hxy
  have hh : response x < response y := by simpa [response, A22.LemmaE.h] using hm hx hy hxy
  simpa [learnedHead, add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hh hg) (1/10)

/-- Fixed latency for an actual READY execution span, including auxiliary
interleavings. Existence and the no-ERROR span must still be proved locally. -/
theorem Execution.learned_reference_latency {n θ route s u after}
    (e : @Execution n θ route s u) (exit : Jump route u after) (i : Fin n) (p : Port)
    (hw : e.ReadyInput i p s.time) (hq : s.x i .q = 1/10)
    (hu : u.main i = .ready) (ha : after.main i = .fast)
    (hspan : u.time - s.time ∈ Icc 0 1) {reference : ℝ}
    (hrefspan : reference ∈ Icc 0 1)
    (href : learnedHead (Real.exp (s.x i (.z p))) reference = 1) :
    u.time = s.time + reference := by
  have hqend := exit.fast_entry_guard i (by rw [hu]; decide) ha
  rw [exit.physical_continuous] at hqend
  have hresponse := e.ready_input_solution i p s.time hw
  have hvalue : learnedHead (Real.exp (s.x i (.z p))) (u.time-s.time) = 1 := by
    simpa [readyPulse, learnedHead, hq, hqend] using hresponse.symm
  have he := (learned_head_strictMono (Real.exp_pos _)).injOn hspan hrefspan (hvalue.trans href.symm)
  linarith

/-- After a physical FAST phase and constant recovery, the exact return date
is strictly below the slow protocol's minimum gap. This is a real log bound. -/
theorem learned_return_before_gap {b f : ℝ} (hb : 17/100 ≤ b ∧ b ≤ 1/5)
    (hf : f ≤ 9/10) : f + 1 + Real.log (5/2) / b < (15/2:ℝ) := by
  have hbp : 0 < b := by linarith
  have hd : Real.log (5/2) / b < (28/5:ℝ) := by
    apply (div_lt_iff₀ hbp).mpr
    nlinarith [KernelR.log_recovery_bounds.2]
  linarith

theorem learned_return_after_auxiliary {b f : ℝ} (hb : 17/100 ≤ b ∧ b ≤ 1/5)
    (hf : 3/10 < f) : (3/2:ℝ) < f + 1 + Real.log (5/2) / b := by
  have hbp : 0 < b := by linarith
  have hd : (9/2:ℝ) < Real.log (5/2) / b := by
    apply (lt_div_iff₀ hbp).mpr
    nlinarith [KernelR.log_recovery_bounds.1]
  linarith

end KernelR.Hybrid
