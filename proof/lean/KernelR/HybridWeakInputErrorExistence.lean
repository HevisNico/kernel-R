import KernelR.HybridFirstInputError

/-! Scalar-margin generalization of the constructed SILENT-to-ERROR entry.
The earlier birth-specific API and all existing state structures are retained. -/
namespace KernelR.Hybrid
open Set

/-- Carried READY charge and an actually weak gain retain a uniform margin,
including the positive residual left by an earlier weak pulse. -/
theorem readyPulse_weak_input_error_margin {initial amplitude start t : ℝ}
    (hi : initial ≤ 7 / 50) (ha : amplitude ≤ 7 / 6) (ht : start ≤ t) :
    readyPulse initial amplitude start t ≤ 24 / 25 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 25 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hr := mul_le_mul_of_nonneg_left (response_uniform_upper hd) (by norm_num : (0 : ℝ) ≤ 7 / 6)
  unfold readyPulse
  linarith

/-- The only quantitative input to a constructed raw SILENT piece is the
analytic main-response margin; no reaching execution is assumed. -/
theorem FirstInputSilent.raw_leg_exists_of_margin {n θ ε s i p T} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (hb : PhysicalBox θ ε)
    (hmargin : ∀ t, s.time ≤ t →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t ≤ 24 / 25)
    (hp : ∀ d ∈ s.pending, s.time + 2 ≤ d.due)
    (hT : g.final.time < T) (hTE : T ≤ g.errorDate) (hTR : T ≤ s.time + 1) :
    Nonempty (SilentLeg θ g.final i p (some s.time) T) := by
  have hs : s.time ≤ g.final.time := by
    change s.time ≤ s.time + f.latency + Real.log (5 / 4) / (θ i).lm p
    linarith [f.early,(hb.aux_durations_positive i p).1]
  apply silent_leg_exists hT g.main_ready g.aux_silent g.aux_other g.raw_active g.raw_other
    (by intro o he; have ho : o = s.time := (Option.some.inj he).symm; subst o; exact ⟨hs,hTR⟩)
    g.main_below g.aux_below
  · intro t ht
    rw [g.response_restart]
    exact hmargin t (hs.trans ht.1)
  · intro t ht
    rw [g.sensor_charge]
    have hend := silent_full_decay_end (start := g.final.time) (ne_of_gt (hb.rates_positive i p).2.1)
    change (4 / 5 : ℝ) * Real.exp (-(θ i).ls p * (g.errorDate - g.final.time)) = 1 / 10 at hend
    rw [← hend]
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    apply Real.exp_lt_exp.mpr
    have htime : t < g.errorDate := ht.2.trans_le hTE
    nlinarith [(hb.rates_positive i p).2.1]
  · intro d hd
    rw [g.queue_preserved] at hd
    linarith [hp d hd]


/-- Construct all three real expiry branches from the analytic margin. -/
theorem FirstInputSilent.first_error_exists_of_margin {n θ ε s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (route : Router n) (hb : PhysicalBox θ ε)
    (hmargin : ∀ t, s.time ≤ t →
      readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time t ≤ 24 / 25)
    (hp : ∀ d ∈ s.pending, s.time + 2 ≤ d.due) : Nonempty (FirstInputError route g) := by
  have hpos := g.errorDate_positive hb
  have hrate := (hb.rates_positive i p).2.1
  have hfinalRawTime : g.final.time < s.time + 1 := by rw [g.date]; linarith [g.deadline]
  by_cases hE : g.errorDate ≤ s.time + 1
  · obtain ⟨leg⟩ := g.raw_leg_exists_of_margin hb hmargin hp hpos le_rfl hE
    let before := readyProtectedEnd θ g.final i p .silent (some s.time) g.errorDate
    have hthreshold : before.x i (.m p) = 1 / 10 := by
      simpa [before,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge,
        FirstInputSilent.errorDate] using silent_full_decay_end (start := g.final.time) (ne_of_gt hrate)
    by_cases hearly : g.errorDate < s.time + 1
    · exact ⟨{
        beforeError := before
        span := .cons (.flow leg.flow) (.nil _)
        span_deliveries := rfl
        span_emissions := rfl
        date := rfl
        main_before := g.main_ready
        silent_before := g.aux_silent
        other_before := g.aux_other
        sensor_before := hthreshold
        main_below := leg.main_below
        aux_below := leg.aux_below
        charge_margin := leg.charge_margin
        pending := g.queue_preserved
        gain_preserved := g.gain_preserved
        recovery_preserved := g.recovery_preserved
        raw_option := Or.inl ⟨g.raw_active,hearly⟩
        raw_other := g.raw_other
      }⟩
    · have heq : g.errorDate = s.time + 1 := le_antisymm hE (le_of_not_gt hearly)
      let expired := setRaw before i p none
      let expiry := rawExpiryJump (route := route) before i p s.time g.raw_active heq
      refine ⟨{
        beforeError := expired
        span := .cons (.flow leg.flow) (.cons (.jump expiry) (.nil _))
        span_deliveries := rfl
        span_emissions := rfl
        date := rfl
        main_before := g.main_ready
        silent_before := g.aux_silent
        other_before := g.aux_other
        sensor_before := hthreshold
        main_below := leg.main_below
        aux_below := leg.aux_below
        charge_margin := leg.charge_margin
        pending := g.queue_preserved
        gain_preserved := g.gain_preserved
        recovery_preserved := g.recovery_preserved
        raw_option := Or.inr ⟨by simp [expired,setRaw],heq.ge⟩
        raw_other := ?_
      }⟩
      intro j q hh
      rw [raw_update_other _ _ _ _ _ _ hh]
      exact g.raw_other j q hh
  · have hRE : s.time + 1 < g.errorDate := lt_of_not_ge hE
    obtain ⟨first⟩ := g.raw_leg_exists_of_margin hb hmargin hp hfinalRawTime hRE.le le_rfl
    let middle := readyProtectedEnd θ g.final i p .silent (some s.time) (s.time + 1)
    let expired := setRaw middle i p none
    have hraw : expired.raw i p = none := by simp [expired,setRaw]
    have hother : ∀ j q, j ≠ i ∨ q ≠ p → expired.raw j q = none := by
      intro j q hh
      rw [raw_update_other _ _ _ _ _ _ hh]
      exact g.raw_other j q hh
    have hm : ∀ j, expired.main j = .ready := g.main_ready
    have ha : expired.aux i p = .silent := g.aux_silent
    have hao : ∀ j q, j ≠ i ∨ q ≠ p → expired.aux j q = .ready := g.aux_other
    have hsensor : expired.x i (.m p) =
        (4 / 5 : ℝ) * Real.exp (-(θ i).ls p * (s.time + 1 - g.final.time)) := by
      simp [expired,middle,readyProtectedEnd,readyProtectedValues,protectedReadyRate,g.sensor_charge,setRaw]
    have hsensorpos : 0 < expired.x i (.m p) := by rw [hsensor]; positivity
    have hend : expired.x i (.m p) * Real.exp (-(θ i).ls p * (g.errorDate - expired.time)) = 1 / 10 := by
      rw [hsensor,mul_assoc,← Real.exp_add]
      change (4 / 5 : ℝ) * Real.exp
        (-(θ i).ls p * (s.time + 1 - g.final.time) + -(θ i).ls p * (g.errorDate - (s.time + 1))) = _
      rw [show -(θ i).ls p * (s.time + 1 - g.final.time) +
        -(θ i).ls p * (g.errorDate - (s.time + 1)) = -(θ i).ls p * (g.errorDate - g.final.time) by ring]
      exact silent_full_decay_end (start := g.final.time) (ne_of_gt hrate)
    have hqnone : ∀ t ∈ Icc expired.time g.errorDate, readyPulse (expired.x i .q)
        (Real.exp (expired.x i (.z p)) * rawInputScale none expired.time) expired.time t ≤ 24 / 25 := by
      intro t ht
      simp only [rawInputScale,mul_zero,readyPulse_zero_eq_relax]
      have hmargin : expired.x i .q ≤ 24 / 25 := first.charge_margin
      have hc := decay_upper (show expired.x i .q - 1 / 10 ≤ (43 / 50 : ℝ) by
        linarith) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (sub_nonneg.mpr ht.1)
      unfold relax
      linarith
    have hxnone : ∀ t ∈ Ico expired.time g.errorDate,
        1 / 10 < expired.x i (.m p) * Real.exp (-(θ i).ls p * (t - expired.time)) := by
      intro t ht
      rw [← hend]
      apply mul_lt_mul_of_pos_left _ hsensorpos
      apply Real.exp_lt_exp.mpr
      nlinarith [ht.2]
    obtain ⟨last⟩ := silent_leg_exists (show expired.time < g.errorDate from hRE) hm ha hao hraw hother
      (by intro o ho; contradiction) first.main_below first.aux_below hqnone hxnone (by
        intro d hd
        change d ∈ g.final.pending at hd
        rw [g.queue_preserved] at hd
        linarith [hp d hd,(g.errorDate_bounds hb).2])
    let before := readyProtectedEnd θ expired i p .silent none g.errorDate
    let expiry := rawExpiryJump (route := route) middle i p s.time g.raw_active rfl
    exact ⟨{
      beforeError := before
      span := .cons (.flow first.flow) (.cons (.jump expiry) (.cons (.flow last.flow) (.nil _)))
      span_deliveries := rfl
      span_emissions := rfl
      date := rfl
      main_before := hm
      silent_before := ha
      other_before := hao
      sensor_before := by
        simpa [before,readyProtectedEnd,readyProtectedValues,protectedReadyRate] using hend
      main_below := last.main_below
      aux_below := last.aux_below
      charge_margin := last.charge_margin
      pending := g.queue_preserved
      gain_preserved := g.gain_preserved
      recovery_preserved := g.recovery_preserved
      raw_option := Or.inr ⟨hraw,hRE.le⟩
      raw_other := hother
    }⟩


/-- A source with weak learned gain can enter ERROR after its true SILENT
phase while retaining arbitrary birth-family carried charge up to .14. -/
theorem FirstInputSilent.weak_raw_leg_exists {n θ ε s i p T} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (hb : PhysicalBox θ ε)
    (hqi : s.x i .q ≤ 7 / 50) (hg : Real.exp (s.x i (.z p)) ≤ 7 / 6)
    (hp : ∀ d ∈ s.pending, s.time + 2 ≤ d.due)
    (hT : g.final.time < T) (hTE : T ≤ g.errorDate) (hTR : T ≤ s.time + 1) :
    Nonempty (SilentLeg θ g.final i p (some s.time) T) := by
  exact g.raw_leg_exists_of_margin hb (fun t ht => readyPulse_weak_input_error_margin hqi hg ht)
    hp hT hTE hTR

/-- The three raw-expiry orders are constructed from a real weak input with
its own carried charge and gain, without imposing a birth-charge reset. -/
theorem FirstInputSilent.weak_first_error_exists {n θ ε s i p} {f : @FirstInputMark n θ s i p}
    (g : FirstInputSilent f) (route : Router n) (hb : PhysicalBox θ ε)
    (hqi : s.x i .q ≤ 7 / 50) (hg : Real.exp (s.x i (.z p)) ≤ 7 / 6)
    (hp : ∀ d ∈ s.pending, s.time + 2 ≤ d.due) : Nonempty (FirstInputError route g) := by
  exact g.first_error_exists_of_margin route hb
    (fun t ht => readyPulse_weak_input_error_margin hqi hg ht) hp

end KernelR.Hybrid
