import KernelR.HybridHighGainCalendar
/-! Direct physical timing margins for the high-gain cadence handoff. -/
namespace KernelR.Hybrid
open Set

theorem response_at_twenty_six_lower : (141 / 500 : ℝ) ≤ response (13 / 50) := by
  have hden : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hratio : (391 / 250 : ℝ) ≤ a / (a - 1 / 2) :=
    (le_div_iff₀ hden).mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.2])
  have he₁ : (87809 / 100000 : ℝ) ≤ Real.exp (-(13 / 100 : ℝ)) := by
    have h := Real.exp_bound (x := -(13 / 100 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hexp : Real.exp (-(36043 / 100000 : ℝ)) ≤ 69738 / 100000 := by
    have h := Real.exp_bound (x := -(36043 / 100000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have he₂ : Real.exp (-a * (13 / 50)) ≤ 69738 / 100000 := by
    apply le_trans ?_ hexp
    apply Real.exp_le_exp.mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.1]
  have hdiff : (18071 / 100000 : ℝ) ≤ Real.exp (-(13 / 100 : ℝ)) - Real.exp (-a * (13 / 50)) := by
    linarith
  have hp := mul_le_mul hratio hdiff (by norm_num : (0 : ℝ) ≤ 18071 / 100000)
    (div_pos (by linarith [a_coarse_bounds.1]) hden).le
  unfold response
  rw [show -(1 / 2 : ℝ) * (13 / 50) = -(13 / 100) by norm_num]
  linarith

theorem readyPulse_high_rest_at_twenty_six {G : ℝ} (hg : 16 / 5 ≤ G) :
    1 < readyPulse (1 / 10) G 0 (13 / 50) := by
  have hp := mul_le_mul hg response_at_twenty_six_lower
    (by norm_num : (0 : ℝ) ≤ 141 / 500) (by linarith : 0 ≤ G)
  simp only [readyPulse,sub_self,zero_mul,add_zero,sub_zero]
  linarith

/-- The reference is the unique root of each cell's own realized high gain. -/
theorem highRestLatency_lt_twenty_six {G : ℝ} (hg : 16 / 5 ≤ G ∧ G ≤ 7 / 2) :
    highRestLatency G < 13 / 50 := by
  have hs := highRestLatency_spec hg
  have hm := (readyPulse_strictMono (initial := (1 / 10 : ℝ)) (amplitude := G)
    (start := 0) (by norm_num) (by linarith [hg.1])).monotoneOn
  by_contra hn
  have h := hm (by norm_num : (13 / 50 : ℝ) ∈ Icc 0 (0 + 9 / 10))
    ⟨by linarith [hs.1],by linarith [hs.2.1]⟩ (le_of_not_gt hn)
  rw [hs.2.2] at h
  linarith [readyPulse_high_rest_at_twenty_six hg.1]

theorem response_at_sixteen_upper : response (4 / 25) ≤ 191 / 1000 := by
  have hden : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hratio : a / (a - 1 / 2) ≤ (7821 / 5000 : ℝ) :=
    (div_le_iff₀ hden).mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])
  have he₁ : Real.exp (-(2 / 25 : ℝ)) ≤ 92312 / 100000 := by
    have h := Real.exp_bound (x := -(2 / 25 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hexp : (80106 / 100000 : ℝ) ≤ Real.exp (-(22181 / 100000 : ℝ)) := by
    have h := Real.exp_bound (x := -(22181 / 100000 : ℝ)) (n := 10) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have he₂ : (80106 / 100000 : ℝ) ≤ Real.exp (-a * (4 / 25)) := by
    apply hexp.trans
    apply Real.exp_le_exp.mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.2]
  have hdiff : Real.exp (-(2 / 25 : ℝ)) - Real.exp (-a * (4 / 25)) ≤ 12206 / 100000 := by
    linarith
  have hnon : 0 ≤ Real.exp (-(2 / 25 : ℝ)) - Real.exp (-a * (4 / 25)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith [a_coarse_bounds.1]
  have hp := mul_le_mul hratio hdiff hnon (by norm_num : (0 : ℝ) ≤ 7821 / 5000)
  unfold response
  rw [show -(1 / 2 : ℝ) * (4 / 25) = -(2 / 25) by norm_num]
  linarith

private theorem response_strictMono_early : StrictMonoOn response (Icc 0 (9 / 10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t _ => (response_derivative t).continuousAt.continuousWithinAt)
  intro t ht
  have hcc := interior_subset ht
  rw [(response_derivative t).deriv]
  linarith [response_derivative_lower hcc.1 hcc.2]

theorem readyPulse_cadence_not_before_sixteen {initial amplitude start t : ℝ}
    (hi : initial ≤ 8 / 25) (ha : amplitude ≤ 7 / 2)
    (ht : start ≤ t) (hu : t ≤ start + 4 / 25) : readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (11 / 50 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hresp := response_strictMono_early.monotoneOn
    (show t - start ∈ Icc 0 (9 / 10) from ⟨hd,by linarith⟩)
    (by norm_num : (4 / 25 : ℝ) ∈ Icc 0 (9 / 10)) (by linarith : t - start ≤ 4 / 25)
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (hresp.trans response_at_sixteen_upper)
    (by norm_num : (0 : ℝ) ≤ 7 / 2)
  unfold readyPulse
  linarith

/-- This bound concerns the actual residual-charge firing selected by the guards. -/
theorem HighGainTrigger.cadence_early_sixteen {n θ route s u i p} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (cycle : SensorCycle e i p)
    (hq : s.x i .q ≤ 8 / 25) (hg : Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) : s.time + 4 / 25 < tr.beforeFire.time := by
  have hroot := tr.firing_equation cycle hr ho hno
  by_contra hn
  have h := readyPulse_cadence_not_before_sixteen hq hg tr.span.time_monotone (le_of_not_gt hn)
  rw [hroot] at h
  exact (lt_irrefl (1 : ℝ)) h

/-- The first high-gain pulse keeps its residual latency; later resting pulses
use the reference. Both now fit the margins needed for two independent wires. -/
theorem CadenceLearnedPulse.high_residual_calendar_timing {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : CadenceLearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (ha : s.aux i p = .ready) (hx : RestBand (s.x i (.m p)))
    (hq : 1 / 10 ≤ s.x i .q ∧ s.x i .q ≤ 8 / 25)
    (hg : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 419 / 300 ≤ u.time) :
    ∃ first : ℝ, 4 / 25 < first ∧ first < 13 / 50 ∧
      first ≤ highRestLatency (Real.exp (s.x i (.z p))) ∧ e.emissionTimes i = [s.time + first] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  let first := pulse.trigger.beforeFire.time - s.time
  have hlo := pulse.trigger.cadence_early_sixteen cycle hq.2 hg.2 hr ho hno
  have hle := pulse.trigger.latency_le_high_rest cycle hq.1 hg hr ho hno
  have hspec := highRestLatency_lt_twenty_six hg
  refine ⟨first,by dsimp [first]; linarith,by dsimp [first]; linarith,hle,?_⟩
  rw [pulse.emissions]
  congr 1
  dsimp [first]
  ring

/-- A whole actual train retains its first residual latency, now with the
stronger margins. No output calendar or selected case word is supplied. -/
theorem cadence_high_residual_calendar_sharp_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main i = .ready)
    (hq : 1 / 10 ≤ s.x i .q ∧ s.x i .q ≤ 8 / 25)
    (hgain : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hbrecovery : 37999 / 100000 ≤ s.x i .b)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 19 / 5 ≤ u.time) :
    ∃ first : ℝ, 4 / 25 < first ∧ first < 13 / 50 ∧
      first ≤ highRestLatency (Real.exp (s.x i (.z p))) ∧
      e.emissionTimes i = (s.time + first) :: times.map (fun t => t + highRestLatency (Real.exp (s.x i (.z p)))) := by
  obtain ⟨first,_,_,hle,hem⟩ := cadence_high_residual_calendar_of_valid hb i p times e hf hv hm
    ⟨hq.1,by linarith [hq.2]⟩ hgain hbrecovery ha hr ho hcalendar hspace hquiet
  have hfirst : 4 / 25 < first := by
    cases times with
    | nil =>
      have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
      obtain ⟨pulse⟩ := e.high_gain_pulse_of_valid hb hf.region hv i p hm
        ⟨by linarith [hq.1],by linarith [hq.2]⟩ hgain ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho hn
        (hquiet s.time (by simp))
      obtain ⟨sharp,hsharp,_,_,hsharpem⟩ := pulse.high_residual_calendar_timing hb hf.region p
        (ha p).1 (ha p).2 hq hgain hr ho hn (by linarith [hquiet s.time (by simp)])
      have heq : s.time + first = s.time + sharp := by
        have hh : [s.time + first] = [s.time + sharp] := by
          simpa only [List.map_nil] using hem.symm.trans hsharpem
        exact (List.cons.inj hh).1
      linarith
    | cons next tail =>
      have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: tail.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
      obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
      have hgap : s.time + 19 / 5 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
      obtain ⟨pulse⟩ := cut.span.high_gain_pulse_of_valid hb hf.region hv i p hm
        ⟨by linarith [hq.1],by linarith [hq.2]⟩ hgain ⟨hbrecovery,hf.recovery_cap i⟩ ha hr ho
        cut.no_arrivals_before (by rw [cut.date.1]; exact hgap)
      obtain ⟨sharp,hsharp,_,_,hsharpem⟩ := pulse.high_residual_calendar_timing hb hf.region p
        (ha p).1 (ha p).2 hq hgain hr ho cut.no_arrivals_before (by rw [cut.date.1]; linarith)
      rw [cut.emissions,hsharpem] at hem
      have heq : s.time + sharp = s.time + first := by
        exact (List.cons.inj (by simpa only [List.singleton_append] using hem)).1
      linarith
  exact ⟨first,hfirst,hle.trans_lt (highRestLatency_lt_twenty_six hgain),hle,hem⟩

end KernelR.Hybrid
