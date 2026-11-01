import KernelR.HybridMidGainInput
/-! Real first-firing bounds that retain higher gain and READY residual charge. -/
namespace KernelR.Hybrid
open Set

/-- The actual three-to-four-dose gain range fits the high-gain firing bound.
No certificate enclosure membership is assumed. -/
theorem cadence_high_gain_bounds {z : ℝ}
    (hl : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z)
    (hu : z ≤ Real.log (3 / 10) + 12 / 5 + 1 / 100000) :
    9 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 7 / 2 := by
  have hsmall : Real.exp (51 / 100 : ℝ) ≤ 17 / 10 := by
    have h := Real.exp_bound (x := (51 / 100 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hlarge : Real.exp (12 / 5 + 1 / 100000 : ℝ) ≤ 289 / 25 := by
    calc
      _ ≤ Real.exp (a + 51 / 50) := Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])
      _ = 4 * Real.exp (51 / 100 : ℝ) ^ 2 := by
        rw [Real.exp_add,show (51 / 50 : ℝ) = 51 / 100 + 51 / 100 by norm_num,Real.exp_add]
        norm_num [a,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        ring
      _ ≤ _ := by nlinarith [(Real.exp_pos (51 / 100 : ℝ)).le]
  constructor
  · have hlo := (learned_gain_bounds (z := Real.log (3 / 10) + 9 / 5 - 1 / 100000)
      le_rfl (by linarith)).1
    exact hlo.trans (Real.exp_le_exp.mpr hl)
  · have h := Real.exp_le_exp.mpr hu
    rw [show Real.log (3 / 10) + 12 / 5 + 1 / 100000 =
      Real.log (3 / 10) + (12 / 5 + 1 / 100000) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
    linarith

/-- Even a residual charge as large as one half cannot fire before 0.1 when
its physical gain is at most 3.5. This does not reuse the old 0.3 bracket. -/
theorem readyPulse_high_gain_not_early {initial amplitude start t : ℝ}
    (hi : initial ≤ 1 / 2) (ha : amplitude ≤ 7 / 2)
    (ht : start ≤ t) (hu : t ≤ start + 1 / 10) : readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (2 / 5 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (response_upper hd) (by norm_num : (0 : ℝ) ≤ 7 / 2)
  have htime := mul_le_mul_of_nonneg_left (show t - start ≤ (1 / 10 : ℝ) by linarith)
    (show 0 ≤ (7 / 2 : ℝ) * a by linarith [a_coarse_bounds.1])
  unfold readyPulse
  nlinarith [a_coarse_bounds.2]

/-- An actual first departure from READY with a broader, proved time window. -/
structure HighGainTrigger {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  beforeFire : Snapshot n
  afterFire : Snapshot n
  span : Execution θ route s beforeFire
  entry : Jump route beforeFire afterFire
  rest : Execution θ route afterFire u
  reconstruct : e = span.append (.cons (.jump entry) rest)
  ready_states : span.AllStates (fun v => v.main i = .ready)
  fast_after : afterFire.main i = .fast
  charge : afterFire.x i .q = 1
  early : s.time + 1 / 10 < afterFire.time
  deadline : afterFire.time < s.time + 9 / 10

/-- The first firing is forced by the actual positive input and guards, for
q up to 0.5 and gains through 3.5. No firing event or case word is supplied. -/
theorem Execution.high_gain_input_trigger {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 2)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time) (hx : RestBand (s.x i (.m p)))
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) : Nonempty (HighGainTrigger e i) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hdrive := cycle.frozen_drive_upper (7 / 2) (by norm_num) hz.2 hr ho hno
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,entry,rest,he,hstates,hv,hw⟩
  · have hlate := e.ready_learned_no_overrun hb hi i p hr (e.allStates_main_flows i .ready h) hq.1 hz.1
    exact False.elim (by linarith)
  · have hflows := segment.allStates_main_flows i .ready hstates
    have hg := entry.ready_main_departure i hv hw
    have hlate := segment.ready_learned_no_overrun hb hi i p hr hflows hq.1 hz.1
    have hearly : s.time + 1 / 10 < v.time := by
      by_contra h
      have hvtime : v.time ≤ s.time + 1 / 10 := le_of_not_gt h
      have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
      have hbound := hp.all_flows
        (fun {v w} f => ∀ t ∈ Ico v.time w.time, t ≤ s.time + 99 / 100 →
          tailDrive v (f.path t) i t ≤ (7 / 2) * a * Real.exp (-a * (t - s.time)))
        (fun {v w} f {cut} hc hend hf t ht hu => hf t ⟨ht.1,ht.2.trans_le hend⟩ hu) hdrive
      have hd : segment.AllFlows (fun {v' w'} f => ∀ t ∈ Ico v'.time w'.time,
          tailDrive v' (f.path t) i t ≤ (7 / 2) * a * Real.exp (-a * (t - s.time))) := by
        refine segment.allFlows_mono ?_ (segment.allFlows_and hbound segment.allFlows_time_bounds)
        intro v' w' f hf t ht
        exact hf.1 t ht (by have htime := (hf.2 t ⟨ht.1,ht.2.le⟩).2; linarith)
      have hu := segment.ready_drive_upper i hflows (s.x i .q) (7 / 2) s.time
        (by rw [readyPulse_initial]) hd
      have hmodel := readyPulse_high_gain_not_early hq.2 le_rfl segment.time_monotone hvtime
      rw [hg.1] at hu
      exact not_lt_of_ge hu hmodel
    exact ⟨⟨v,w,segment,entry,rest,he,hstates,hg.2,
      by rw [entry.physical_continuous,hg.1],
      by rw [entry.time_unchanged]; exact hearly,
      by rw [entry.time_unchanged]; exact hlate⟩⟩

/-- The selected physical departure contributes exactly one emission and has
no earlier same-cell emission. Later outputs remain explicit in the tail. -/
theorem HighGainTrigger.emission_times {n θ route s u i} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) : e.emissionTimes i = tr.beforeFire.time :: tr.rest.emissionTimes i := by
  have hs := tr.span.allStates_final tr.ready_states
  have hu : tr.afterFire.main i ≠ .ready := by rw [tr.fast_after]; decide
  have hentry := tr.entry.ready_main_departure_emission i hs hu
  have hnone := tr.span.no_emissions_of_ready_states i tr.ready_states
  have hfilter : tr.span.ledger.emissions.filter (fun event => event.1 = i) = [] :=
    List.map_eq_nil_iff.mp hnone
  calc
    e.emissionTimes i = (tr.span.append (.cons (.jump tr.entry) tr.rest)).emissionTimes i :=
      congrArg (fun execution => execution.emissionTimes i) tr.reconstruct
    _ = _ := by
      simp [Execution.emissionTimes,Execution.emissions_append,Execution.ledger,Move.ledger,
        Ledger.add,hentry,hfilter]

/-- The guard equation retains the original residual charge and physical gain.
The upper firing deadline is before ERROR, so gain freezing is derived. -/
theorem HighGainTrigger.firing_equation {n θ route s u i p} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (cycle : SensorCycle e i p) (hr : s.raw i p = some s.time)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q) :
    readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) s.time tr.beforeFire.time = 1 := by
  have hp : e.IsPrefix tr.span :=
    (congrArg (fun actual => actual.IsPrefix tr.span) tr.reconstruct).mpr (.append_left _ _)
  have hdeadline : tr.beforeFire.time < s.time + 9 / 10 := by simpa only [tr.entry.time_unchanged] using tr.deadline
  have hraw := tr.span.raw_active_before i p s.time hr (by linarith)
  have hothers : tr.span.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply tr.span.allFlows_forall (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q; exact tr.span.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
    · exact tr.span.allFlows_mono (fun f hf _ => hf) (tr.span.raw_absent_allFlows i q
        (tr.span.raw_absent_of_no_arrival i q (ho q hq) (hp.no_arrival i q (hno q))).2)
  have hgain := hp.all_flows
    (fun {v w} f => ∀ t ∈ Icc v.time w.time, t ≤ s.time + 99 / 100 → f.path t i (.z p) = s.x i (.z p))
    (fun {v w} f {cut} hc hend hf t ht hu => hf t ⟨ht.1,ht.2.trans hend⟩ hu) cycle.gain_before_error
  have hconst : tr.span.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i (.z p) = s.x i (.z p)) := by
    refine tr.span.allFlows_mono ?_ (tr.span.allFlows_and hgain tr.span.allFlows_time_bounds)
    intro v w f hf t ht
    exact hf.1 t ht (by have h := (hf.2 t ht).2; linarith)
  have hdrive : tr.span.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t = Real.exp (s.x i (.z p)) * a * Real.exp (-a * (t - s.time))) := by
    refine tr.span.allFlows_mono ?_ (tr.span.allFlows_and hraw (tr.span.allFlows_and hothers hconst))
    intro v w f hf t ht
    unfold tailDrive
    rw [Finset.sum_eq_single p]
    · simp only [hf.2.2 t ⟨ht.1,ht.2.le⟩,rawTail,hf.1,mul_assoc]
    · intro q _ hq; simp [rawTail,hf.2.1 q hq]
    · simp
  have hm := tr.span.allStates_main_flows i .ready tr.ready_states
  have hu := tr.span.ready_drive_upper i hm (s.x i .q) (Real.exp (s.x i (.z p))) s.time
    (by rw [readyPulse_initial]) (tr.span.allFlows_mono (fun f hf t ht => (hf t ht).le) hdrive)
  have hl := tr.span.ready_drive_lower i hm (s.x i .q) (Real.exp (s.x i (.z p))) s.time
    (by rw [readyPulse_initial]) (tr.span.allFlows_mono (fun f hf t ht => (hf t ht).ge) hdrive)
  have he := le_antisymm hl hu
  have hq : tr.beforeFire.x i .q = 1 := by simpa only [tr.entry.physical_continuous] using tr.charge
  simpa only [hq] using he

/-- A direct real lower bound at 0.3, for the later high-gain cadence. -/
theorem response_high_gain_deadline : (29 / 100 : ℝ) ≤ response (3 / 10) := by
  have he₁ : (43 / 50 : ℝ) ≤ Real.exp (-(3 / 20 : ℝ)) := by
    have h := Real.exp_bound (x := -(3 / 20 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have he₂ : Real.exp (-(2 / 5 : ℝ)) ≤ 671 / 1000 := by
    have h := Real.exp_bound (x := -(2 / 5 : ℝ)) (n := 5) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have he₃ : Real.exp (-a * (3 / 10)) ≤ Real.exp (-(2 / 5 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    linarith [KernelR.log_four_bounds.1]
  have hd : 0 < a - 1 / 2 := by linarith [a_coarse_bounds.1]
  have hc : (14 / 9 : ℝ) ≤ a / (a - 1 / 2) :=
    (le_div_iff₀ hd).mpr (by linarith [a_coarse_bounds.2])
  have he : (189 / 1000 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ) * (3 / 10)) - Real.exp (-a * (3 / 10)) := by
    norm_num only [show -(1 / 2 : ℝ) * (3 / 10) = -(3 / 20) by norm_num]
    linarith
  have h := mul_le_mul hc he (by norm_num : (0 : ℝ) ≤ 189 / 1000)
    (div_pos (by linarith [a_coarse_bounds.1]) hd).le
  change _ ≤ response (3 / 10) at h
  linarith

theorem readyPulse_high_gain_by_deadline {initial amplitude start : ℝ}
    (hi : 1 / 10 - 1 / 100000 ≤ initial) (ha : 16 / 5 ≤ amplitude) :
    1 < readyPulse initial amplitude start (start + 3 / 10) := by
  have he : Real.exp (-(1 / 2 : ℝ) * (3 / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hcarry : -(1 / 100000 : ℝ) ≤ (initial - 1 / 10) * Real.exp (-(1 / 2) * (3 / 10)) := by
    have h := mul_le_mul_of_nonneg_right (show -(1 / 100000 : ℝ) ≤ initial - 1 / 10 by linarith)
      (Real.exp_pos (-(1 / 2 : ℝ) * (3 / 10))).le
    nlinarith
  have hp := mul_le_mul_of_nonneg_left response_high_gain_deadline (show 0 ≤ amplitude by linarith)
  simp only [readyPulse, add_sub_cancel_left]
  nlinarith

/-- A READY execution with this physical input cannot persist through 0.3. -/
theorem Execution.ready_high_gain_no_overrun {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hr : s.raw i p = some s.time) (hm : e.MainFlows i .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q) (hz : 16 / 5 ≤ Real.exp (s.x i (.z p))) :
    u.time < s.time + 3 / 10 := by
  by_contra hlate
  obtain ⟨v,cut,hcut,hv⟩ := e.prefix_at (s.time + 3 / 10) (by linarith) (le_of_not_gt hlate)
  have hraw := cut.raw_active_before i p s.time hr (by rw [hv]; linarith)
  have hgain := cut.gain_flow_lower hb i p
  have hd : cut.AllFlows (fun {w z} f => ∀ t ∈ Ico w.time z.time,
      Real.exp (s.x i (.z p)) * a * Real.exp (-a * (t - s.time)) ≤ tailDrive w (f.path t) i t) := by
    refine cut.allFlows_mono ?_ (cut.allFlows_and hraw hgain)
    intro w z f hf t ht
    have hsingle : Real.exp (f.path t i (.z p)) * rawTail w i p t ≤ tailDrive w (f.path t) i t := by
      unfold tailDrive
      exact Finset.single_le_sum (fun q _ => mul_nonneg (Real.exp_pos (f.path t i (.z q))).le
        (rawTail_nonnegative w i q t)) (Finset.mem_univ p)
    have hmono := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hf.2 t ⟨ht.1,ht.2.le⟩))
      (rawTail_nonnegative w i p t)
    simpa only [rawTail,hf.1,mul_assoc] using hmono.trans hsingle
  have hl := cut.ready_drive_lower i (hcut.main_flows i .ready hm) (s.x i .q)
    (Real.exp (s.x i (.z p))) s.time (by rw [readyPulse_initial]) hd
  have hu := (cut.upper_region hb hi i).2.1
  have hc := readyPulse_high_gain_by_deadline (start := s.time) hq hz
  rw [hv] at hl
  linarith

/-- The actual selected first firing satisfies the sharper high-gain deadline. -/
theorem HighGainTrigger.high_gain_deadline {n θ ε route s u i} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s) (p : Port)
    (hr : s.raw i p = some s.time) (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q)
    (hz : 16 / 5 ≤ Real.exp (s.x i (.z p))) : tr.afterFire.time < s.time + 3 / 10 := by
  rw [tr.entry.time_unchanged]
  exact tr.span.ready_high_gain_no_overrun hb hi i p hr
    (tr.span.allStates_main_flows i .ready tr.ready_states) hq hz

/-- Four actual ERROR doses put the original nominal weak gain above 3.2. -/
theorem cadence_four_dose_gain_lower {z : ℝ}
    (hl : Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤ z) : 16 / 5 ≤ Real.exp z := by
  have hlo : (32 / 3 : ℝ) ≤ Real.exp (12 / 5 - 1 / 100000) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12 / 5 - 1 / 100000) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have h := Real.exp_le_exp.mpr hl
  rw [show Real.log (3 / 10) + 12 / 5 - 1 / 100000 =
    Real.log (3 / 10) + (12 / 5 - 1 / 100000) by ring,
    Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
  linarith

end KernelR.Hybrid
