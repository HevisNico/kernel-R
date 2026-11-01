import KernelR.HybridResidualLatency

/-! A remaining physical raw tail cannot cause a second firing after a late
READY reopening. Its original date and actual residual charge are retained. -/
namespace KernelR.Hybrid
open Set

/-- An isolated READY charge strictly below threshold remains below threshold
under its exact zero-current relaxation, even when it exceeds the rest value. -/
theorem Execution.ready_without_input_subthreshold {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .ready) (hx : s.x i .q < 1)
    (hr : ∀ p, s.raw i p = none) (hno : ∀ p, NoArrivalAt e i p) :
    e.AllStates (fun v => v.main i = .ready) := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hraw : ∀ p, segment.RawAbsent i p := fun p =>
      (segment.raw_absent_of_no_arrival i p (hr p) (hp.no_arrival i p (hno p))).2
    have hsol := segment.ready_no_current_solution i (segment.allStates_main_flows i .ready hstates) hraw
    have hg := exit.ready_main_departure i hv hw
    have hdecay : Real.exp (-(1 / 2 : ℝ) * (v.time - s.time)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [segment.time_monotone])
    have hbound : 1 / 10 + (s.x i .q - 1 / 10) *
        Real.exp (-(1 / 2 : ℝ) * (v.time - s.time)) < 1 := by
      by_cases hq : s.x i .q ≤ 1 / 10
      · have hm := mul_nonpos_of_nonpos_of_nonneg (show s.x i .q - 1 / 10 ≤ 0 by linarith)
          (Real.exp_pos (-(1 / 2 : ℝ) * (v.time - s.time))).le
        linarith
      · have hm := mul_le_mul_of_nonneg_left hdecay (show 0 ≤ s.x i .q - 1 / 10 by linarith)
        linarith
    rw [hg.1] at hsol
    linarith

noncomputable def rawTailMass (G start origin t : ℝ) : ℝ :=
  1 / 10 + G * (Real.exp (-a * (start - origin)) - Real.exp (-a * (t - origin)))

theorem rawTailMass_derivative (G start origin t : ℝ) :
    HasDerivAt (rawTailMass G start origin) (G * a * Real.exp (-a * (t - origin))) t := by
  have h := (((((hasDerivAt_id t).sub_const origin).const_mul (-a)).exp).const_sub
    (Real.exp (-a * (start - origin)))).const_mul G
  exact (h.const_add (1 / 10)).congr_deriv (by simp only [id_eq]; ring)

theorem rawTailMass_upper {G start origin t : ℝ} (hG : 0 ≤ G)
    (hs : origin + 1 / 2 ≤ start) (ht : t ≤ origin + 1) :
    rawTailMass G start origin t ≤ 1 / 10 + G / 4 := by
  have hhalf : Real.exp (-a * (1 / 2 : ℝ)) = 1 / 2 := by
    have hsq : Real.exp (-a * (1 / 2 : ℝ)) ^ 2 = 1 / 4 := by
      rw [pow_two,← Real.exp_add,show -a * (1 / 2 : ℝ) + -a * (1 / 2) = -a by ring,exp_neg_a]
    nlinarith [Real.exp_pos (-a * (1 / 2 : ℝ))]
  have hfirst : Real.exp (-a * (start - origin)) ≤ 1 / 2 := by
    rw [← hhalf]
    apply Real.exp_le_exp.mpr
    nlinarith [a_coarse_bounds.1]
  have hlast : 1 / 4 ≤ Real.exp (-a * (t - origin)) := by
    rw [← exp_neg_a]
    apply Real.exp_le_exp.mpr
    nlinarith [a_coarse_bounds.1]
  unfold rawTailMass
  nlinarith

/-- Once the READY charge is at least its rest value, dropping its nonpositive
leak gives a valid upper comparison against the remaining raw mass. -/
theorem Flow.ready_raw_tail_mass_upper {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hm : s.main i = .ready) (G start origin : ℝ)
    (hlo : 1 / 10 ≤ s.x i .q) (hup : s.x i .q ≤ rawTailMass G start origin s.time)
    (hd : ∀ t ∈ Ico s.time u.time,
      tailDrive s (f.path t) i t ≤ G * a * Real.exp (-a * (t - origin))) :
    ∀ t ∈ Icc s.time u.time,
      1 / 10 ≤ f.path t i .q ∧ f.path t i .q ≤ rawTailMass G start origin t := by
  have hnon : ∀ t ∈ Ico s.time u.time,
      (0 : ℝ) * a * Real.exp (-a * (t - s.time)) ≤ tailDrive s (f.path t) i t := by
    intro t ht
    simp only [zero_mul]
    unfold tailDrive
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (rawTail_nonnegative s i p t))
  have hlower := f.ready_drive_lower i hm (1 / 10) 0 s.time (by simpa only [readyPulse_initial] using hlo) hnon
  simp only [readyPulse,sub_self,zero_mul,add_zero] at hlower
  have hupper : ∀ t ∈ Icc s.time u.time, f.path t i .q ≤ rawTailMass G start origin t := by
    apply linear_comparison_of_right_derivatives (rate := 0)
      (lower := fun t => (1 / 2) * (1 / 10 - f.path t i .q) + tailDrive s (f.path t) i t)
      (upper := fun t => G * a * Real.exp (-a * (t - origin)))
      (f.continuous i .q)
      (fun t _ => (rawTailMass_derivative G start origin t).continuousAt.continuousWithinAt)
      (fun t ht => (f.ready_right_derivative i hm t ht).congr_deriv (by ring))
      (fun t _ => (rawTailMass_derivative G start origin t).hasDerivWithinAt.congr_deriv (by ring))
      (by simpa only [f.initial] using hup)
    intro t ht
    have hl := hlower t ⟨ht.1,ht.2.le⟩
    linarith [hd t ht]
  exact fun t ht => ⟨hlower t ht,hupper t ht⟩

theorem Execution.ready_raw_tail_mass_upper {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) (G start origin : ℝ)
    (hlo : 1 / 10 ≤ s.x i .q) (hup : s.x i .q ≤ rawTailMass G start origin s.time)
    (hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - origin)))) :
    1 / 10 ≤ u.x i .q ∧ u.x i .q ≤ rawTailMass G start origin u.time := by
  induction e with
  | nil => exact ⟨hlo,hup⟩
  | cons move rest ih => cases move with
    | flow f =>
      have hf := f.ready_raw_tail_mass_upper i hm.1 G start origin hlo hup hd.1
        _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hf
      exact ih hm.2 hf.1 hf.2 hd.2
    | jump j =>
      exact ih hm (by simpa only [j.physical_continuous] using hlo)
        (by simpa only [j.physical_continuous,j.time_unchanged] using hup) hd

/-- A real upper bound on the possibly changing gain is sufficient. No
constancy or absence of ERROR is assumed. -/
theorem Execution.isolated_raw_tail_drive_upper {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin G : ℝ) (hG : 0 ≤ G)
    (hr : s.raw i p = some origin) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hg : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      t ≤ origin + 1 → Real.exp (f.path t i (.z p)) ≤ G)) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - origin))) := by
  have hraw := (e.raw_allowed_of_no_arrival i p origin (Or.inr hr) (hno p)).2
  have hothers : e.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply e.allFlows_forall (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q; exact e.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
    · exact e.allFlows_mono (fun f hf _ => hf)
        (e.raw_absent_allFlows i q (e.raw_absent_of_no_arrival i q (ho q hq) (hno q)).2)
  refine e.allFlows_mono ?_ (e.allFlows_and hraw (e.allFlows_and hothers hg))
  intro v w f hf t ht
  have hsum : tailDrive v (f.path t) i t = Real.exp (f.path t i (.z p)) * rawTail v i p t := by
    unfold tailDrive
    apply Finset.sum_eq_single p
    · intro q _ hq; simp [rawTail,hf.2.1 q hq]
    · simp
  rw [hsum]
  rcases hf.1 with hn | hr
  · simp only [rawTail,hn,mul_zero]
    exact mul_nonneg (mul_nonneg hG (by linarith [a_coarse_bounds.1])) (Real.exp_pos _).le
  · have hend := (f.raw_support i p origin hr).2
    have hex := hf.2.2 t ht (ht.2.le.trans hend)
    simpa only [rawTail,hr,mul_assoc] using mul_le_mul_of_nonneg_right hex (rawTail_nonnegative v i p t)

/-- The raw tail up to its actual end remains subthreshold, derived by
contradicting the first physical READY departure. -/
theorem Execution.ready_raw_tail_prefix {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (origin G : ℝ) (hm : s.main i = .ready) (hq : s.x i .q = 1 / 10)
    (hG : 0 ≤ G) (hsmall : G < 18 / 5) (hs : origin + 1 / 2 ≤ s.time)
    (hu : u.time ≤ origin + 1)
    (hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - origin)))) :
    e.AllStates (fun v => v.main i = .ready) ∧
      1 / 10 ≤ u.x i .q ∧ u.x i .q ≤ 1 / 10 + G / 4 := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · have hb := e.ready_raw_tail_mass_upper i (e.allStates_main_flows i .ready h) G s.time origin
      (by rw [hq]) (by simp [rawTailMass,hq]) hd
    exact ⟨h,hb.1,hb.2.trans (rawTailMass_upper hG hs hu)⟩
  · have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hdrive := hp.all_flows
      (fun {v w} f => ∀ t ∈ Ico v.time w.time,
        tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - origin)))
      (fun {v w} f {cut} hc hend hf t ht => hf t ⟨ht.1,ht.2.trans_le hend⟩) hd
    have hb := segment.ready_raw_tail_mass_upper i (segment.allStates_main_flows i .ready hstates)
      G s.time origin (by rw [hq]) (by simp [rawTailMass,hq]) hdrive
    have hg := exit.ready_main_departure i hv hw
    have hvtime : v.time ≤ origin + 1 := by
      rw [← exit.time_unchanged]
      exact rest.time_monotone.trans hu
    have hbound := hb.2.trans (rawTailMass_upper hG hs hvtime)
    rw [hg.1] at hbound
    linarith

/-- A genuine raw departure changes no main mode. -/
theorem Jump.main_unchanged_of_raw_departure {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : s.raw i p = some origin)
    (ha : u.raw i p = none) : u.main = s.main := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

structure RawTailQuiet {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin G : ℝ) where
  departure : RawDeparture e i p origin
  ready_states : e.AllStates (fun v => v.main i = .ready)
  emissions : e.emissionTimes i = []
  raw_finished : ∀ q, u.raw i q = none
  charge_at_end : 1 / 10 ≤ departure.afterEnd.x i .q ∧
    departure.afterEnd.x i .q ≤ 1 / 10 + G / 4
  charge_decay : u.x i .q = 1 / 10 + (departure.afterEnd.x i .q - 1 / 10) *
    Real.exp (-(1 / 2) * (u.time - departure.afterEnd.time))

/-- Select the actual raw-end jump, integrate the whole remaining tail, then
retain the exact zero-current relaxation of its real endpoint charge. -/
theorem Execution.raw_tail_no_fire {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin G : ℝ) (hm : s.main i = .ready) (hq : s.x i .q = 1 / 10)
    (hG : 0 ≤ G) (hsmall : G < 18 / 5) (hs : origin + 1 / 2 ≤ s.time)
    (hstart : s.time ≤ origin + 1) (hend : origin + 1 < u.time)
    (hr : s.raw i p = some origin) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hg : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      t ≤ origin + 1 → Real.exp (f.path t i (.z p)) ≤ G)) :
    Nonempty (RawTailQuiet e i p origin G) := by
  have hdrive := e.isolated_raw_tail_drive_upper i p origin G hG hr ho hno hg
  obtain ⟨d⟩ := e.raw_end_completion i p origin hr hstart hend
  have hd := hdrive
  rw [d.reconstruct,Execution.allFlows_append] at hd
  have hprefix := d.span.ready_raw_tail_prefix i origin G hm hq hG hsmall hs d.date.le hd.1
  have hafter : d.afterEnd.main i = .ready := by
    rw [d.exit.main_unchanged_of_raw_departure i p origin d.raw_before d.raw_after]
    exact d.span.allStates_final hprefix.1
  have hcharge : 1 / 10 ≤ d.afterEnd.x i .q ∧ d.afterEnd.x i .q ≤ 1 / 10 + G / 4 := by
    simpa only [d.exit.physical_continuous] using hprefix.2
  have hnoRest : ∀ q, NoArrivalAt d.rest i q := by
    intro q
    have h := hno q
    rw [d.reconstruct,Execution.noArrivalAt_append] at h
    exact fun v hv => h.2 v (List.mem_append_right _ hv)
  have hrawAfter : ∀ q, d.afterEnd.raw i q = none := by
    intro q
    by_cases hq : q = p
    · subst q; exact d.raw_after
    · have h := e.raw_none_states i q (ho q hq) (hno q)
      rw [d.reconstruct,Execution.allStates_append] at h
      exact d.rest.allStates_initial h.2.2
  have hquiet := d.rest.ready_without_input_subthreshold i hafter (by linarith [hcharge.2]) hrawAfter hnoRest
  have hraw : ∀ q, d.rest.RawAbsent i q := fun q =>
    (d.rest.raw_absent_of_no_arrival i q (hrawAfter q) (hnoRest q)).2
  have hstates : e.AllStates (fun v => v.main i = .ready) := by
    rw [d.reconstruct,Execution.allStates_append]
    exact ⟨hprefix.1,d.span.allStates_final hprefix.1,hquiet⟩
  refine ⟨⟨d,hstates,e.no_emissions_of_ready_states i hstates,
    fun q => (d.rest.raw_absent_of_no_arrival i q (hrawAfter q) (hnoRest q)).1,hcharge,?_⟩⟩
  exact d.rest.ready_no_current_solution i (d.rest.allStates_main_flows i .ready hquiet) hraw

end KernelR.Hybrid
