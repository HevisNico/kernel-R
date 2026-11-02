import KernelR.HybridRawTailNoFire

/-! The genuine remaining RAW tail after a READY return at0.43. The own
raw gain is bounded more tightly than the generic high-gain ceiling, so the
remaining physical mass stays subthreshold without replacing its origin. -/
namespace KernelR.Hybrid
open Set

theorem raw_scale_after_forty_three_upper {start origin : ℝ}
    (hs : origin + 43 / 100 ≤ start) :
    Real.exp (-a * (start - origin)) ≤ 14 / 25 := by
  have he : Real.exp (-(2967 / 5000 : ℝ)) ≤ 14 / 25 := by
    have h := Real.exp_bound (x := -(2967 / 5000 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  apply le_trans (Real.exp_le_exp.mpr ?_) he
  have ha : (69 / 50 : ℝ) ≤ a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  nlinarith

theorem rawTailMass_full_upper {G start origin time : ℝ} (hG : 0 ≤ G)
    (hs : origin + 43 / 100 ≤ start) (ht : time ≤ origin + 1) :
    rawTailMass G start origin time ≤ 1 / 10 + (31 / 100) * G := by
  have hfirst := raw_scale_after_forty_three_upper hs
  have hlast : 1 / 4 ≤ Real.exp (-a * (time - origin)) := by
    rw [← exp_neg_a]
    apply Real.exp_le_exp.mpr
    nlinarith [a_coarse_bounds.1]
  unfold rawTailMass
  nlinarith

/-- The raw tail up to its actual end remains subthreshold, derived by
contradicting the first physical READY departure. -/
theorem Execution.ready_raw_full_tail_prefix {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (origin G : ℝ) (hm : s.main i = .ready) (hq : s.x i .q = 1 / 10)
    (hG : 0 ≤ G) (hsmall : G < 90 / 31) (hs : origin + 43 / 100 ≤ s.time)
    (hu : u.time ≤ origin + 1)
    (hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - origin)))) :
    e.AllStates (fun v => v.main i = .ready) ∧
      1 / 10 ≤ u.x i .q ∧ u.x i .q ≤ 1 / 10 + (31 / 100) * G := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · have hb := e.ready_raw_tail_mass_upper i (e.allStates_main_flows i .ready h) G s.time origin
      (by rw [hq]) (by simp [rawTailMass,hq]) hd
    exact ⟨h,hb.1,hb.2.trans (rawTailMass_full_upper hG hs hu)⟩
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
    have hbound := hb.2.trans (rawTailMass_full_upper hG hs hvtime)
    rw [hg.1] at hbound
    linarith

structure RawFullTailQuiet {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin G : ℝ) where
  departure : RawDeparture e i p origin
  ready_states : e.AllStates (fun v => v.main i = .ready)
  emissions : e.emissionTimes i = []
  raw_finished : ∀ q, u.raw i q = none
  charge_at_end : 1 / 10 ≤ departure.afterEnd.x i .q ∧
    departure.afterEnd.x i .q ≤ 1 / 10 + (31 / 100) * G
  charge_decay : u.x i .q = 1 / 10 + (departure.afterEnd.x i .q - 1 / 10) *
    Real.exp (-(1 / 2) * (u.time - departure.afterEnd.time))

/-- Select the actual raw-end jump, integrate the whole remaining tail, then
retain the exact zero-current relaxation of its real endpoint charge. -/
theorem Execution.raw_full_tail_no_fire {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin G : ℝ) (hm : s.main i = .ready) (hq : s.x i .q = 1 / 10)
    (hG : 0 ≤ G) (hsmall : G < 90 / 31) (hs : origin + 43 / 100 ≤ s.time)
    (hstart : s.time ≤ origin + 1) (hend : origin + 1 < u.time)
    (hr : s.raw i p = some origin) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hg : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      t ≤ origin + 1 → Real.exp (f.path t i (.z p)) ≤ G)) :
    Nonempty (RawFullTailQuiet e i p origin G) := by
  have hdrive := e.isolated_raw_tail_drive_upper i p origin G hG hr ho hno hg
  obtain ⟨d⟩ := e.raw_end_completion i p origin hr hstart hend
  have hd := hdrive
  rw [d.reconstruct,Execution.allFlows_append] at hd
  have hprefix := d.span.ready_raw_full_tail_prefix i origin G hm hq hG hsmall hs d.date.le hd.1
  have hafter : d.afterEnd.main i = .ready := by
    rw [d.exit.main_unchanged_of_raw_departure i p origin d.raw_before d.raw_after]
    exact d.span.allStates_final hprefix.1
  have hcharge : 1 / 10 ≤ d.afterEnd.x i .q ∧ d.afterEnd.x i .q ≤ 1 / 10 + (31 / 100) * G := by
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
