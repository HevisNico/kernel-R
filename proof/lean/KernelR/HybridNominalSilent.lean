import KernelR.HybridPulseBounds
import KernelR.HybridPulseSection

/-! The silent input case at arbitrary reachable recovery, including the nominal fast gain. -/
namespace KernelR.Hybrid
open Set

theorem SensorCycle.single_drive_upper {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (G : ℝ) (hG : 0 ≤ G)
    (hg : ∀ z, z ≤ s.x i (.z p) + 11 / 125 → Real.exp z ≤ G)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - s.time))) := by
  have hraw := (e.raw_allowed_of_no_arrival i p s.time (Or.inr hr) (hno p)).2
  have hothers : e.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply e.allFlows_forall (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q; exact e.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
    · exact e.allFlows_mono (fun f hf _ => hf)
        (e.raw_absent_allFlows i q (e.raw_absent_of_no_arrival i q (ho q hq) (hno q)).2)
  refine e.allFlows_mono ?_ (e.allFlows_and hraw (e.allFlows_and hothers (cycle.gain_during_raw hb)))
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
  · have hend := (f.raw_support i p s.time hr).2
    have hbound := hf.2.2 t ⟨ht.1,ht.2.le⟩ (ht.2.le.trans hend)
    have hex := hg (f.path t i (.z p)) hbound
    simpa only [rawTail,hr,mul_assoc] using mul_le_mul_of_nonneg_right hex (rawTail_nonnegative v i p t)

theorem Execution.ready_of_upper_drive {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .ready) (G : ℝ)
    (hdrive : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - s.time))))
    (hmodel : ∀ t, s.time ≤ t → readyPulse (s.x i .q) G s.time t < 1) :
    e.AllStates (fun v => v.main i = .ready) ∧ e.emissionTimes i = [] := by
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact ⟨h,e.no_emissions_of_ready_states i h⟩
  · have hg := exit.ready_main_departure i hv hw
    have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hd := hp.all_flows
      (fun {v w} f => ∀ t ∈ Ico v.time w.time,
        tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - s.time)))
      (fun {v w} f {cut} hc hend hf t ht => hf t ⟨ht.1,ht.2.trans_le hend⟩) hdrive
    have hu := segment.ready_drive_upper i (segment.allStates_main_flows i .ready hstates)
      (s.x i .q) G s.time (by rw [readyPulse_initial]) hd
    have hm := hmodel v.time segment.time_monotone
    rw [hg.1] at hu
    exact False.elim (not_lt_of_ge hu hm)

/-- The silent READY case includes both low-port training gains and the
nominal fast gain, with a uniform section radius covering small birth residue. -/
theorem Execution.nominal_silent_input {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready) (hq : s.x i .q ≤ 7 / 50)
    (hz : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) :
    e.AllStates (fun v => v.main i = .ready) ∧ e.emissionTimes i = [] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hdrive := cycle.single_drive_upper hb (4 / 3) (by norm_num)
    (fun z hz' => fast_nominal_raw_gain_upper (by linarith)) hr ho hno
  exact e.ready_of_upper_drive i hm (4 / 3) hdrive
    (fun t ht => readyPulse_nominal_silent hq le_rfl ht)

theorem SensorCycle.error_dose_of_headroom {n θ ε route born s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p)) :
    cycle.phases.errorPhase.span.ledger.error i p = 3 / 5 ∧
      cycle.phases.errorPhase.afterExit.x i (.z p) = s.x i (.z p) + 3 / 5 := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  let pastMark := past.append (tr.span.append (.cons (.jump tr.entry) (.nil _)))
  let pastSilent := pastMark.append (mk.span.append (.cons (.jump mk.exit) (.nil _)))
  let pastError := pastSilent.append (si.span.append (.cons (.jump si.exit) (.nil _)))
  have hmain := er.span.allStates_main_flows i .ready (cycle.error_states hm).1
  have hh' : si.afterExit.x i (.z p) + 8 * (si.afterExit.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p) := by
    rw [cycle.error_initial_gain,si.after_charge]
    norm_num only [protectedFloor]
    linarith
  have ho := er.span.error_exposed_of_headroom pastError hborn hb i p er.flows hmain hh'
  have hd := er.span.full_error_of_open_endpoints i p ho
    (by change si.afterExit.x i (.m p) = 1 / 10; simpa only [protectedFloor] using si.after_charge)
    (by simpa only [protectedFloor] using er.charge)
  refine ⟨hd,?_⟩
  change er.afterExit.x i (.z p) = _
  rw [er.exit.physical_continuous,er.span.gain_balance i p,hd,cycle.error_initial_gain]

theorem SensorCycle.total_error_of_headroom {n θ ε route born s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p))
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    e.ledger.error i p = 3 / 5 ∧ u.x i (.z p) = s.x i (.z p) + 3 / 5 := by
  let er := cycle.phases.errorPhase
  have hd := cycle.error_dose_of_headroom past hborn hb hm hh
  have hready := cycle.error_rest_ready (past.raw_valid hborn.raw_valid) hr hno
  have hgain := (er.rest.gain_constant_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready hready)).1
  have hu : u.x i (.z p) = s.x i (.z p) + 3 / 5 := hgain.trans hd.2
  refine ⟨?_,hu⟩
  have h := e.gain_balance i p
  linarith

theorem Execution.nominal_silent_dose {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.main i = .ready) (hq : s.x i .q ≤ 7 / 50)
    (hz : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) :
    e.emissionTimes i = [] ∧ e.ledger.error i p = 3 / 5 ∧
      u.x i (.z p) = s.x i (.z p) + 3 / 5 ∧ u.x i .b = s.x i .b := by
  have hi := past.upper_region hb hborn.upper_region
  have hsilent := e.nominal_silent_input hb hi i p hm hq hz ha hr hx ho hno ht
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p) :=
    lt_of_le_of_lt (by linarith) (hb.fast_nominal_headroom i p)
  have hd := cycle.total_error_of_headroom past hborn hb hsilent.1 hh hr (hno p)
  exact ⟨hsilent.2,hd.1,hd.2,e.recovery_constant_ready i (e.allStates_main_flows i .ready hsilent.1)⟩

end KernelR.Hybrid
