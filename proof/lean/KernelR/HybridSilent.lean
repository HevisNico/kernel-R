import KernelR.HybridMainComparison
import KernelR.HybridMainBounds
import KernelR.HybridSensorGain

/-! An isolated low-gain pulse has no actual main emissions and receives a full ERROR dose from reachable states. -/
namespace KernelR.Hybrid
open Set MeasureTheory


theorem Jump.ready_main_departure {n route s u} (j : @Jump n route s u) (i : Fin n)
    (hs : s.main i = .ready) (hu : u.main i ≠ .ready) :
    s.x i .q = 1 ∧ u.main i = .fast := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]

/-- The actual raw tags and late ERROR onset bound the input to the main
coordinate. No upper bound is needed on gains of inactive ports. -/
theorem SensorCycle.low_gain_drive_upper {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε)
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + 6 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ (7 / 6) * a * Real.exp (-a * (t - s.time))) := by
  have hraw := (e.raw_allowed_of_no_arrival i p s.time (Or.inr hr) (hno p)).2
  have hothers : e.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply e.allFlows_forall
      (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q
      exact e.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
    · have h := e.raw_absent_allFlows i q (e.raw_absent_of_no_arrival i q (ho q hq) (hno q)).2
      exact e.allFlows_mono (fun f hf _ => hf) h
  have hgain := cycle.gain_during_raw hb
  have h := e.allFlows_and hraw (e.allFlows_and hothers hgain)
  refine e.allFlows_mono ?_ h
  intro v w f hf t ht
  have hsum : tailDrive v (f.path t) i t = Real.exp (f.path t i (.z p)) * rawTail v i p t := by
    unfold tailDrive
    apply Finset.sum_eq_single p
    · intro q _ hq; simp [rawTail, hf.2.1 q hq]
    · simp
  rw [hsum]
  rcases hf.1 with hn | hr
  · simp only [rawTail, hn, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [a_coarse_bounds.1])) (Real.exp_pos _).le
  · have hend := (f.raw_support i p s.time hr).2
    have hzt := hf.2.2 t ⟨ht.1, ht.2.le⟩ (ht.2.le.trans hend)
    have hg : Real.exp (f.path t i (.z p)) ≤ 7 / 6 :=
      low_gain_tail_upper (by linarith)
    simpa only [rawTail, hr, mul_assoc] using
      mul_le_mul_of_nonneg_right hg (rawTail_nonnegative v i p t)

/-- An isolated low-gain input cannot cause a main firing. The READY trace is
derived by selecting and excluding its first possible physical departure. -/
theorem Execution.silent_input {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready) (hq : s.x i .q ≤ 3 / 25)
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + 6 / 5 + 1 / 100000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) :
    e.AllStates (fun v => v.main i = .ready) ∧ e.emissionTimes i = [] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hdrive := cycle.low_gain_drive_upper hb hz hr ho hno
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact ⟨h,e.no_emissions_of_ready_states i h⟩
  · have hguard := exit.ready_main_departure i hv hw
    have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hd := hp.all_flows
      (fun {v w} f => ∀ t ∈ Ico v.time w.time,
        tailDrive v (f.path t) i t ≤ (7 / 6) * a * Real.exp (-a * (t - s.time)))
      (fun {v w} f {cut} hc hend hf t ht => hf t ⟨ht.1, ht.2.trans_le hend⟩) hdrive
    have hu := segment.ready_drive_upper i (segment.allStates_main_flows i .ready hstates) (s.x i .q) (7 / 6) s.time
      (by rw [readyPulse_initial]) hd
    have hmodel := readyPulse_silent_window hq (le_refl (7 / 6 : ℝ)) segment.time_monotone
    rw [hguard.1] at hu
    exact False.elim (not_lt_of_ge hu hmodel)

theorem Execution.deliveries_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u) :
    (segment.append rest).deliveries = segment.deliveries ++ rest.deliveries := by
  induction segment with
  | nil => rfl
  | cons move tail ih => simp only [append,deliveries,ih,List.append_assoc]

theorem Execution.noArrivalAt_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u) (i : Fin n) (p : Port) :
    NoArrivalAt (segment.append rest) i p ↔ NoArrivalAt segment i p ∧ NoArrivalAt rest i p := by
  simp only [NoArrivalAt,deliveries_append,List.mem_append,or_imp,forall_and]

theorem Execution.IsPrefix.no_arrival {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (hcut : e.IsPrefix cut) (i : Fin n) (p : Port)
    (hno : NoArrivalAt e i p) : NoArrivalAt cut i p := by
  induction hcut with
  | nil => simp [NoArrivalAt,deliveries]
  | flowCut f rest ht hend => simp [NoArrivalAt,deliveries,Move.deliveries]
  | step move rest cut hcut ih =>
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact hno d (List.mem_append_left _ h)
    · exact ih (fun d hd => hno d (List.mem_append_right _ hd)) d h

theorem Execution.aux_ready_no_current_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hm : e.AuxFlows i p .ready) (hr : e.RawAbsent i p) :
    u.x i (.m p) = 1 / 40 + (s.x i (.m p) - 1 / 40) * Real.exp (-(1 / 2) * (u.time - s.time)) := by
  induction e with
  | nil => simp
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hrest := ih hm.2 hr.2
      have hflow := f.aux_ready_no_current_solution i p hm.1 hr.1 _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hflow
      rw [hrest,hflow]
      have he := attenuation_split (1 / 2) s.time v.time u.time
      linear_combination (s.x i (.m p) - 1 / 40) * he
    | jump j => simpa only [j.physical_continuous,j.time_unchanged] using ih hm hr

/-- A READY sensor at or below rest cannot trigger without a new arrival. -/
theorem Execution.aux_ready_without_input {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hs : s.aux i p = .ready) (hx : s.x i (.m p) ≤ 1 / 40)
    (hr : s.raw i p = none) (hno : NoArrivalAt e i p) :
    e.AllStates (fun v => v.aux i p = .ready) := by
  rcases e.first_state_change (fun v => v.aux i p) .ready
    (fun f => congrFun (congrFun f.aux_fixed i) p) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hraw := (segment.raw_absent_of_no_arrival i p hr (hp.no_arrival i p hno)).2
    have hsol := segment.aux_ready_no_current_solution i p (segment.allStates_aux_flows i p .ready hstates) hraw
    have hg := exit.ready_aux_departure i p hv hw
    have hdecay : (s.x i (.m p) - 1 / 40) * Real.exp (-(1 / 2) * (v.time - s.time)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    rw [hg.1] at hsol
    linarith
theorem SensorCycle.error_states {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) {P : Snapshot n → Prop} (h : e.AllStates P) :
    cycle.phases.errorPhase.span.AllStates P ∧ cycle.phases.errorPhase.rest.AllStates P := by
  rw [cycle.trigger.reconstruct,Execution.allStates_append] at h
  have hmk := h.2.2
  rw [cycle.phases.markPhase.reconstruct,Execution.allStates_append] at hmk
  have hsi := hmk.2.2
  rw [cycle.phases.silentPhase.reconstruct,Execution.allStates_append] at hsi
  have her := hsi.2.2
  rw [cycle.phases.errorPhase.reconstruct,Execution.allStates_append] at her
  exact ⟨her.1,her.2.2⟩

theorem SensorCycle.error_initial_gain {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) : cycle.phases.silentPhase.afterExit.x i (.z p) = s.x i (.z p) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  have htr := tr.span.gain_constant_aux i p .ready (by decide) tr.flows
  have hmk := mk.span.gain_constant_aux i p .mark (by decide) mk.flows
  have hsi := si.span.gain_constant_aux i p .silent (by decide) si.flows
  change si.afterExit.x i (.z p) = _
  rw [si.exit.physical_continuous,hsi.1,mk.exit.physical_continuous,hmk.1,
    tr.entry.physical_continuous,htr.1]

/-- Reserve and headroom are derived from the actual reachable trace. A silent
main cell therefore receives one full ERROR dose in its extracted sensor cycle. -/
theorem SensorCycle.error_dose_when_ready {n θ ε route born s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + 6 / 5 + 1 / 100000) :
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
  have hh : si.afterExit.x i (.z p) + 8 * (si.afterExit.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p) := by
    rw [cycle.error_initial_gain,si.after_charge]
    norm_num only [protectedFloor]
    linarith [hb.low_gain_headroom i p]
  have ho := er.span.error_exposed_of_headroom pastError hborn hb i p er.flows hmain hh
  have hd := er.span.full_error_of_open_endpoints i p ho
    (by change si.afterExit.x i (.m p) = 1 / 10; simpa only [protectedFloor] using si.after_charge)
    (by simpa only [protectedFloor] using er.charge)
  refine ⟨hd,?_⟩
  change er.afterExit.x i (.z p) = _
  rw [er.exit.physical_continuous,er.span.gain_balance i p,hd,cycle.error_initial_gain]

theorem SensorCycle.error_rest_no_arrival {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (q : Port) (h : NoArrivalAt e i q) :
    NoArrivalAt cycle.phases.errorPhase.rest i q := by
  rw [cycle.trigger.reconstruct,Execution.noArrivalAt_append] at h
  have hmk : NoArrivalAt cycle.trigger.rest i q := fun d hd => h.2 d (List.mem_append_right _ hd)
  rw [cycle.phases.markPhase.reconstruct,Execution.noArrivalAt_append] at hmk
  have hsi : NoArrivalAt cycle.phases.markPhase.rest i q := fun d hd => hmk.2 d (List.mem_append_right _ hd)
  rw [cycle.phases.silentPhase.reconstruct,Execution.noArrivalAt_append] at hsi
  have her : NoArrivalAt cycle.phases.silentPhase.rest i q := fun d hd => hsi.2 d (List.mem_append_right _ hd)
  rw [cycle.phases.errorPhase.reconstruct,Execution.noArrivalAt_append] at her
  exact fun d hd => her.2 d (List.mem_append_right _ hd)

/-- No later input means that the sensor stays at rest after the extracted
cycle. Consequently the total dose, not merely its ERROR subspan, is 3/5. -/
theorem SensorCycle.total_error_dose_when_ready {n θ ε route born s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + 6 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    e.ledger.error i p = 3 / 5 ∧ u.x i (.z p) = s.x i (.z p) + 3 / 5 := by
  let er := cycle.phases.errorPhase
  have hvalid := e.allStates_raw_valid (past.raw_valid hborn.raw_valid)
  have hallowed := e.raw_allowed_states i p s.time (Or.inr hr) hno
  have hv := er.rest.allStates_initial (cycle.error_states hvalid).2
  have ha := er.rest.allStates_initial (cycle.error_states hallowed).2
  have hraw : er.afterExit.raw i p = none := by
    rcases ha with h | h
    · exact h
    · exact False.elim (not_lt_of_ge (hv i p s.time h).2 cycle.ready_after_raw)
  have hquiet := er.rest.aux_ready_without_input i p cycle.phases.ready_mode
    (by simpa only [protectedFloor] using er.after_charge.le) hraw (cycle.error_rest_no_arrival p hno)
  have hgain := (er.rest.gain_constant_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready hquiet)).1
  have hd := cycle.error_dose_when_ready past hborn hb hm hz
  have hu : u.x i (.z p) = s.x i (.z p) + 3 / 5 := hgain.trans hd.2
  refine ⟨?_,hu⟩
  have hb := e.gain_balance i p
  linarith

theorem Execution.recovery_constant_ready {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) : u.x i .b = s.x i .b := by
  induction e with
  | nil => rfl
  | cons move rest ih => cases move with
    | flow f =>
      have hf := f.recovery_constant_when_ready i hm.1 _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hf
      exact (ih hm.2).trans hf
    | jump j => simpa only [j.physical_continuous] using ih hm

/-- The silent pulse case derives no emission, a total ERROR dose of 3/5,
the corresponding actual log-gain increase, and unchanged recovery. -/
theorem Execution.silent_input_dose {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hm : s.main i = .ready) (hq : s.x i .q ≤ 3 / 25)
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + 6 / 5 + 1 / 100000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) :
    e.emissionTimes i = [] ∧ e.ledger.error i p = 3 / 5 ∧
      u.x i (.z p) = s.x i (.z p) + 3 / 5 ∧ u.x i .b = s.x i .b := by
  have hi := past.upper_region hb hborn.upper_region
  have hsilent := e.silent_input hb hi i p hm hq hz ha hr hx ho hno ht
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hd := cycle.total_error_dose_when_ready past hborn hb hsilent.1 hz hr (hno p)
  exact ⟨hsilent.2,hd.1,hd.2,e.recovery_constant_ready i (e.allStates_main_flows i .ready hsilent.1)⟩

end KernelR.Hybrid
