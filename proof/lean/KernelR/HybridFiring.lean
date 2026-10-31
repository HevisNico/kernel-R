import KernelR.HybridSilent

/-! The first actual firing of an isolated learned input is extracted and dated from the physical equations. -/
namespace KernelR.Hybrid
open Set MeasureTheory


/-- A learned input forces the actual first main firing before 9/10, even
with variable nondecreasing gain and other nonnegative port currents. -/
theorem Execution.ready_learned_no_overrun {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hr : s.raw i p = some s.time) (hm : e.MainFlows i .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q) (hz : 9 / 5 ≤ Real.exp (s.x i (.z p))) :
    u.time < s.time + 9 / 10 := by
  by_contra hlate
  obtain ⟨v,cut,hcut,hv⟩ := e.prefix_at (s.time + 9 / 10) (by linarith) (le_of_not_gt hlate)
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
  have hc := readyPulse_emission_by_deadline (start := s.time) hq hz
  rw [hv] at hl
  linarith

theorem SensorCycle.learned_drive_upper_early {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hz : Real.exp (s.x i (.z p)) ≤ 2)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time, t ≤ s.time + 99 / 100 →
      tailDrive v (f.path t) i t ≤ 2 * a * Real.exp (-a * (t - s.time))) := by
  have hraw := (e.raw_allowed_of_no_arrival i p s.time (Or.inr hr) (hno p)).2
  have hothers : e.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply e.allFlows_forall (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q
      exact e.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
    · exact e.allFlows_mono (fun f hf _ => hf)
        (e.raw_absent_allFlows i q (e.raw_absent_of_no_arrival i q (ho q hq) (hno q)).2)
  refine e.allFlows_mono ?_ (e.allFlows_and hraw (e.allFlows_and hothers cycle.gain_before_error))
  intro v w f hf t ht htime
  have hsum : tailDrive v (f.path t) i t = Real.exp (f.path t i (.z p)) * rawTail v i p t := by
    unfold tailDrive
    apply Finset.sum_eq_single p
    · intro q _ hq; simp [rawTail,hf.2.1 q hq]
    · simp
  rw [hsum,hf.2.2 t ⟨ht.1,ht.2.le⟩ htime]
  rcases hf.1 with hn | hr
  · simp only [rawTail,hn,mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [a_coarse_bounds.1])) (Real.exp_pos _).le
  · simpa only [rawTail,hr,mul_assoc] using
      mul_le_mul_of_nonneg_right hz (rawTail_nonnegative v i p t)

structure MainTrigger {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  beforeFire : Snapshot n
  afterFire : Snapshot n
  span : Execution θ route s beforeFire
  entry : Jump route beforeFire afterFire
  rest : Execution θ route afterFire u
  reconstruct : e = span.append (.cons (.jump entry) rest)
  ready_states : span.AllStates (fun v => v.main i = .ready)
  fast_after : afterFire.main i = .fast
  charge : afterFire.x i .q = 1
  early : s.time + 3 / 10 < afterFire.time
  deadline : afterFire.time < s.time + 9 / 10

theorem Execution.learned_input_trigger {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : 1 / 40 - 1 / 100000 ≤ s.x i (.m p) ∧ s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) : Nonempty (MainTrigger e i) := by
  have hgain := learned_gain_bounds hz.1 hz.2
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hdrive := cycle.learned_drive_upper_early hgain.2 hr ho hno
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,entry,rest,he,hstates,hv,hw⟩
  · have hlate := e.ready_learned_no_overrun hb hi i p hr (e.allStates_main_flows i .ready h) hq.1 hgain.1
    exact False.elim (by linarith)
  · have hflows := segment.allStates_main_flows i .ready hstates
    have hg := entry.ready_main_departure i hv hw
    have hlate := segment.ready_learned_no_overrun hb hi i p hr hflows hq.1 hgain.1
    have hearly : s.time + 3 / 10 < v.time := by
      by_contra h
      have hvtime : v.time ≤ s.time + 3 / 10 := le_of_not_gt h
      have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
      have hbound := hp.all_flows
        (fun {v w} f => ∀ t ∈ Ico v.time w.time, t ≤ s.time + 99 / 100 →
          tailDrive v (f.path t) i t ≤ 2 * a * Real.exp (-a * (t - s.time)))
        (fun {v w} f {cut} hc hend hf t ht hu => hf t ⟨ht.1,ht.2.trans_le hend⟩ hu) hdrive
      have hd : segment.AllFlows (fun {v' w'} f => ∀ t ∈ Ico v'.time w'.time,
          tailDrive v' (f.path t) i t ≤ 2 * a * Real.exp (-a * (t - s.time))) := by
        refine segment.allFlows_mono ?_ (segment.allFlows_and hbound segment.allFlows_time_bounds)
        intro a' b' f hf t ht
        exact hf.1 t ht (by have htime := (hf.2 t ⟨ht.1,ht.2.le⟩).2; linarith)
      have hu := segment.ready_drive_upper i hflows (s.x i .q) 2 s.time (by rw [readyPulse_initial]) hd
      have hm := readyPulse_emission_not_early hq.2 (le_refl (2 : ℝ)) segment.time_monotone hvtime
      rw [hg.1] at hu
      exact not_lt_of_ge hu hm
    exact ⟨⟨v,w,segment,entry,rest,he,hstates,hg.2,
      by rw [entry.physical_continuous,hg.1],
      by rw [entry.time_unchanged]; exact hearly,
      by rw [entry.time_unchanged]; exact hlate⟩⟩
theorem Jump.ready_main_departure_emission {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hs : s.main i = .ready) (hu : u.main i ≠ .ready) :
    j.ledger.emissions = [(i,s.time)] := by
  cases j <;> simp_all [Jump.ledger,Ledger.zero,setMain,setAux,setRaw,Function.update_apply]

theorem Execution.emissions_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u) :
    (segment.append rest).ledger.emissions = segment.ledger.emissions ++ rest.ledger.emissions := by
  induction segment with
  | nil => rfl
  | cons move tail ih => simp only [append,ledger,Ledger.add,ih,List.append_assoc]

/-- The first main-mode departure contributes exactly one actual emission at
its physical guard date. Every earlier same-cell emission is excluded. -/
theorem MainTrigger.emission_times {n θ route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) : e.emissionTimes i = tr.beforeFire.time :: tr.rest.emissionTimes i := by
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

theorem MainTrigger.positive_count {n θ route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) : 1 ≤ (e.signal i).count := by
  rw [Execution.signal_count,tr.emission_times]
  simp

end KernelR.Hybrid
