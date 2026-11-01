import KernelR.HybridPulseBounds
import KernelR.HybridPulseSection

/-! Actual first firing and prepared-section preservation for both training gain regimes. -/
namespace KernelR.Hybrid
open Set

theorem SensorCycle.frozen_drive_upper {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (G : ℝ) (hG : 0 ≤ G) (hz : Real.exp (s.x i (.z p)) ≤ G)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time, t ≤ s.time + 99 / 100 →
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - s.time))) := by
  have hraw := (e.raw_allowed_of_no_arrival i p s.time (Or.inr hr) (hno p)).2
  have hothers : e.AllFlows (fun {v w} _ => ∀ q, q ≠ p → v.raw i q = none) := by
    apply e.allFlows_forall (fun q {v w} _ => q ≠ p → v.raw i q = none)
    intro q
    by_cases hq : q = p
    · subst q; exact e.allFlows_mono (fun f _ h => False.elim (h rfl)) hraw
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
    exact mul_nonneg (mul_nonneg hG (by linarith [a_coarse_bounds.1])) (Real.exp_pos _).le
  · simpa only [rawTail,hr,mul_assoc] using mul_le_mul_of_nonneg_right hz (rawTail_nonnegative v i p t)

theorem Execution.mid_gain_input_trigger {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port) (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time)
    (hx : RestBand (s.x i (.m p))) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 419 / 300 ≤ u.time) : Nonempty (MainTrigger e i) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have hdrive := cycle.frozen_drive_upper (12 / 5) (by norm_num) hz.2 hr ho hno
  rcases e.first_state_change (fun v => v.main i) .ready
    (fun f => congrFun f.main_fixed i) hm with h | ⟨v,w,segment,entry,rest,he,hstates,hv,hw⟩
  · have hlate := e.ready_learned_no_overrun hb hi i p hr (e.allStates_main_flows i .ready h) hq.1 hz.1
    exact False.elim (by linarith)
  · have hflows := segment.allStates_main_flows i .ready hstates
    have hg := entry.ready_main_departure i hv hw
    have hlate := segment.ready_learned_no_overrun hb hi i p hr hflows hq.1 hz.1
    have hearly : s.time + 3 / 10 < v.time := by
      by_contra h
      have hvtime : v.time ≤ s.time + 3 / 10 := le_of_not_gt h
      have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
      have hbound := hp.all_flows
        (fun {v w} f => ∀ t ∈ Ico v.time w.time, t ≤ s.time + 99 / 100 →
          tailDrive v (f.path t) i t ≤ (12 / 5) * a * Real.exp (-a * (t - s.time)))
        (fun {v w} f {cut} hc hend hf t ht hu => hf t ⟨ht.1,ht.2.trans_le hend⟩ hu) hdrive
      have hd : segment.AllFlows (fun {v' w'} f => ∀ t ∈ Ico v'.time w'.time,
          tailDrive v' (f.path t) i t ≤ (12 / 5) * a * Real.exp (-a * (t - s.time))) := by
        refine segment.allFlows_mono ?_ (segment.allFlows_and hbound segment.allFlows_time_bounds)
        intro v' w' f hf t ht
        exact hf.1 t ht (by have htime := (hf.2 t ⟨ht.1,ht.2.le⟩).2; linarith)
      have hu := segment.ready_drive_upper i hflows (s.x i .q) (12 / 5) s.time (by rw [readyPulse_initial]) hd
      have hmodel := readyPulse_mid_gain_not_early hq.2 le_rfl segment.time_monotone hvtime
      rw [hg.1] at hu
      exact not_lt_of_ge hu hmodel
    exact ⟨⟨v,w,segment,entry,rest,he,hstates,hg.2,
      by rw [entry.physical_continuous,hg.1],
      by rw [entry.time_unchanged]; exact hearly,
      by rw [entry.time_unchanged]; exact hlate⟩⟩

theorem Execution.learned_mid_pulse_of_valid {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : PreparedSection s i)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (LearnedPulse e i) := by
  obtain ⟨tr⟩ := e.mid_gain_input_trigger hb hi i p hs.ready hs.charge hz (hs.auxiliary p).1 hr (hs.auxiliary p).2 ho hno (by linarith)
  exact tr.prepared_case_of_valid hb hi hv p hs hr ho hno ht

theorem Execution.learned_mid_pulse {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hs : PreparedSection s i)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (LearnedPulse e i) := by
  exact e.learned_mid_pulse_of_valid hb (past.upper_region hb hborn.upper_region)
    (past.raw_valid hborn.raw_valid) i p hs hz hr ho hno ht

end KernelR.Hybrid
