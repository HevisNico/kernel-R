import KernelR.HybridSilentReturn
/-! Silent physical inputs at period four, retaining the actual READY charge carry. -/
namespace KernelR.Hybrid
open Set

theorem readyPulse_uniform_bound {initial amplitude start t Q G : ℝ}
    (hi : initial ≤ Q) (hQ : 1 / 10 ≤ Q) (ha : amplitude ≤ G) (hG : 0 ≤ G)
    (ht : start ≤ t) : readyPulse initial amplitude start t ≤ Q + G * (16 / 25) := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ Q - 1 / 10 by linarith)
    (by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (response_uniform_upper hd) hG
  unfold readyPulse
  linarith

theorem period_four_ready_decay {duration : ℝ} (ht : 3 ≤ duration) :
    Real.exp (-(1 / 2 : ℝ) * duration) ≤ 9 / 40 := by
  have hex : (40 / 9 : ℝ) ≤ Real.exp (3 / 2) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  calc
    _ ≤ Real.exp (-(3 / 2 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by
      rw [Real.exp_neg,inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith

/-- After the actual raw end, the exact READY relaxation retains a quantitative
charge bound at a four-unit successor. No reset to resting charge is used. -/
theorem Execution.silent_period_four_carry {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (Q G : ℝ) (hQ : 1 / 10 ≤ Q) (hG : 0 ≤ G)
    (hq : s.x i .q ≤ Q) (hm : e.AllStates (fun v => v.main i = .ready))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 4 ≤ u.time)
    (hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      tailDrive v (f.path t) i t ≤ G * a * Real.exp (-a * (t - s.time)))) :
    u.x i .q ≤ 1 / 10 + (Q + G * (16 / 25) - 1 / 10) * (9 / 40) ∧
      ∀ q, u.raw i q = none := by
  obtain ⟨d⟩ := e.raw_end_completion i p s.time hr (by linarith) (by linarith)
  have hmode := hm
  rw [d.reconstruct,Execution.allStates_append] at hmode
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
  have hraw : ∀ q, d.rest.RawAbsent i q := fun q =>
    (d.rest.raw_absent_of_no_arrival i q (hrawAfter q) (hnoRest q)).2
  have hsol := d.rest.ready_no_current_solution i (d.rest.allStates_main_flows i .ready hmode.2.2) hraw
  have hdrive := hd
  rw [d.reconstruct,Execution.allFlows_append] at hdrive
  have hupper := d.span.ready_drive_upper i (d.span.allStates_main_flows i .ready hmode.1)
    (s.x i .q) G s.time (by rw [readyPulse_initial]) hdrive.1
  have hpeak := readyPulse_uniform_bound hq hQ le_rfl hG d.span.time_monotone
  have hx : d.afterEnd.x i .q ≤ Q + G * (16 / 25) := by
    rw [d.exit.physical_continuous]
    exact hupper.trans hpeak
  have hdate : d.afterEnd.time = s.time + 1 := by rw [d.exit.time_unchanged,d.date]
  have hdecay := period_four_ready_decay (duration := u.time - d.afterEnd.time) (by rw [hdate]; linarith)
  have hcarry := mul_le_mul_of_nonneg_right
    (show d.afterEnd.x i .q - 1 / 10 ≤ Q + G * (16 / 25) - 1 / 10 by linarith)
    (Real.exp_pos (-(1 / 2 : ℝ) * (u.time - d.afterEnd.time))).le
  have hnon : 0 ≤ Q + G * (16 / 25) - 1 / 10 := by nlinarith
  refine ⟨by nlinarith,fun q => (d.rest.raw_absent_of_no_arrival i q (hrawAfter q) (hnoRest q)).1⟩

structure CadenceReadyCoordinates {n} (s : Snapshot n) (i : Fin n) (cap : ℝ) : Prop where
  ready : s.main i = .ready
  charge : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ cap
  auxiliary : ∀ p, s.aux i p = .ready ∧ RestBand (s.x i (.m p))

structure CadenceSilentPulse {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (cap : ℝ) where
  cycle : SensorCycle e i p
  coordinates : CadenceReadyCoordinates u i cap
  emissions : e.emissionTimes i = []
  error_dose : e.ledger.error i p = 3 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_zero : ∀ q, e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = s.x i (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q)
  recovery_preserved : u.x i .b = s.x i .b
  raw_finished : ∀ q, u.raw i q = none

/-- Quantitative real drive bounds give the physical silent case and full
ERROR dose while keeping enough charge information for the next period-four
input. The supplied bounds are scalar inequalities, not pulse-case premises. -/
theorem Execution.cadence_silent_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (Q G nextCap : ℝ)
    (hs : CadenceReadyCoordinates s i Q) (hQ : 1 / 10 ≤ Q) (hG : 0 ≤ G)
    (hpeak : Q + G * (16 / 25) < 1)
    (hnext : 1 / 10 + (Q + G * (16 / 25) - 1 / 10) * (9 / 40) ≤ nextCap)
    (hz : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hg : ∀ z, z ≤ s.x i (.z p) + 11 / 125 → Real.exp z ≤ G)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 4 ≤ u.time) :
    Nonempty (CadenceSilentPulse e i p nextCap) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hf.region i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hdrive := cycle.single_drive_upper hb G hG hg hr ho hno
  have hsilent := e.ready_of_upper_drive i hs.ready G hdrive
    (fun t ht => (readyPulse_uniform_bound hs.charge.2 hQ le_rfl hG ht).trans_lt hpeak)
  have hflows := e.allStates_main_flows i .ready hsilent.1
  have hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p) :=
    lt_of_le_of_lt (by linarith) (hb.fast_nominal_headroom i p)
  have hd := cycle.total_error_of_invariant hb hf hv hsilent.1 hh hr (hno p)
  have hcarry := e.silent_period_four_carry i p Q G hQ hG hs.charge.2 hsilent.1 hr ho hno ht hdrive
  have hlower := e.ready_charge_lower i hflows hs.charge.1
  have htarget := cycle.final_rest hv hr (hno p)
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq) (hno q)
  refine ⟨⟨cycle,?_,hsilent.2,hd.1,?_,fun q => e.mark_zero_ready i q hflows,
    hd.2,fun q hq => (hother q hq).2,e.recovery_constant_ready i hflows,hcarry.2⟩⟩
  · refine ⟨e.allStates_final hsilent.1,⟨hlower,hcarry.1.trans hnext⟩,?_⟩
    intro q
    by_cases hq : q = p
    · subst q
      exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1
  · intro q hq
    have h := e.gain_balance i q
    rw [(hother q hq).2] at h
    linarith

end KernelR.Hybrid
