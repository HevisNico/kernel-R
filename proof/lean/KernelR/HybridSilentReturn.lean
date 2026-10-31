import KernelR.HybridNominalSilent

/-! Actual silent learning preserves READY coordinates before the next separated input. -/
namespace KernelR.Hybrid
open Set

structure ReadyCoordinates {n} (s : Snapshot n) (i : Fin n) : Prop where
  ready : s.main i = .ready
  charge : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50
  auxiliary : ∀ p, s.aux i p = .ready ∧ RestBand (s.x i (.m p))

theorem PreparedSection.ready_coordinates {n s i} (hs : @PreparedSection n s i) : ReadyCoordinates s i :=
  ⟨hs.ready,hs.charge,hs.auxiliary⟩

theorem Execution.allFlows_of {n θ route s u} (e : @Execution n θ route s u)
    (P : ∀ {v w : Snapshot n}, Flow θ v w → Prop) (h : ∀ {v w} (f : Flow θ v w), P f) :
    e.AllFlows P := by
  induction e with
  | nil => trivial
  | cons move rest ih => cases move with
    | flow f => exact ⟨h f,ih⟩
    | jump j => exact ih

theorem Execution.raw_none_states {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hr : s.raw i p = none) (hno : NoArrivalAt e i p) :
    e.AllStates (fun v => v.raw i p = none) := by
  induction e with
  | nil => exact hr
  | cons move rest ih =>
    refine ⟨hr,ih ?_ (fun d hd => hno d (List.mem_append_right _ hd))⟩
    cases move with
    | flow f => simpa only [f.raw_fixed] using hr
    | jump j =>
      exact j.raw_none_of_no_arrival i p hr (fun d hd => hno d (List.mem_append_left _ hd))

theorem Execution.ready_charge_lower {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .ready) (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q) :
    1 / 10 - 1 / 100000 ≤ u.x i .q := by
  have hd : e.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      (0 : ℝ) * a * Real.exp (-a * (t - s.time)) ≤ tailDrive v (f.path t) i t) := by
    apply e.allFlows_of
    intro v w f t ht
    simp only [zero_mul]
    unfold tailDrive
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (rawTail_nonnegative v i p t))
  have hlo := e.ready_drive_lower i hm (s.x i .q) 0 s.time (by rw [readyPulse_initial]) hd
  have he : Real.exp (-(1 / 2 : ℝ) * (u.time - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [e.time_monotone])
  have hc : -(1 / 100000 : ℝ) ≤ (s.x i .q - 1 / 10) * Real.exp (-(1 / 2) * (u.time - s.time)) := by
    have h := mul_le_mul_of_nonneg_right (show -(1 / 100000 : ℝ) ≤ s.x i .q - 1 / 10 by linarith)
      (Real.exp_pos (-(1 / 2 : ℝ) * (u.time - s.time))).le
    nlinarith
  simp only [readyPulse,zero_mul,add_zero] at hlo
  linarith

theorem long_ready_decay {duration : ℝ} (ht : 13 / 2 ≤ duration) :
    Real.exp (-(1 / 2 : ℝ) * duration) ≤ 1 / 25 := by
  have hex : (25 : ℝ) ≤ Real.exp (13 / 4) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 4) 10
    norm_num [Finset.sum_range_succ] at h
    linarith
  calc
    _ ≤ Real.exp (-(13 / 4 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by
      rw [Real.exp_neg,inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith

/-- Once the actual raw end is selected, READY relaxation returns the charge
to the common input band before every 7.5-gap successor. -/
theorem Execution.silent_charge_return {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : e.AllStates (fun v => v.main i = .ready))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) :
    u.x i .q ≤ 7 / 50 ∧ ∀ q, u.raw i q = none := by
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
  have hx : d.afterEnd.x i .q ≤ 1 := by
    rw [d.exit.physical_continuous]; exact (d.span.upper_region hb hi i).2.1
  have hdate : d.afterEnd.time = s.time + 1 := by rw [d.exit.time_unchanged,d.date]
  have hdecay := long_ready_decay (duration := u.time - d.afterEnd.time) (by rw [hdate]; linarith)
  have hcarry := mul_le_mul_of_nonneg_right (show d.afterEnd.x i .q - 1 / 10 ≤ (9 / 10 : ℝ) by linarith)
    (Real.exp_pos (-(1 / 2 : ℝ) * (u.time - d.afterEnd.time))).le
  refine ⟨by nlinarith,?_⟩
  exact fun q => (d.rest.raw_absent_of_no_arrival i q (hrawAfter q) (hnoRest q)).1

structure SilentPulse {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) where
  cycle : SensorCycle e i p
  coordinates : ReadyCoordinates u i
  emissions : e.emissionTimes i = []
  error_dose : e.ledger.error i p = 3 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_zero : ∀ q, e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = s.x i (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q)
  recovery_preserved : u.x i .b = s.x i .b
  raw_finished : ∀ q, u.raw i q = none

/-- The complete silent input case works at low birth recovery as well as
after preparation. No MARK dose or training word is assumed. -/
theorem Execution.silent_pulse_of_invariant {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hz : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (SilentPulse e i p) := by
  have hi := hf.region
  have hsilent := e.nominal_silent_input hb hi i p hs.ready hs.charge.2 hz (hs.auxiliary p).1 hr (hs.auxiliary p).2 ho hno (by linarith)
  have hflows := e.allStates_main_flows i .ready hsilent.1
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p) :=
    lt_of_le_of_lt (by linarith) (hb.fast_nominal_headroom i p)
  have hd := cycle.total_error_of_invariant hb hf hv hsilent.1 hh hr (hno p)
  have hqreturn := e.silent_charge_return hb hi i p hsilent.1 hr ho hno ht
  have hqlower := e.ready_charge_lower i hflows hs.charge.1
  have htarget := cycle.final_rest hv hr (hno p)
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq) (hno q)
  refine ⟨⟨cycle,?_,hsilent.2,hd.1,?_,fun q => e.mark_zero_ready i q hflows,
    hd.2,fun q hq => (hother q hq).2,e.recovery_constant_ready i hflows,hqreturn.2⟩⟩
  · refine ⟨e.allStates_final hsilent.1,⟨hqlower,hqreturn.1⟩,?_⟩
    intro q
    by_cases hq : q = p
    · subst q; exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1
  · intro q hq
    have h := e.gain_balance i q
    rw [(hother q hq).2] at h
    linarith

theorem Execution.silent_pulse {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hz : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (SilentPulse e i p) := by
  exact e.silent_pulse_of_invariant hb (past.physical_invariant hb (hborn.physical_invariant hb))
    (past.raw_valid hborn.raw_valid) i p hs hz hr ho hno ht

theorem SilentPulse.prepared {n θ route s u i p} {e : @Execution n θ route s u}
    (pulse : SilentPulse e i p) (hs : PreparedSection s i) : PreparedSection u i :=
  ⟨pulse.coordinates.ready,pulse.coordinates.charge,
    by rw [pulse.recovery_preserved]; exact hs.recovery,pulse.coordinates.auxiliary⟩

end KernelR.Hybrid
