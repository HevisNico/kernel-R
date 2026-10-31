import KernelR.HybridStableMemory

/-! An isolated learned pulse preserves the prepared section with exact doses and count. -/
namespace KernelR.Hybrid
open Set

def RestBand (m : ℝ) : Prop := 1 / 40 - 1 / 100000 ≤ m ∧ m ≤ 1 / 40 + 1 / 100000

structure PreparedSection {n} (s : Snapshot n) (i : Fin n) : Prop where
  ready : s.main i = .ready
  charge : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50
  recovery : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000
  auxiliary : ∀ p, s.aux i p = .ready ∧ RestBand (s.x i (.m p))

theorem Execution.aux_no_input_rest_band {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hs : s.aux i p = .ready) (hx : RestBand (s.x i (.m p)))
    (hr : s.raw i p = none) (hno : NoArrivalAt e i p) :
    (u.aux i p = .ready ∧ RestBand (u.x i (.m p))) ∧ u.x i (.z p) = s.x i (.z p) := by
  have hquiet := e.aux_ready_without_input_band i p hs hx.2 hr hno
  have hm := e.allStates_aux_flows i p .ready hquiet
  have hraw := (e.raw_absent_of_no_arrival i p hr hno).2
  have hsol := e.aux_ready_no_current_solution i p hm hraw
  have hup := decay_upper (show s.x i (.m p) - 1 / 40 ≤ (1 / 100000 : ℝ) by linarith [hx.2])
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (sub_nonneg.mpr e.time_monotone)
  have he : Real.exp (-(1 / 2 : ℝ) * (u.time - s.time)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [e.time_monotone])
  have hlow : -(1 / 100000 : ℝ) ≤ (s.x i (.m p) - 1 / 40) * Real.exp (-(1 / 2) * (u.time - s.time)) := by
    have h := mul_le_mul_of_nonneg_right (show -(1 / 100000 : ℝ) ≤ s.x i (.m p) - 1 / 40 by linarith [hx.1])
      (Real.exp_pos (-(1 / 2 : ℝ) * (u.time - s.time))).le
    nlinarith
  exact ⟨⟨e.allStates_final hquiet,by constructor <;> linarith⟩,(e.gain_constant_aux i p .ready (by decide) hm).1⟩

theorem SensorCycle.final_rest {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hv₀ : RawValid s) (hr : s.raw i p = some s.time)
    (hno : NoArrivalAt e i p) : u.aux i p = .ready ∧ u.x i (.m p) = 1 / 40 := by
  let er := cycle.phases.errorPhase
  have hquiet := cycle.error_rest_ready hv₀ hr hno
  have hrawAll := e.raw_allowed_states i p s.time (Or.inr hr) hno
  have hvalid := e.allStates_raw_valid hv₀
  have ha := er.rest.allStates_initial (cycle.error_states hrawAll).2
  have hv := er.rest.allStates_initial (cycle.error_states hvalid).2
  have hraw : er.afterExit.raw i p = none := by
    rcases ha with h | h
    · exact h
    · exact False.elim (not_lt_of_ge (hv i p s.time h).2 cycle.ready_after_raw)
  have hrspan := (er.rest.raw_absent_of_no_arrival i p hraw (cycle.error_rest_no_arrival p hno)).2
  have hsol := er.rest.aux_ready_no_current_solution i p (er.rest.allStates_aux_flows i p .ready hquiet) hrspan
  have hcharge : er.afterExit.x i (.m p) = 1 / 40 := by simpa only [protectedFloor] using er.after_charge
  exact ⟨er.rest.allStates_final hquiet,by simpa only [hcharge,sub_self,zero_mul,add_zero] using hsol⟩

structure LearnedPulse {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  trigger : MainTrigger e i
  admission_return : ReadyReturn e i
  emissions : e.emissionTimes i = [trigger.beforeFire.time]
  error_zero : ∀ p, e.ledger.error i p = 0
  mark_zero : ∀ p, e.ledger.mark i p = 0
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ p, u.raw i p = none

/-- An actual isolated learned-pulse case with return and preserved memories.
It neither supplies a case word nor asserts birth-to-section reachability. -/
theorem Execution.learned_pulse {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hs : PreparedSection s i)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (LearnedPulse e i) := by
  have hi := past.upper_region hb hborn.upper_region
  have hv := past.raw_valid hborn.raw_valid
  obtain ⟨tr⟩ := e.learned_input_trigger hb hi i p hs.ready hs.charge hz (hs.auxiliary p).1 hr (hs.auxiliary p).2 ho hno (by linarith)
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  obtain ⟨ret⟩ := tr.ready_return past hborn hb hs.recovery.1 p hr ho hno ht
  have hu := ret.final_ready hno
  have hzero := cycle.total_error_zero_of_trigger tr past hborn hr (hno p)
  have hbfinal := e.learned_recovery_unchanged cycle tr hb hv hr hno ho
    (fun q _ => ⟨(hs.auxiliary q).1,(hs.auxiliary q).2.2⟩)
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq) (hno q)
  have htarget := cycle.final_rest hv hr (hno p)
  have hgain : ∀ q, u.x i (.z q) = s.x i (.z q) := by
    intro q
    by_cases hq : q = p
    · subst q; exact hzero.2
    · exact (hother q hq).2
  have hmark : ∀ q, e.ledger.mark i q = 0 := by
    intro q
    by_cases hq : q = p
    · subst q; exact cycle.mark_zero_of_trigger tr hb hv hr (hno p)
    · have hquiet := e.aux_ready_without_input_band i q (hs.auxiliary q).1 (hs.auxiliary q).2.2 (ho q hq) (hno q)
      exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  refine ⟨⟨tr,ret,tr.only_emission past hborn p hr ho hno,?_,hmark,hgain,hbfinal,?_,hu.2,?_⟩⟩
  · intro q
    have h := e.gain_balance i q
    rw [hgain q] at h
    linarith
  · refine ⟨hu.1,by rw [hu.2]; norm_num,by rw [hbfinal]; exact hs.recovery,?_⟩
    intro q
    by_cases hq : q = p
    · subst q
      exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1
  · exact e.allStates_final hraw (by linarith)

end KernelR.Hybrid
