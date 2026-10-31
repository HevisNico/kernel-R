import KernelR.HybridRecoveryTrace

/-! An unconditional one-input MARK budget, before proving actuator exposure. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Execution.mark_split {n θ route s u v w} (e : @Execution n θ route s u)
    (segment : Execution θ route s v) (exit : Jump route v w) (rest : Execution θ route w u)
    (he : e = segment.append (.cons (.jump exit) rest)) (i : Fin n) (p : Port) :
    e.ledger.mark i p = segment.ledger.mark i p + rest.ledger.mark i p := by
  calc
    e.ledger.mark i p = (segment.append (.cons (.jump exit) rest)).ledger.mark i p :=
      congrArg (fun actual => actual.ledger.mark i p) he
    _ = _ := by simp [mark_append,ledger,Move.ledger,Ledger.add,exit.mark_zero]

/-- The actual sensor decomposition places the entire MARK ledger in its
selected MARK phase, including all zero-time interleavings. -/
theorem SensorCycle.mark_ledger_eq_phase {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    e.ledger.mark i p = cycle.phases.markPhase.span.ledger.mark i p := by
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  have hst := e.mark_skip_zero_head st.span st.entry st.rest st.reconstruct i p
    (st.span.mark_zero_aux i p .ready (by decide) st.flows)
  have hmk := st.rest.mark_split mk.span mk.exit mk.rest mk.reconstruct i p
  have hsi := mk.rest.mark_skip_zero_head si.span si.exit si.rest si.reconstruct i p
    (si.span.mark_zero_aux i p .silent (by decide) si.flows)
  have her := si.rest.mark_skip_zero_head er.span er.exit er.rest er.reconstruct i p
    (er.span.mark_zero_aux i p .error (by decide) er.flows)
  have htail := er.rest.mark_zero_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready (cycle.error_rest_ready hv hr hno))
  linarith

/-- One autonomous sensor cycle can add at most one full MARK charge, even
before the main-mode and actuator-gate chronology has been established. -/
theorem SensorCycle.mark_budget {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) : e.ledger.mark i p ≤ 1 / 10 := by
  rw [cycle.mark_ledger_eq_phase hv hr hno]
  have hbound := cycle.phases.markPhase.span.mark_charge_upper hb i p cycle.phases.markPhase.flows
  rw [cycle.trigger.charge,cycle.phases.markPhase.charge] at hbound
  norm_num only [protectedFloor] at hbound
  linarith

theorem Execution.recovery_one_input_budget {n θ ε route s u i p} (e : @Execution n θ route s u)
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ha : ∀ q, q ≠ p → s.aux i q = .ready ∧ s.x i (.m q) ≤ 1 / 40 + 1 / 100000) :
    u.x i .b ≤ s.x i .b + 1 / 10 := by
  have hother : ∀ q, q ≠ p → e.ledger.mark i q = 0 := by
    intro q hq
    have hquiet := e.aux_ready_without_input_band i q (ha q hq).1 (ha q hq).2 (ho q hq) (hno q)
    exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hbnd := cycle.mark_budget hb hv hr (hno p)
  have hsum : e.ledger.recovery i = e.ledger.mark i p := by
    rw [e.recovery_sum_marks i]
    exact Finset.sum_eq_single p (fun q _ hq => hother q hq) (by simp)
  rw [e.recovery_balance i,hsum]
  linarith

theorem Execution.recovery_upper_of_end {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (B : ℝ) (he : u.x i .b ≤ B) :
    e.AllStates (fun v => v.x i .b ≤ B) ∧
      e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b ≤ B) := by
  induction e with
  | nil => exact ⟨he,trivial⟩
  | @cons s v u move rest ih =>
    have hrest := ih he
    have hv : v.x i .b ≤ B := (rest.recovery_nondecreasing hb i).trans he
    cases move with
    | flow f =>
      have hs := f.recovery_nondecreasing hb i _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hs
      exact ⟨⟨hs.trans hv,hrest.1⟩,⟨fun t ht => (f.recovery_le_final hb i t ht).trans hv,hrest.2⟩⟩
    | jump j => exact ⟨⟨by simpa only [j.physical_continuous] using hv,hrest.1⟩,hrest.2⟩

theorem Execution.accumulatedRecovery_of_upper {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (B : ℝ)
    (h : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b ≤ B)) :
    e.accumulatedRecovery i ≤ B * (u.time - s.time) := by
  induction e with
  | nil => simp [accumulatedRecovery]
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hf : f.accumulatedRecovery i ≤ B * (v.time - s.time) := by
        have hI : (∫ t in s.time..v.time, f.path t i .b) ≤ ∫ _t in s.time..v.time, B :=
          intervalIntegral.integral_mono_on f.positive.le
            ((f.continuous i .b).intervalIntegrable_of_Icc f.positive.le) intervalIntegrable_const h.1
        simpa only [Flow.accumulatedRecovery,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hI
      have hr := ih h.2
      simp only [accumulatedRecovery]
      linarith
    | jump j => simpa only [accumulatedRecovery,j.time_unchanged] using ih h

theorem SensorCycle.mark_flows {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) {P : ∀ {v w : Snapshot n}, Flow θ v w → Prop} (h : e.AllFlows P) :
    cycle.phases.markPhase.span.AllFlows P := by
  rw [cycle.trigger.reconstruct,Execution.allFlows_append] at h
  have hrest : cycle.trigger.rest.AllFlows P := h.2
  rw [cycle.phases.markPhase.reconstruct,Execution.allFlows_append] at hrest
  exact hrest.1

theorem Execution.mark_exposed_of_upper {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (ha : e.AuxFlows i p .mark)
    (hm : e.AllStates (fun v => v.main i ≠ .ready))
    (hc : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b < 11 / 10)) :
    e.MarkExposed i p := by
  induction e with
  | nil => trivial
  | @cons s v u move rest ih =>
    let progressed := past.append (.cons move (.nil _))
    cases move with
    | flow f =>
      exact ⟨f.mark_open_of_reachable past hborn hb i p ha.1 hm.1 hc.1,ih progressed ha.2 hm.2 hc.2⟩
    | jump j => exact ih progressed ha hm.2 hc

end KernelR.Hybrid
