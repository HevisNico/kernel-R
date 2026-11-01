import KernelR.HybridProtectedReturn

/-! The protected input prepares recovery from its actual low-recovery SLOW entry. -/
namespace KernelR.Hybrid
open Set

theorem Execution.no_emissions_of_slow_window {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.main i = .slow)
    (hw : e.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow))
    (hr : e.AllStates (fun v => s.time + 1 < v.time → ∀ p, v.raw i p = none))
    (hno : ∀ p, NoArrivalAt e i p) : e.emissionTimes i = [] := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hwmode⟩
  · exact e.no_emissions_if_not_ready i (e.allStates_mono (fun v hv => by rw [hv]; decide) h)
  · have hwindow := hw
    rw [he,Execution.allStates_append] at hwindow
    have hafterWindow := rest.allStates_initial hwindow.2.2
    have hlate : s.time + 419 / 300 < w.time := by
      by_contra hn
      exact hwmode (hafterWindow (le_of_not_gt hn))
    have hraw := hr
    rw [he,Execution.allStates_append] at hraw
    have hrawAfter := rest.allStates_initial hraw.2.2 (by linarith : s.time + 1 < w.time)
    have hnoRest : ∀ p, NoArrivalAt rest i p := by
      intro p
      have hn := hno p
      rw [he,Execution.noArrivalAt_append] at hn
      exact fun d hd => hn.2 d (List.mem_append_right _ hd)
    have hq : w.x i .q ≤ 1 / 10 := by rw [exit.physical_continuous,exit.slow_departure_guard i hv hwmode]
    have hquiet := rest.ready_without_input i (exit.slow_main_departure i hv hwmode) hq hrawAfter hnoRest
    exact e.no_emissions_of_split segment exit rest he i
      (segment.no_emissions_if_not_ready i (segment.allStates_mono (fun v hv => by rw [hv]; decide) hstates))
      (exit.no_emissions_if_not_ready i (by rw [hv]; decide))
      (rest.no_emissions_of_ready_states i hquiet)

structure ProtectedPulse {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (p : Port) where
  cycle : SensorCycle e i p
  admission_return : ReadyReturn e i
  emissions : e.emissionTimes i = []
  mark_dose : e.ledger.mark i p = 1 / 10
  mark_other : ∀ q, q ≠ p → e.ledger.mark i q = 0
  error_zero : ∀ q, e.ledger.error i q = 0
  gain_preserved : ∀ q, u.x i (.z q) = s.x i (.z q)
  recovery_gain : u.x i .b = s.x i .b + 1 / 10
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ q, u.raw i q = none

/-- A protected input at the SLOW entry left by the first strong low-recovery
pulse supplies exactly one MARK dose and prepares the next learned input.
The sensor cycle, open gates, zero output count and return are derived from e. -/
theorem Execution.protected_pulse_of_invariant {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (ProtectedPulse e i p) := by
  have hi := hf.region
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hd := cycle.full_protected_mark_of_invariant hb hf hv hs hr ho hno
  obtain ⟨ret⟩ := cycle.protected_return_of_invariant hb hf hv hs hr ho hno ht
  have hu := ret.final_ready hno
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq) (hno q)
  have hgain : ∀ q, u.x i (.z q) = s.x i (.z q) := by
    intro q
    by_cases hq : q = p
    · subst q; exact hd.2.2
    · exact (hother q hq).2
  have hmark : ∀ q, q ≠ p → e.ledger.mark i q = 0 := by
    intro q hq
    have hquiet := e.aux_ready_without_input_band i q (hs.auxiliary q).1 (hs.auxiliary q).2.2 (ho q hq) (hno q)
    exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hbgain : u.x i .b = s.x i .b + 1 / 10 := by
    rw [e.recovery_balance i,e.recovery_sum_marks i,
      Finset.sum_eq_single p (fun q _ hq => hmark q hq) (by simp),hd.1]
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  have htarget := cycle.final_rest hv hr (hno p)
  refine ⟨{
    cycle := cycle
    admission_return := ret
    emissions := e.no_emissions_of_slow_window i hs.slow (cycle.protected_window hb hv hs hr ho hno).1 hraw hno
    mark_dose := hd.1
    mark_other := hmark
    error_zero := ?_
    gain_preserved := hgain
    recovery_gain := hbgain
    prepared := ?_
    charge_rest := hu.2
    raw_finished := e.allStates_final hraw (by linarith)
  }⟩
  · intro q
    have h := e.gain_balance i q
    rw [hgain q] at h
    linarith
  · refine ⟨hu.1,by rw [hu.2]; norm_num,by rw [hbgain]; constructor <;> linarith [hs.recovery.1,hs.recovery.2],?_⟩
    intro q
    by_cases hq : q = p
    · subst q; exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1

theorem Execution.protected_pulse {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (ProtectedPulse e i p) := by
  exact e.protected_pulse_of_invariant hb (past.physical_invariant hb (hborn.physical_invariant hb))
    (past.raw_valid hborn.raw_valid) i p hs hr ho hno ht

end KernelR.Hybrid
