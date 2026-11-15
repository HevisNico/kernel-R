import ProtectedReceipt
import KernelR.HybridMarkBudget

/-! The protected receipt dose on the actual auxiliary-deadline segment. -/
namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid Set

/-- The receipt budget excludes a first SLOW departure on the selected
cell. The accumulated recovery is that of the actual execution prefix. -/
theorem slow_through_budget {θ : Fin N → KernelR.Hybrid.Parameters}
    {route : Router N} {s u : Snapshot N} (body : Execution θ route s u) (i : Fin N)
    (fastEnd : ℝ) (slow : s.main i = .slow)
    (charge : s.x i .q = (1 / 4) * Real.exp (-(9 / 50) * (s.time - fastEnd)))
    (B : ℝ) (nonnegative : 0 ≤ B)
    (budget : (9 / 50) * (s.time - fastEnd) + B * (u.time - s.time) < 9 / 10)
    (recovery : body.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b ≤ B)) :
    body.AllStates (fun v => v.main i = .slow) := by
  rcases body.first_state_change (fun v => v.main i) .slow
      (fun f => congrFun f.main_fixed i) slow with stays |
      ⟨before, after, prefixRun, exit, rest, shape, states, beforeSlow, departure⟩
  · exact stays
  · have prefixRecovery : prefixRun.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time,
          f.path t i .b ≤ B) := by
      rw [shape, Execution.allFlows_append] at recovery
      exact recovery.1
    have integral := prefixRun.accumulatedRecovery_of_upper i B prefixRecovery
    have onTime : before.time ≤ u.time := exit.time_unchanged.ge.trans rest.time_monotone
    have maxIntegral := integral.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_right onTime s.time) nonnegative)
    have cost : (9 / 50) * (s.time - fastEnd) + prefixRun.accumulatedRecovery i < 9 / 10 := by
      linarith
    have solution := prefixRun.slow_solution i (prefixRun.allStates_main_flows i .slow states)
    rw [exit.slow_departure_guard i beforeSlow departure, charge, mul_assoc, ← Real.exp_add] at solution
    have exponent : -(9 / 50) * (s.time - fastEnd) + -prefixRun.accumulatedRecovery i =
        -((9 / 50) * (s.time - fastEnd) + prefixRun.accumulatedRecovery i) := by ring
    rw [exponent] at solution
    exact ((ne_of_lt (quarter_above_reopen cost)) solution).elim

/-- Per-cell observations on the actual segment from RAW admission to the
auxiliary deadline. Activity on the other cells remains in the segment. -/
structure ReceiptWindow {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} (body : Execution θ route s u) (i : Fin N) (port : Port) : Prop where
  slow : body.AllStates (fun v => v.main i = .slow)
  noFire : body.emissionTimes i = []
  error : ∀ q, body.ledger.error i q = 0
  mark : ∀ q, body.ledger.mark i q = if q = port then 1 / 10 else 0
  recovery : body.ledger.recovery i = 1 / 10
  settled : ∀ q, u.raw i q = none ∧ u.aux i q = .ready

/-- The one-input MARK cap is proved before it is used in the T3 inequality.
The completed dose then comes from the actual MARK endpoints in the selected
cell's sensor cycle. -/
theorem receipt_window_doses {θ : Fin N → KernelR.Hybrid.Parameters} {route : Router N}
    {s u : Snapshot N} {ε : ℝ} (body : Execution θ route s u) (i : Fin N) (port : Port)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (fastEnd : ℝ) (slow : s.main i = .slow)
    (charge : s.x i .q = (1 / 4) * Real.exp (-(9 / 50) * (s.time - fastEnd)))
    (cold : s.x i .b = 9 / 50)
    (date : u.time = s.time + (auxDeadline : ℝ))
    (budget : (9 / 50) * (s.time - fastEnd) + (7 / 25) * (auxDeadline : ℝ) < 9 / 10)
    (aux : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (active : s.raw i port = some s.time) (inactive : ∀ q, q ≠ port → s.raw i q = none)
    (isolated : ∀ q, NoArrivalAt body i q) : ReceiptWindow body i port := by
  have deadline : s.time + 419 / 300 ≤ u.time := by rw [date]; norm_num [auxDeadline]
  obtain ⟨cycle⟩ := body.sensor_cycle box physical.region i port (aux port).1 active
    (aux port).2 deadline
  have provisional := body.recovery_one_input_budget cycle box valid active inactive isolated
    (fun q _ => ⟨(aux q).1, (aux q).2.2⟩)
  have bound := body.recovery_upper_of_end box i (7 / 25) (by linarith)
  have stays := slow_through_budget body i fastEnd slow charge (7 / 25) (by norm_num)
    (by rw [date]; linarith) bound.2
  have protectedStates : body.AllStates (fun v => v.main i ≠ .ready) :=
    body.allStates_mono (fun v hv => by rw [hv]; decide) stays
  have silent := body.no_emissions_if_not_ready i protectedStates
  let phase := cycle.phases.markPhase
  let pastMark := cycle.trigger.span.append (.cons (.jump cycle.trigger.entry) (.nil _))
  have cap : phase.span.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time,
      f.path t i .b < 11 / 10) := by
    refine phase.span.allFlows_mono ?_ (cycle.mark_flows bound.2)
    intro v w f h t ht
    linarith [h t ht]
  have exposed := phase.span.mark_exposed_of_invariant box
    (pastMark.physical_invariant box physical) i port phase.flows
    (cycle.mark_states protectedStates) cap
  have fullMark := phase.span.full_mark_of_open_endpoints i port exposed cycle.trigger.charge
    (by simpa only [protectedFloor] using phase.charge)
  have selected : body.ledger.mark i port = 1 / 10 :=
    (cycle.mark_ledger_eq_phase valid active (isolated port)).trans fullMark
  have other (q : Port) (ne : q ≠ port) : body.AllStates (fun v => v.aux i q = .ready) :=
    body.aux_ready_without_input_band i q (aux q).1 (aux q).2.2 (inactive q ne) (isolated q)
  have otherMark (q : Port) (ne : q ≠ port) : body.ledger.mark i q = 0 :=
    body.mark_zero_aux i q .ready (by decide) (body.allStates_aux_flows i q .ready (other q ne))
  have dry := body.raw_expired_states i s.time valid (fun q => by
    by_cases same : q = port
    · subst q; exact Or.inr active
    · exact Or.inl (inactive q same)) isolated
  have expired : s.time + 1 < u.time := by rw [date]; norm_num [auxDeadline]
  refine ⟨stays, silent, ?_, ?_, ?_, ?_⟩
  · intro q
    have gain := body.gain_constant_protected_states i q protectedStates
    have balance := body.gain_balance i q
    linarith
  · intro q
    by_cases same : q = port
    · subst q; simpa using selected
    · simp [same, otherMark q same]
  · rw [body.recovery_sum_marks i,
      Finset.sum_eq_single port (fun q _ ne => otherMark q ne) (by simp), selected]
  · intro q
    refine ⟨body.allStates_final dry expired q, ?_⟩
    by_cases same : q = port
    · subst q; exact (cycle.final_rest valid active (isolated port)).1
    · exact body.allStates_final (other q same)

end NetworkStability.NativeMultiToken
