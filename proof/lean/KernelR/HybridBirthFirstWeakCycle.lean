import KernelR.HybridErrorCompletion
import KernelR.HybridFirstInputError
import KernelR.HybridBirthInput

/-! The first complete weak input is constructed from the actual birth queue,
including both possible orders of raw expiry and ERROR entry. -/
namespace KernelR.Hybrid

structure BirthFirstWeakCycle (θ : Fin 1 → Parameters) (route : Router 1) (born : Snapshot 1) where
  birth : BirthState born
  sources : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16
  final : Snapshot 1
  continuation : Execution θ route (birthProtocolFirstAfter born) final
  continuation_transversal : continuation.ContactsTransversal
  pulse : SilentPulse continuation 0 0
  date : final.time = 15 / 2
  saturated : CompleteThrough continuation (15 / 2)
  pending : final.pending = sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16
  no_later_delivery : continuation.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

noncomputable def BirthFirstWeakCycle.execution {θ route born} (c : BirthFirstWeakCycle θ route born) :
    Execution θ route born c.final :=
  .cons (.jump (birth_protocol_first_jump c.birth c.sources)) c.continuation

@[simp] theorem BirthFirstWeakCycle.contacts_transversal {θ route born}
    (c : BirthFirstWeakCycle θ route born) : c.execution.ContactsTransversal := by
  simpa [BirthFirstWeakCycle.execution, birth_protocol_first_jump,
    Execution.ContactsTransversal, Jump.ContactTransversal] using c.continuation_transversal

theorem BirthFirstWeakCycle.complete {θ route born} (c : BirthFirstWeakCycle θ route born) :
    CompleteThrough c.execution (15 / 2) := c.saturated

/-- The complete first weak pulse and its quiet suffix exist for every READY
A birth and physical fabrication choice, without an incoming execution. -/
theorem birth_protocol_first_weak_cycle_exists {θ ε route born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16) :
    Nonempty (BirthFirstWeakCycle θ route born) := by
  obtain ⟨f,_,_⟩ := birth_protocol_first_mark_exists (route := route) hborn hb ha hqueue
  have hqi : (birthProtocolFirstAfter born).x 0 .q ≤ 10001 / 100000 := by
    change born.x 0 .q ≤ 10001 / 100000
    linarith [(hborn.2.2 0).2.1.2]
  have hg : Real.exp ((birthProtocolFirstAfter born).x 0 (.z 0)) ≤ 4 / 3 :=
    hborn.nominal_pulse_gain_upper 0 0
  have hp2 : ∀ d ∈ (birthProtocolFirstAfter born).pending,
      (birthProtocolFirstAfter born).time + 2 ≤ d.due := by
    intro d hd
    change born.time + 2 ≤ d.due
    rw [hborn.1]
    linarith [birth_protocol_remaining_due d hd]
  obtain ⟨g⟩ := f.first_silent_exists hb (by linarith) hg (by
    intro d hd; linarith [hp2 d hd])
  obtain ⟨h⟩ := g.first_error_exists route hb hqi hg hp2
  have hqueueFinal : h.final.pending = (birthProtocolFirstAfter born).pending := h.pending
  have hgainFinal (j : Fin 1) (q : Port) : h.final.x j (.z q) =
      (birthProtocolFirstAfter born).x j (.z q) := h.gain_preserved j q
  let past : Execution θ route born (birthProtocolFirstAfter born) :=
    .cons (.jump (birth_protocol_first_jump hborn hqueue)) (.nil _)
  let preparedTrace := ((f.execution route).append (g.continuation route)).append h.execution
  have hphysical : PhysicalInvariant θ h.final :=
    (past.append preparedTrace).physical_invariant hb (hborn.physical_invariant hb)
  have hz : born.x 0 (.z 0) ≤ Real.log (6 / 5) + 1 / 1000 := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 10)
      (by norm_num : (3 / 10 : ℝ) ≤ 6 / 5)
    have hz := ((hborn.2.2 0).2.2.2.2 (0 : Port)).1.2
    simp only [nominalGain,show (0 : Port) ≠ 1 by decide,ite_false] at hz
    linarith
  have hheadroom : h.final.x 0 (.z 0) + 8 * (h.final.x 0 (.m 0) - 1 / 40) <
      Real.log ((θ 0).cap 0) := by
    rw [hgainFinal,h.sensor_charge]
    change born.x 0 (.z 0) + 8 * (1 / 10 - 1 / 40) < Real.log ((θ 0).cap 0)
    linarith [hb.fast_nominal_headroom 0 0]
  have hduration : h.final.time + errorTailDuration θ h.final 0 0 =
      born.time + f.latency + auxCycleDuration (θ 0) 0 := by
    rw [h.error_date_exact,g.date]
    simp only [FirstInputMark.silentDate,errorTailDuration,h.sensor_charge]
    norm_num only [show (40 : ℝ) * (1 / 10) = 4 by norm_num]
    dsimp [auxCycleDuration,birthProtocolFirstAfter,setRaw]
    ring
  have hschedule := hb.first_cycle_schedule 0 0 ⟨f.early,f.deadline⟩
  have hfinish : born.time + 1 < h.final.time + errorTailDuration θ h.final 0 0 := by
    rw [hduration]
    linarith [hschedule.2.2.2.2.1]
  have hfinish_upper : h.final.time + errorTailDuration θ h.final 0 0 < 419 / 300 := by
    rw [hduration,hborn.1]
    simpa using hschedule.2.2.2.2.2
  have hfuture : ∀ d ∈ h.final.pending,
      h.final.time + errorTailDuration θ h.final 0 0 < d.due := by
    intro d hd
    rw [hqueueFinal] at hd
    linarith [birth_protocol_remaining_due d hd]
  have hm0 : 1 / 40 < h.final.x 0 (.m 0) := by rw [h.sensor_charge]; norm_num
  have hmu : h.final.x 0 (.m 0) ≤ 1 / 10 := h.sensor_charge.le
  have hcompletion : Nonempty (ErrorCompletion θ route h.final 0 0) := by
    rcases h.raw_option with ⟨hr,hactive⟩ | ⟨hr,hafter⟩
    · exact error_completion_with_raw_tail hb h.final 0 0 hphysical h.main_ready h.initialmode
        h.aux_other born.time hr h.raw_other hm0 hmu hheadroom (h.error_date_lower hb).le
        hactive hfinish h.charge_margin h.main_below h.aux_below hfuture
    · have hnone : ∀ j q, h.final.raw j q = none := by
        intro j q
        by_cases hh : j = 0 ∧ q = 0
        · rcases hh with ⟨rfl,rfl⟩; exact hr
        · exact h.raw_other j q (by tauto)
      exact error_completion_without_raw hb h.final 0 0 hphysical h.main_ready h.initialmode
        h.aux_other hnone hm0 hmu hheadroom h.main_below h.aux_below hfuture
  obtain ⟨c⟩ := hcompletion
  have hquiet_time : c.final.time < 15 / 2 := by rw [c.date]; linarith
  have hpquiet : ∀ d ∈ c.final.pending, (15 / 2 : ℝ) < d.due := by
    intro d hd
    rw [c.pending,hqueueFinal] at hd
    linarith [birth_protocol_remaining_due d hd]
  let waitFlow : Flow θ c.final (quietAt c.final (15 / 2)) := quietFlow c.final hquiet_time c.main_ready c.aux_ready c.raw_none
    c.main_below c.aux_below (fun d hd => (hpquiet d hd).le)
  let quiet : Execution θ route c.final (quietAt c.final (15 / 2)) :=
    .cons (.flow waitFlow) (.nil _)
  let tail := (preparedTrace.append c.execution).append quiet
  have hdeliveries : tail.deliveries = [] := by
    simp [tail,preparedTrace,quiet,FirstInputMark.execution,FirstInputSilent.continuation,
      Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries,
      h.deliveries,c.deliveries]
  have hstart : ReadyCoordinates (birthProtocolFirstAfter born) 0 := by
    have h := hborn.ready_coordinates 0 ha
    exact ⟨h.ready,h.charge,h.auxiliary⟩
  have hno : ∀ q, NoArrivalAt tail 0 q := by simp [NoArrivalAt,hdeliveries]
  obtain ⟨pulse⟩ := tail.silent_pulse past hborn hb 0 0 hstart hz f.raw_active
    (fun q hq => f.raw_other 0 q (Or.inr hq)) hno (by change born.time + 15 / 2 ≤ 15 / 2; rw [hborn.1]; linarith)
  obtain ⟨_,hsaturated⟩ := quiet_complete_exists (θ := θ) (route := route) c.final hquiet_time
    c.main_ready c.aux_ready c.raw_none c.main_below c.aux_below hpquiet
  refine ⟨{
    birth := hborn
    sources := hqueue
    final := quietAt c.final (15 / 2)
    continuation := tail
    continuation_transversal := by
      simp [tail, preparedTrace, quiet, FirstInputSilent.continuation,
        Execution.ContactsTransversal, Jump.ContactTransversal,
        f.contacts_transversal, h.contacts_transversal, c.contacts_transversal]
    pulse := pulse
    date := rfl
    saturated := hsaturated
    pending := ?_
    no_later_delivery := hdeliveries
    physical := (past.append tail).physical_invariant hb (hborn.physical_invariant hb)
    raw_valid := (past.append tail).raw_valid hborn.raw_valid
  }⟩
  change c.final.pending = _
  rw [c.pending,hqueueFinal]
  rfl


theorem BirthFirstWeakCycle.deliveries {θ route born} (c : BirthFirstWeakCycle θ route born) :
    c.execution.deliveries = [⟨0,0,0⟩] := by
  change [⟨0,0,0⟩] ++ c.continuation.deliveries = [⟨0,0,0⟩]
  rw [c.no_later_delivery]
  rfl

theorem BirthFirstWeakCycle.emissions {θ route born} (c : BirthFirstWeakCycle θ route born) :
    c.execution.ledger.emissions = [] := by
  have hnil : c.continuation.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event he
    have hc : event.1 = (0 : Fin 1) := Subsingleton.elim _ _
    have hm : event.2 ∈ c.continuation.emissionTimes 0 := by
      apply List.mem_map.mpr
      exact ⟨event,by simp [List.mem_filter,he,hc],rfl⟩
    rw [c.pulse.emissions] at hm
    contradiction
  change [] ++ c.continuation.ledger.emissions = []
  simpa using hnil

theorem BirthFirstWeakCycle.error_dose {θ route born} (c : BirthFirstWeakCycle θ route born) :
    c.execution.ledger.error 0 0 = 3 / 5 := by
  change 0 + c.continuation.ledger.error 0 0 = 3 / 5
  simpa using c.pulse.error_dose

theorem BirthFirstWeakCycle.mark_zero {θ route born} (c : BirthFirstWeakCycle θ route born) (p : Port) :
    c.execution.ledger.mark 0 p = 0 := by
  change 0 + c.continuation.ledger.mark 0 p = 0
  simpa using c.pulse.mark_zero p

theorem BirthFirstWeakCycle.gain_target {θ route born} (c : BirthFirstWeakCycle θ route born) :
    c.final.x 0 (.z 0) = born.x 0 (.z 0) + 3 / 5 := c.pulse.gain_target

theorem BirthFirstWeakCycle.gain_other {θ route born} (c : BirthFirstWeakCycle θ route born)
    (p : Port) (hp : p ≠ 0) : c.final.x 0 (.z p) = born.x 0 (.z p) := c.pulse.gain_other p hp

theorem BirthFirstWeakCycle.recovery_preserved {θ route born} (c : BirthFirstWeakCycle θ route born) :
    c.final.x 0 .b = born.x 0 .b := c.pulse.recovery_preserved

end KernelR.Hybrid
