import KernelR.HybridResponseMarginInput
import KernelR.HybridErrorCompletion
import KernelR.HybridCadenceWeakStages
import KernelR.HybridResidualLatency

/-! Actual period-four weak responses with stage-specific carried charge.
Every ODE segment, sensor jump, RAW expiry, and next arrival is constructed. -/
namespace KernelR.Hybrid
open Set

structure CadenceWeakResponse (θ : Fin 1 → Parameters) (route : Router 1)
    (s : Snapshot 1) (p : Port) (k : Fin 3) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  date : final.time = s.time + 4
  initial_ready : s.main 0 = .ready
  pulse : CadenceSilentPulse execution 0 p (cadenceWeakOutputCap k)
  pending : final.pending = s.pending
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  sensorFinal : Snapshot 1
  sensorExecution : Execution θ route s sensorFinal
  sensor_done : sensorFinal.time < s.time + 419 / 300
  waitFlow : Flow θ sensorFinal final
  reconstruct : execution = sensorExecution.append (.cons (.flow waitFlow) (.nil _))
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Finite scalar stage bounds discharge the guards of newly constructed
MARK/SILENT/ERROR paths. The real source queue may be due at the endpoint. -/
theorem cadence_weak_response_exists {θ ε route} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (k : Fin 3)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (cadenceWeakInputCap k))
    (hz : s.x 0 (.z p) ≤ Real.log (3 / 10) + (3 / 5) * (k.val : ℝ) + 1 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hp : ∀ d ∈ s.pending, s.time + 4 ≤ d.due) :
    Nonempty (CadenceWeakResponse θ route s p k) := by
  have hcap : 1 / 10 ≤ cadenceWeakInputCap k := by
    fin_cases k <;> norm_num [cadenceWeakInputCap]
  have hG : 0 ≤ cadenceWeakDriveCap k := by
    fin_cases k <;> norm_num [cadenceWeakDriveCap]
  have hPeak : cadenceWeakInputCap k + cadenceWeakDriveCap k * (16 / 25) ≤ 24 / 25 := by
    fin_cases k <;> norm_num [cadenceWeakInputCap,cadenceWeakDriveCap]
  have hg : Real.exp (s.x 0 (.z p)) ≤ cadenceWeakDriveCap k :=
    cadenceWeak_raw_gain_upper k (by linarith)
  have hmargin : ∀ t, s.time ≤ t →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t ≤ 24 / 25 := by
    intro t ht
    exact (readyPulse_uniform_bound hs.charge.2 hcap hg hG ht).trans hPeak
  have hguard : ∀ t, s.time ≤ t →
      readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z p))) s.time t < 1 := by
    intro t ht
    linarith [hmargin t ht]
  have hm : ∀ j, s.main j = .ready := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hs.ready
  have ha : ∀ j q, s.aux j q = .ready := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (hs.auxiliary q).1
  have hq : ∀ j, s.x j .q < 1 := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hcapUpper : cadenceWeakInputCap k < 1 := by
      fin_cases k <;> norm_num [cadenceWeakInputCap]
    linarith [hs.charge.2]
  have hx : ∀ j q, s.x j (.m q) < 1 := by
    intro j q
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    linarith [(hs.auxiliary q).2.2]
  have hother : ∀ j q, j ≠ (0 : Fin 1) ∨ q ≠ p → s.raw j q = none := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  obtain ⟨f⟩ := first_input_mark_of_response_margin_exists s hb 0 p hm ha hr hother hq hx
    hguard (hs.auxiliary p).2 (fun d hd => by linarith [hp d hd])
  obtain ⟨g⟩ := f.first_silent_of_response_margin_exists hb hguard
    (fun d hd => by linarith [hp d hd])
  obtain ⟨h⟩ := g.first_error_exists_of_margin route hb hmargin
    (fun d hd => by linarith [hp d hd])
  have hnominal : s.x 0 (.z p) ≤ Real.log (6 / 5) + 1 / 1000 :=
    cadenceWeak_below_fast_nominal k hz
  have hqueue : h.final.pending = s.pending := h.pending
  have hgain (j : Fin 1) (q : Port) : h.final.x j (.z q) = s.x j (.z q) := h.gain_preserved j q
  let preparedTrace := ((f.execution route).append (g.continuation route)).append h.execution
  have hphysical : PhysicalInvariant θ h.final := preparedTrace.physical_invariant hb hf
  have hheadroom : h.final.x 0 (.z p) + 8 * (h.final.x 0 (.m p) - 1 / 40) <
      Real.log ((θ 0).cap p) := by
    rw [hgain,h.sensor_charge]
    linarith [hb.fast_nominal_headroom 0 p,hnominal]
  have hduration : h.final.time + errorTailDuration θ h.final 0 p =
      s.time + f.latency + auxCycleDuration (θ 0) p := by
    rw [h.error_date_exact,g.date]
    simp only [FirstInputMark.silentDate,errorTailDuration,h.sensor_charge]
    norm_num only [show (40 : ℝ) * (1 / 10) = 4 by norm_num]
    dsimp [auxCycleDuration]
    ring
  have hschedule := hb.first_cycle_schedule 0 p ⟨f.early,f.deadline⟩
  have hfinish : s.time + 1 < h.final.time + errorTailDuration θ h.final 0 p := by
    rw [hduration]; linarith [hschedule.2.2.2.2.1]
  have hfinish_upper : h.final.time + errorTailDuration θ h.final 0 p < s.time + 419 / 300 := by
    rw [hduration]; linarith [hschedule.2.2.2.2.2]
  have hfuture : ∀ d ∈ h.final.pending,
      h.final.time + errorTailDuration θ h.final 0 p < d.due := by
    intro d hd; rw [hqueue] at hd; linarith [hp d hd]
  have hm0 : 1 / 40 < h.final.x 0 (.m p) := by rw [h.sensor_charge]; norm_num
  have hmu : h.final.x 0 (.m p) ≤ 1 / 10 := h.sensor_charge.le
  have hcompletion : Nonempty (ErrorCompletion θ route h.final 0 p) := by
    rcases h.raw_option with ⟨hr,hactive⟩ | ⟨hr,hafter⟩
    · exact error_completion_with_raw_tail hb h.final 0 p hphysical h.main_ready h.initialmode
        h.aux_other s.time hr h.raw_other hm0 hmu hheadroom (h.error_date_lower hb).le
        hactive hfinish h.charge_margin h.main_below h.aux_below hfuture
    · have hnone : ∀ j q, h.final.raw j q = none := by
        intro j q
        by_cases hh : j = 0 ∧ q = p
        · rcases hh with ⟨rfl,rfl⟩; exact hr
        · exact h.raw_other j q (by tauto)
      exact error_completion_without_raw hb h.final 0 p hphysical h.main_ready h.initialmode
        h.aux_other hnone hm0 hmu hheadroom h.main_below h.aux_below hfuture
  obtain ⟨c⟩ := hcompletion
  have hquiet_time : c.final.time < s.time + 4 := by rw [c.date]; linarith
  have hpquiet : ∀ d ∈ c.final.pending, s.time + 4 ≤ d.due := by
    intro d hd; rw [c.pending,hqueue] at hd; exact hp d hd
  let waitFlow : Flow θ c.final (quietAt c.final (s.time + 4)) :=
    quietFlow c.final hquiet_time c.main_ready c.aux_ready c.raw_none c.main_below c.aux_below
      hpquiet
  let quiet : Execution θ route c.final (quietAt c.final (s.time + 4)) :=
    .cons (.flow waitFlow) (.nil _)
  let trace := (preparedTrace.append c.execution).append quiet
  have hdeliveries : trace.deliveries = [] := by
    simp [trace,preparedTrace,quiet,FirstInputMark.execution,FirstInputSilent.continuation,
      Execution.deliveries_append,Execution.deliveries,Move.deliveries,Jump.deliveries,
      h.deliveries,c.deliveries]
  have hemissions : trace.ledger.emissions = [] := by
    simp [trace,preparedTrace,quiet,FirstInputMark.execution,FirstInputSilent.continuation,
      Execution.emissions_append,Execution.ledger,Move.ledger,Flow.ledger,Jump.ledger,
      Ledger.add,Ledger.zero,h.emissions,c.emissions]
  have hno : ∀ q, NoArrivalAt trace 0 q := by simp [NoArrivalAt,hdeliveries]
  obtain ⟨pulse⟩ := trace.cadence_weak_stage hb hf hv 0 p k hs hz hr ho hno
    (by change s.time + 4 ≤ s.time + 4; exact le_rfl)
  exact ⟨{
    contacts_transversal := by
      simp [trace, preparedTrace, quiet, Execution.ContactsTransversal,
        f.contacts_transversal, g.continuation_contacts_transversal,
        h.contacts_transversal, c.contacts_transversal]
    final := quietAt c.final (s.time + 4), execution := trace, date := rfl, initial_ready := hs.ready
    pulse := pulse, pending := c.pending.trans hqueue
    emissions := hemissions, deliveries := hdeliveries
    sensorFinal := c.final, sensorExecution := preparedTrace.append c.execution
    sensor_done := by rw [c.date]; exact hfinish_upper
    waitFlow := waitFlow, reconstruct := rfl
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv
  }⟩

namespace CadenceWeakResponse
variable {θ route s p k} (c : CadenceWeakResponse θ route s p k)

theorem charge_lower (h : 1 / 10 ≤ s.x 0 .q) : 1 / 10 ≤ c.final.x 0 .q := by
  have hm := c.execution.ready_states_of_no_emissions 0 c.initial_ready
    (by simp [Execution.emissionTimes,c.emissions])
  exact c.execution.ready_charge_ge_rest 0 (c.execution.allStates_main_flows 0 .ready hm) h

end CadenceWeakResponse

structure CadenceWeakNextSource {θ route s p k} (c : CadenceWeakResponse θ route s p k)
    (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ route s final
  arrival : Jump route c.final final
  reconstruct : execution = c.execution.append (.cons (.jump arrival) (.nil _))
  contacts_transversal : execution.ContactsTransversal
  date : final.time = s.time + 4
  values : final.x = c.final.x
  coordinates : CadenceReadyCoordinates final 0 (cadenceWeakOutputCap k)
  gain_target : final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → final.x 0 (.z q) = s.x 0 (.z q)
  recovery : final.x 0 .b = s.x 0 .b
  raw_active : final.raw 0 p = some final.time
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,p,s.time + 4⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (s.time + 4)

/-- Consume the existing exact next-source occurrence after the constructed
period-four response; remaining source multiplicities and order are retained. -/
theorem cadence_weak_next_source_exists {θ ε route s p k}
    (c : CadenceWeakResponse θ route s p k) (hb : PhysicalBox θ ε)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (later : List (Delivery 1)) (hqueue : s.pending = ⟨0,p,s.time + 4⟩ :: later)
    (hlater : ∀ d ∈ later, s.time + 4 < d.due) :
    Nonempty (CadenceWeakNextSource c later) := by
  let final : Snapshot 1 := {setRaw c.final 0 p (some c.final.time) with pending := later}
  let arrival : Jump route c.final final := .arrive c.final ⟨0,p,s.time + 4⟩ [] later
    (c.pending.trans hqueue) c.date.symm (c.pulse.raw_finished p)
  have haEm : arrival.ledger.emissions = [] := rfl
  have haDel : arrival.deliveries = [⟨0,p,s.time + 4⟩] := rfl
  let trace := c.execution.append (.cons (.jump arrival) (.nil _))
  have hraw : final.raw 0 p = some final.time := by simp [final,setRaw]
  have hother : ∀ q, q ≠ p → final.raw 0 q = none := by
    intro q hq
    simp [final,setRaw,hq,c.pulse.raw_finished]
  have hcoords : CadenceReadyCoordinates final 0 (cadenceWeakOutputCap k) :=
    ⟨c.pulse.coordinates.ready,c.pulse.coordinates.charge,c.pulse.coordinates.auxiliary⟩
  have hfuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    change d ∈ later at hd
    change c.final.time < d.due
    rw [c.date]
    exact hlater d hd
  have hcomplete : CompleteThrough trace (s.time + 4) := by
    refine ⟨c.date,?_,?_⟩
    · intro u
      apply BeforeGuards.no_jump
      · constructor
        · intro i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          rw [hcoords.ready]
          have hcap : cadenceWeakOutputCap k < 1 := by
            fin_cases k <;> norm_num [cadenceWeakOutputCap]
          linarith [hcoords.charge.2]
        · intro i q
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          rw [(hcoords.auxiliary q).1]
          linarith [(hcoords.auxiliary q).2.2]
      · intro i q origin hr
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        by_cases hq : q = p
        · subst q
          have ho : origin = final.time := Option.some.inj (hr.symm.trans hraw)
          rw [ho]; linarith
        · rw [hother q hq] at hr; contradiction
      · exact hfuture
    · intro d hd
      rw [← c.date]
      exact hfuture d hd
  exact ⟨{
    contacts_transversal := by
      simp [trace, arrival, Execution.ContactsTransversal, Jump.ContactTransversal, c.contacts_transversal]
    final := final, execution := trace, arrival := arrival, reconstruct := rfl, date := c.date, values := rfl, coordinates := hcoords
    gain_target := c.pulse.gain_target, gain_other := c.pulse.gain_other
    recovery := c.pulse.recovery_preserved, raw_active := hraw, raw_other := hother
    pending := rfl, emissions := by
      simp only [trace,Execution.emissions_append,c.emissions,Execution.ledger,Move.ledger,
        haEm,Ledger.add,Ledger.zero,List.nil_append]
    deliveries := by
      simp only [trace,Execution.deliveries_append,c.deliveries,Execution.deliveries,Move.deliveries,
        haDel,List.nil_append,List.append_nil]
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv
    complete := hcomplete
  }⟩

end KernelR.Hybrid
