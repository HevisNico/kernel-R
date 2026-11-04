import KernelR.HybridErrorCompletion
import KernelR.HybridSilentReturn
import KernelR.HybridWeakInputErrorExistence

namespace KernelR.Hybrid
open Set

structure WeakInputCycle {n} (θ : Fin n → Parameters) (route : Router n)
    (s : Snapshot n) (i : Fin n) (p : Port) where
  final : Snapshot n
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  pulse : SilentPulse execution i p
  date : final.time = s.time + 15 / 2
  complete : CompleteThrough execution (s.time + 15 / 2)
  pending : final.pending = s.pending
  deliveries : execution.deliveries = []
  emissions : execution.ledger.emissions = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Construct an actual weak pulse from its current physical section. The
carried charge need only be READY, not in the original narrow birth band. -/
theorem weak_input_cycle_exists {n θ ε route} (s : Snapshot n) (hb : @PhysicalBox n θ ε)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hs : ∀ j, ReadyCoordinates s j)
    (hg : Real.exp (s.x i (.z p)) ≤ 7 / 6)
    (hz : s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : s.raw i p = some s.time)
    (ho : ∀ j q, j ≠ i ∨ q ≠ p → s.raw j q = none)
    (hp : ∀ d ∈ s.pending, s.time + 8 ≤ d.due) :
    Nonempty (WeakInputCycle θ route s i p) := by
  have hm : ∀ j, s.main j = .ready := fun j => (hs j).ready
  have ha : ∀ j q, s.aux j q = .ready := fun j q => ((hs j).auxiliary q).1
  have hq : ∀ j, s.x j .q < 1 := by intro j; linarith [(hs j).charge.2]
  have hx : ∀ j q, s.x j (.m q) < 1 := by intro j q; linarith [((hs j).auxiliary q).2.2]
  obtain ⟨f⟩ := first_input_mark_exists s hb i p hm ha hr ho hq hx (hs i).charge.2
    (by linarith) ((hs i).auxiliary p).2 (by intro d hd; linarith [hp d hd])
  obtain ⟨g⟩ := f.first_silent_exists hb (hs i).charge.2 (by linarith) (by
    intro d hd; linarith [hp d hd])
  obtain ⟨h⟩ := g.weak_first_error_exists route hb (hs i).charge.2 hg (by
    intro d hd; linarith [hp d hd])
  have hqueue : h.final.pending = s.pending := h.pending
  have hgain (j : Fin n) (q : Port) : h.final.x j (.z q) = s.x j (.z q) := h.gain_preserved j q
  let preparedTrace := ((f.execution route).append (g.continuation route)).append h.execution
  have hphysical : PhysicalInvariant θ h.final := preparedTrace.physical_invariant hb hf
  have hheadroom : h.final.x i (.z p) + 8 * (h.final.x i (.m p) - 1 / 40) <
      Real.log ((θ i).cap p) := by
    rw [hgain,h.sensor_charge]
    linarith [hb.fast_nominal_headroom i p]
  have hduration : h.final.time + errorTailDuration θ h.final i p =
      s.time + f.latency + auxCycleDuration (θ i) p := by
    rw [h.error_date_exact,g.date]
    simp only [FirstInputMark.silentDate,errorTailDuration,h.sensor_charge]
    norm_num only [show (40 : ℝ) * (1 / 10) = 4 by norm_num]
    dsimp [auxCycleDuration]
    ring
  have hschedule := hb.first_cycle_schedule i p ⟨f.early,f.deadline⟩
  have hfinish : s.time + 1 < h.final.time + errorTailDuration θ h.final i p := by
    rw [hduration]; linarith [hschedule.2.2.2.2.1]
  have hfinish_upper : h.final.time + errorTailDuration θ h.final i p < s.time + 419 / 300 := by
    rw [hduration]; linarith [hschedule.2.2.2.2.2]
  have hfuture : ∀ d ∈ h.final.pending,
      h.final.time + errorTailDuration θ h.final i p < d.due := by
    intro d hd; rw [hqueue] at hd; linarith [hp d hd]
  have hm0 : 1 / 40 < h.final.x i (.m p) := by rw [h.sensor_charge]; norm_num
  have hmu : h.final.x i (.m p) ≤ 1 / 10 := h.sensor_charge.le
  have hcompletion : Nonempty (ErrorCompletion θ route h.final i p) := by
    rcases h.raw_option with ⟨hr,hactive⟩ | ⟨hr,hafter⟩
    · exact error_completion_with_raw_tail hb h.final i p hphysical h.main_ready h.initialmode
        h.aux_other s.time hr h.raw_other hm0 hmu hheadroom (h.error_date_lower hb).le
        hactive hfinish h.charge_margin h.main_below h.aux_below hfuture
    · have hnone : ∀ j q, h.final.raw j q = none := by
        intro j q
        by_cases hh : j = i ∧ q = p
        · rcases hh with ⟨rfl,rfl⟩; exact hr
        · exact h.raw_other j q (by tauto)
      exact error_completion_without_raw hb h.final i p hphysical h.main_ready h.initialmode
        h.aux_other hnone hm0 hmu hheadroom h.main_below h.aux_below hfuture
  obtain ⟨c⟩ := hcompletion
  have hquiet_time : c.final.time < s.time + 15 / 2 := by rw [c.date]; linarith
  have hpquiet : ∀ d ∈ c.final.pending, s.time + 15 / 2 < d.due := by
    intro d hd; rw [c.pending,hqueue] at hd; linarith [hp d hd]
  let waitFlow : Flow θ c.final (quietAt c.final (s.time + 15 / 2)) :=
    quietFlow c.final hquiet_time c.main_ready c.aux_ready c.raw_none c.main_below c.aux_below
      (fun d hd => (hpquiet d hd).le)
  let quiet : Execution θ route c.final (quietAt c.final (s.time + 15 / 2)) :=
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
  have hno : ∀ q, NoArrivalAt trace i q := by simp [NoArrivalAt,hdeliveries]
  obtain ⟨pulse⟩ := trace.silent_pulse_of_invariant hb hf hv i p (hs i) hz hr
    (fun q hq => ho i q (Or.inr hq)) hno le_rfl
  obtain ⟨_,hsaturated⟩ := quiet_complete_exists (θ := θ) (route := route) c.final hquiet_time
    c.main_ready c.aux_ready c.raw_none c.main_below c.aux_below hpquiet
  refine ⟨{
    final := quietAt c.final (s.time + 15 / 2)
    execution := trace
    contacts_transversal := by
      simp [trace, preparedTrace, quiet, FirstInputSilent.continuation,
        Execution.ContactsTransversal, Jump.ContactTransversal,
        f.contacts_transversal, h.contacts_transversal, c.contacts_transversal]
    pulse := pulse
    date := rfl
    complete := hsaturated
    pending := ?_
    deliveries := hdeliveries
    emissions := hemissions
    physical := trace.physical_invariant hb hf
    raw_valid := trace.raw_valid hv
  }⟩
  change c.final.pending = s.pending
  rw [c.pending,hqueue]

end KernelR.Hybrid
