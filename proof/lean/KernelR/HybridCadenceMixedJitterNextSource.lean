import KernelR.HybridCadenceMixedResponse
import KernelR.HybridCadenceHighFireExistence
import KernelR.HybridLocalFutureFrame

/-! A real mixed response supports a next source at any gap at least3.8.
Only its actual prefix through ERROR completion is retained, then its physical
READY relaxation is constructed directly at H. The nominal four-unit wait is
not used, and the positive residual charge and energy are never reset. -/
namespace KernelR.Hybrid

def cadenceMixedJitterLocalState (s : Snapshot 1) : Snapshot 1 := {s with pending := []}

structure CadenceMixedJitterNextSource (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (H : ℝ) (later : List (Delivery 1)) where
  mixed : CadenceMixedResponse θ (cadenceMixedJitterLocalState s) p
  active : Execution θ (fun _ _ => []) (cadenceMixedJitterLocalState s) mixed.errorEnd.final
  active_state : active = mixed.markPrefix.execution.append (mixed.reopened.execution.append
    (mixed.errorStart.execution.append mixed.errorEnd.execution))
  active_reconstruct : mixed.execution = active.append mixed.wait
  quietFlow : Flow θ mixed.errorEnd.final (quietAt mixed.errorEnd.final H)
  quiet : Execution θ (fun _ _ => []) mixed.errorEnd.final (quietAt mixed.errorEnd.final H)
  quiet_reconstruct : quiet = .cons (.flow quietFlow) (.nil _)
  offline : Execution θ (fun _ _ => []) (cadenceMixedJitterLocalState s) (quietAt mixed.errorEnd.final H)
  offline_reconstruct : offline = active.append quiet
  pulse : CadenceMixedPulse offline 0 p
  before : Snapshot 1
  before_state : before = appendPending (quietAt mixed.errorEnd.final H) (⟨0,p,H⟩ :: later)
  framed : Execution θ (fun _ _ => []) s before
  framed_ledger : framed.ledger = offline.ledger
  final : Snapshot 1
  final_state : final = {setRaw before 0 p (some before.time) with pending := later}
  arrival : Jump (fun _ _ => []) before final
  execution : Execution θ (fun _ _ => []) s final
  reconstruct : execution = framed.append (.cons (.jump arrival) (.nil _))
  date : final.time = H
  values : final.x = (quietAt mixed.errorEnd.final H).x
  coordinates : CadenceReadyCoordinates final 0 (8 / 25)
  charge_lower : 1 / 10 ≤ final.x 0 .q
  raw_active : final.raw 0 p = some H
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gain_target : final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → final.x 0 (.z q) = s.x 0 (.z q)
  gain_log : Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤ final.x 0 (.z p) ∧
    final.x 0 (.z p) ≤ Real.log (3 / 10) + 12 / 5 + 1 / 100000
  high_gain : 16 / 5 ≤ Real.exp (final.x 0 (.z p)) ∧ Real.exp (final.x 0 (.z p)) ≤ 7 / 2
  recovery_gain : final.x 0 .b = s.x 0 .b + 1 / 10
  recovery_band : 37999 / 100000 ≤ final.x 0 .b ∧ final.x 0 .b ≤ 38001 / 100000
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨0,p,H⟩]
  error_target : execution.ledger.error 0 p = 3 / 5
  error_other : ∀ q, q ≠ p → execution.ledger.error 0 q = 0
  mark_target : execution.ledger.mark 0 p = 1 / 10
  mark_other : ∀ q, q ≠ p → execution.ledger.mark 0 q = 0
  recovery_dose : execution.ledger.recovery 0 = 1 / 10
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution H

theorem cadence_mixed_jitter_next_source_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hm : s.main 0 = .slow)
    (hq : 61 / 500 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 7 / 50)
    (hB : 27999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 28001 / 100000)
    (ha : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = ⟨0,p,H⟩ :: later) (hgap : s.time + 19 / 5 ≤ H)
    (hLater : ∀ d ∈ later, H < d.due) :
    Nonempty (CadenceMixedJitterNextSource θ s p H later) := by
  let s0 := cadenceMixedJitterLocalState s
  have hf0 : PhysicalInvariant θ s0 := ⟨hf.region,hf.gain_cap,hf.recovery_cap,hf.reserve⟩
  obtain ⟨m⟩ := cadence_mixed_response_exists hb s0 p hf0 hv hm hq hB ha hz hr ho
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  let active := m.markPrefix.execution.append (m.reopened.execution.append
    (m.errorStart.execution.append m.errorEnd.execution))
  have hReconstruct : m.execution = active.append m.wait := by
    simp only [active,Execution.append_assoc,m.reconstruct]
  have heActive : active.ledger.emissions = [] := by
    simp only [active,Execution.emissions_append,m.markPrefix.emissions,m.reopened.emissions,
      m.errorStart.emissions,m.errorEnd.emissions,List.nil_append]
  have hdActive : active.deliveries = [] := by
    simp only [active,Execution.deliveries_append,m.markPrefix.deliveries,m.reopened.deliveries,
      m.errorStart.deliveries,m.errorEnd.deliveries,List.nil_append]
  have hDuration : errorTailDuration θ m.errorStart.final 0 p = Real.log 4 / (θ 0).le p := by
    simp only [errorTailDuration,m.errorStart.sensor_charge]
    norm_num
  have hBudget : m.markPrefix.final.time - s.time + Real.log 8 / (θ 0).ls p +
      Real.log 4 / (θ 0).le p < 419 / 300 := m.markPrefix.sensor_budget
  have hErrorEnd : m.errorEnd.final.time < s.time + 419 / 300 := by
    rw [m.errorEnd.date,hDuration,m.errorStart.date]
    linarith [hBudget]
  have hEnd : m.errorEnd.final.time < H := by linarith [hErrorEnd]
  have hEmpty : m.errorEnd.final.pending = [] := by
    rw [m.errorEnd.pending,m.errorStart.pending,m.reopened.pending,m.markPrefix.pending]
    rfl
  let flow : Flow θ m.errorEnd.final (quietAt m.errorEnd.final H) :=
    quietFlow m.errorEnd.final hEnd m.errorEnd.main_ready m.errorEnd.aux_ready m.errorEnd.raw_none
      m.errorEnd.main_below m.errorEnd.aux_below
      (by intro d hd; rw [hEmpty] at hd; contradiction)
  let quiet : Execution θ (fun _ _ => []) m.errorEnd.final (quietAt m.errorEnd.final H) :=
    .cons (.flow flow) (.nil _)
  let offline := active.append quiet
  have heOffline : offline.ledger.emissions = [] := by rw [Execution.emissions_append,heActive]; rfl
  have hdOffline : offline.deliveries = [] := by rw [Execution.deliveries_append,hdActive]; rfl
  obtain ⟨pulse⟩ := offline.cadence_mixed_pulse hb hf0 hv 0 p hm hq hB ha hz hr ho
    (by intro q; simp [NoArrivalAt,hdOffline]) hgap
  let future : List (Delivery 1) := ⟨0,p,H⟩ :: later
  obtain ⟨framed0,hFrame,hFrameDel⟩ := offline.appendFuture_emptyRoute future
    (by intro d hd; rcases List.mem_cons.mp hd with he | hd
        · subst d; exact le_rfl
        · exact (hLater d hd).le)
  have hSource : s = appendPending s0 future := by
    simp only [s0,cadenceMixedJitterLocalState,appendPending,future,List.nil_append]
    rw [← hqueue]
  let before := appendPending (quietAt m.errorEnd.final H) future
  let framed : Execution θ (fun _ _ => []) s before := framed0.cast_source hSource
  have hFramedLedger : framed.ledger = offline.ledger := (framed0.cast_source_ledger hSource).trans hFrame
  have heFramed : framed.ledger.emissions = [] := (congrArg (fun L : Ledger 1 => L.emissions) hFramedLedger).trans heOffline
  have hdFramed : framed.deliveries = [] := (framed0.cast_source_deliveries hSource).trans (hFrameDel.trans hdOffline)
  have hBeforeQueue : before.pending = [] ++ (⟨0,p,H⟩ : Delivery 1) :: later := by
    change m.errorEnd.final.pending ++ future = _
    rw [hEmpty]
  let final : Snapshot 1 := {setRaw before 0 p (some before.time) with pending := later}
  let arrival : Jump (fun _ _ => []) before final := .arrive before ⟨0,p,H⟩ [] later hBeforeQueue rfl (m.errorEnd.raw_none 0 p)
  let trace := framed.append (.cons (.jump arrival) (.nil _))
  have hLow : 1 / 10 ≤ final.x 0 .q := pulse.charge.1
  have hCoordinates : CadenceReadyCoordinates final 0 (8 / 25) :=
    ⟨pulse.ready,⟨by linarith [hLow],pulse.charge_cadence⟩,pulse.auxiliary⟩
  have hRaw : final.raw 0 p = some H := by simp [final,setRaw,before,appendPending,quietAt]
  have hOther (q : Port) (hq : q ≠ p) : final.raw 0 q = none := by
    change (setRaw before 0 p (some before.time)).raw 0 q = none
    rw [raw_update_other _ _ _ _ _ _ (Or.inr hq)]
    exact m.errorEnd.raw_none 0 q
  have hGainTarget : final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5 := pulse.gain_target
  have hGainOther : ∀ q, q ≠ p → final.x 0 (.z q) = s.x 0 (.z q) := pulse.gain_other
  have hGainLog : Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤ final.x 0 (.z p) ∧
      final.x 0 (.z p) ≤ Real.log (3 / 10) + 12 / 5 + 1 / 100000 := by
    rw [hGainTarget]
    constructor <;> linarith [hz.1,hz.2]
  have hRecovery : final.x 0 .b = s.x 0 .b + 1 / 10 := pulse.recovery_gain
  have heTrace : trace.ledger.emissions = [] := by
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [trace,Execution.emissions_append,heFramed,Execution.ledger,Move.ledger,hj,
      Ledger.add,Ledger.zero,List.nil_append]
  have hdTrace : trace.deliveries = [⟨0,p,H⟩] := by
    have hj : arrival.deliveries = [⟨0,p,H⟩] := rfl
    simp only [trace,Execution.deliveries_append,hdFramed,Execution.deliveries,Move.deliveries,hj,List.nil_append,List.append_nil]
  have hError : trace.ledger.error 0 p = 3 / 5 := by
    have h := trace.gain_balance 0 p
    rw [hGainTarget] at h; linarith
  have hErrorOther (q : Port) (hq : q ≠ p) : trace.ledger.error 0 q = 0 := by
    have h := trace.gain_balance 0 q
    rw [hGainOther q hq] at h; linarith
  have hMarkEq (q : Port) : trace.ledger.mark 0 q = offline.ledger.mark 0 q := by
    have h := congrArg (fun L : Ledger 1 => L.mark 0 q) hFramedLedger
    have hj : arrival.ledger.mark 0 q = 0 := rfl
    change (framed.append (.cons (.jump arrival) (.nil _))).ledger.mark 0 q = _
    rw [Execution.mark_append,h]
    simp only [Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,hj,add_zero]
  have hRecoveryDose : trace.ledger.recovery 0 = 1 / 10 := by
    have h := trace.recovery_balance 0
    rw [hRecovery] at h; linarith
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := hLater
  have hComplete : CompleteThrough trace H := by
    refine ⟨rfl,?_,hLater⟩
    intro u; apply BeforeGuards.no_jump
    · constructor
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [hCoordinates.ready]
        linarith [hCoordinates.charge.2]
      · intro j q
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [(hCoordinates.auxiliary q).1]
        linarith [(hCoordinates.auxiliary q).2.2]
    · intro j q origin hraw
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        have ho : origin = H := Option.some.inj (hraw.symm.trans hRaw)
        rw [ho]
        change H < H + 1
        linarith
      · rw [hOther q hq] at hraw; contradiction
    · exact hFuture
  refine ⟨{
    mixed := m, active := active, active_state := rfl, active_reconstruct := hReconstruct
    quietFlow := flow, quiet := quiet, quiet_reconstruct := rfl
    offline := offline, offline_reconstruct := rfl, pulse := pulse
    before := before, before_state := rfl, framed := framed, framed_ledger := hFramedLedger
    final := final, final_state := rfl, arrival := arrival, execution := trace, reconstruct := rfl
    date := rfl, values := rfl, coordinates := hCoordinates, charge_lower := pulse.charge.1
    raw_active := hRaw, raw_other := hOther, pending := rfl
    gain_target := hGainTarget, gain_other := hGainOther, gain_log := hGainLog
    high_gain := cadence_four_dose_gain_bounds hGainLog, recovery_gain := hRecovery
    recovery_band := ?_, emissions := heTrace, deliveries := hdTrace
    error_target := hError, error_other := hErrorOther
    mark_target := (hMarkEq p).trans pulse.mark_case.mark_dose
    mark_other := fun q hq => (hMarkEq q).trans (pulse.mark_case.mark_other q hq)
    recovery_dose := hRecoveryDose
    physical := trace.physical_invariant hb hf, raw_valid := trace.raw_valid hv, complete := hComplete
  }⟩
  rw [hRecovery]
  constructor <;> linarith [hB.1,hB.2]

end KernelR.Hybrid
