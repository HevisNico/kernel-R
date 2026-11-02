import KernelR.HybridCadenceHighCompletion
import KernelR.HybridLocalFutureFrame

/-! An actual high response can serve an independently jittered next source
at least3.8 later. The isolated response is constructed with an empty queue;
its real reopen prefix is followed by a quiet flow to the requested date,
then the original queue is framed along precisely this path. -/
namespace KernelR.Hybrid

/-- Construction metadata; the returned execution starts at the full source. -/
def cadenceHighLocalState (s : Snapshot 1) : Snapshot 1 := {s with pending := []}

structure CadenceHighJitterReadyAt (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (H : ℝ) (future : List (Delivery 1)) where
  fire : CadenceHighFire θ (fun _ _ => []) (cadenceHighLocalState s) 0 p
  completion : CadenceHighCompletion fire
  quietFlow : Flow θ completion.returned.returnState (quietAt completion.returned.returnState H)
  quiet : Execution θ (fun _ _ => []) completion.returned.returnState (quietAt completion.returned.returnState H)
  quiet_reconstruct : quiet = .cons (.flow quietFlow) (.nil _)
  offline : Execution θ (fun _ _ => []) (cadenceHighLocalState s) (quietAt completion.returned.returnState H)
  offline_reconstruct : offline = fire.execution.append
    ((completion.toSlow.append completion.returned.head).append quiet)
  final : Snapshot 1
  final_state : final = appendPending (quietAt completion.returned.returnState H) future
  execution : Execution θ (fun _ _ => []) s final
  framed_ledger : execution.ledger = offline.ledger
  date : final.time = H
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = future
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = [(0,fire.final.time)]
  deliveries : execution.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Neither a reaching execution nor an emitted calendar is a premise. -/
theorem cadence_high_jitter_ready_at_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (future : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (8 / 25)) (hq : 1 / 10 ≤ s.x 0 .q)
    (hg : 16 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 7 / 2)
    (hB : 37999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 38001 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = future) (hgap : s.time + 19 / 5 ≤ H)
    (hFuture : ∀ d ∈ future, H ≤ d.due) :
    Nonempty (CadenceHighJitterReadyAt θ s p H future) := by
  let s0 := cadenceHighLocalState s
  have hf0 : PhysicalInvariant θ s0 := ⟨hf.region,hf.gain_cap,hf.recovery_cap,hf.reserve⟩
  have hs0 : CadenceReadyCoordinates s0 0 (8 / 25) := ⟨hs.ready,hs.charge,hs.auxiliary⟩
  obtain ⟨fire⟩ := cadence_high_fire_exists hb s0 p hf0 hv hs0 hq hg hr ho
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  obtain ⟨done⟩ := fire.high_completion_exists hb hs0 hB ho
    (by intro d hd; change d ∈ ([] : List (Delivery 1)) at hd; contradiction)
  have hEnd : done.returned.returnState.time < H := lt_of_lt_of_le done.return_deadline hgap
  have hReturnEmpty : done.returned.returnState.pending = [] := by
    rw [done.return_pending,fire.pending,List.append_nil]
    rfl
  let flow := quietFlow (θ := θ) done.returned.returnState hEnd
    (fun j => (done.return_ready j).ready)
    (fun j q => ((done.return_ready j).auxiliary q).1) done.return_raw_none
    (fun j => by linarith [(done.return_ready j).charge.2])
    (fun j q => by linarith [((done.return_ready j).auxiliary q).2.2])
    (by intro d hd; rw [hReturnEmpty] at hd; contradiction)
  let quiet : Execution θ (fun _ _ => []) done.returned.returnState
      (quietAt done.returned.returnState H) := .cons (.flow flow) (.nil _)
  let returnPrefix := done.toSlow.append done.returned.head
  have hReturnEm : returnPrefix.ledger.emissions = [] := done.return_emissions
  have hReturnDel : returnPrefix.deliveries = [] := done.return_deliveries
  let offline := fire.execution.append (returnPrefix.append quiet)
  have hOfflineEm : offline.ledger.emissions = [(0,fire.final.time)] := by
    rw [Execution.emissions_append,Execution.emissions_append,fire.emissions,hReturnEm]
    rfl
  have hOfflineDel : offline.deliveries = [] := by
    rw [Execution.deliveries_append,Execution.deliveries_append,fire.deliveries,hReturnDel]
    rfl
  obtain ⟨framed0,hLedger,hDel⟩ := offline.appendFuture_emptyRoute future hFuture
  have hSource : s = appendPending s0 future := by
    simp only [s0,cadenceHighLocalState,appendPending,List.nil_append]
    rw [←hqueue]
  let framed := framed0.cast_source hSource
  let final := appendPending (quietAt done.returned.returnState H) future
  have hFramedLedger : framed.ledger = offline.ledger :=
    (framed0.cast_source_ledger hSource).trans hLedger
  have hReady : ∀ j, ReadyCoordinates final j := by
    intro j
    have h := quietAt_ready_coordinates done.returned.returnState j (done.return_ready j) hEnd.le
    exact ⟨h.ready,h.charge,h.auxiliary⟩
  have hCharge : final.x 0 .q = 1 / 10 := by
    change relax (1 / 2) (1 / 10) (done.returned.returnState.x 0 .q) done.returned.returnState.time H = _
    rw [done.return_charge]
    simp [relax]
  have hGains : ∀ j q, final.x j (.z q) = s.x j (.z q) := fun j q =>
    (done.return_gains j q).trans (fire.gain_preserved j q)
  have hRecovery : ∀ j, final.x j .b = s.x j .b := fun j =>
    (done.return_recovery j).trans (fire.recovery_preserved j)
  refine ⟨{
    fire := fire, completion := done, quietFlow := flow, quiet := quiet, quiet_reconstruct := rfl
    offline := offline, offline_reconstruct := rfl, final := final, final_state := rfl
    execution := framed, framed_ledger := hFramedLedger, date := rfl
    ready := hReady, charge := hCharge, raw_none := done.return_raw_none
    pending := by change done.returned.returnState.pending ++ future = future; rw [hReturnEmpty,List.nil_append]
    gains := hGains, recovery := hRecovery
    emissions := (congrArg (fun L : Ledger 1 => L.emissions) hFramedLedger).trans hOfflineEm
    deliveries := (framed0.cast_source_deliveries hSource).trans (hDel.trans hOfflineDel)
    physical := framed.physical_invariant hb hf, raw_valid := framed.raw_valid hv
  }⟩

structure CadenceHighJitterNextSource (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (p : Port) (H : ℝ) (later : List (Delivery 1)) where
  readyAt : CadenceHighJitterReadyAt θ s p H (⟨0,p,H⟩ :: later)
  final : Snapshot 1
  final_state : final = {setRaw readyAt.final 0 p (some H) with pending := later}
  arrival : Jump (fun _ _ => []) readyAt.final final
  execution : Execution θ (fun _ _ => []) s final
  reconstruct : execution = readyAt.execution.append (.cons (.jump arrival) (.nil _))
  date : final.time = H
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_active : final.raw 0 p = some H
  raw_other : ∀ q, q ≠ p → final.raw 0 q = none
  pending : final.pending = later
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = [(0,readyAt.fire.final.time)]
  deliveries : execution.deliveries = [⟨0,p,H⟩]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution H

theorem cadence_high_jitter_next_source_exists {θ ε} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (H : ℝ) (later : List (Delivery 1))
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hs : CadenceReadyCoordinates s 0 (8 / 25)) (hq : 1 / 10 ≤ s.x 0 .q)
    (hg : 16 / 5 ≤ Real.exp (s.x 0 (.z p)) ∧ Real.exp (s.x 0 (.z p)) ≤ 7 / 2)
    (hB : 37999 / 100000 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 38001 / 100000)
    (hr : s.raw 0 p = some s.time) (ho : ∀ q, q ≠ p → s.raw 0 q = none)
    (hqueue : s.pending = ⟨0,p,H⟩ :: later) (hgap : s.time + 19 / 5 ≤ H)
    (hLater : ∀ d ∈ later, H < d.due) :
    Nonempty (CadenceHighJitterNextSource θ s p H later) := by
  obtain ⟨r⟩ := cadence_high_jitter_ready_at_exists hb s p H _ hf hv hs hq hg hB hr ho hqueue hgap
    (by intro d hd; rcases List.mem_cons.mp hd with h | h
        · subst d; exact le_rfl
        · exact (hLater d h).le)
  let final : Snapshot 1 := {setRaw r.final 0 p (some r.final.time) with pending := later}
  let arrival : Jump (fun _ _ => []) r.final final :=
    .arrive r.final ⟨0,p,H⟩ [] later r.pending r.date.symm (r.raw_none 0 p)
  let execution := r.execution.append (.cons (.jump arrival) (.nil _))
  have hReady : ∀ j, ReadyCoordinates final j := fun j =>
    ⟨(r.ready j).ready,(r.ready j).charge,(r.ready j).auxiliary⟩
  have hRaw : final.raw 0 p = some H := by simp [final,setRaw,r.date]
  have hOther (q : Port) (hq : q ≠ p) : final.raw 0 q = none := by
    simp [final,setRaw,hq,r.raw_none]
  have hEm : execution.ledger.emissions = [(0,r.fire.final.time)] := by
    have hj : arrival.ledger.emissions = [] := rfl
    simp only [execution,Execution.emissions_append,r.emissions,Execution.ledger,Move.ledger,hj,Ledger.add,Ledger.zero,List.append_nil]
  have hDel : execution.deliveries = [⟨0,p,H⟩] := by
    rw [Execution.deliveries_append,r.deliveries]
    rfl
  have hComplete : CompleteThrough execution H := by
    refine ⟨r.date,?_,hLater⟩
    intro u
    apply BeforeGuards.no_jump
    · constructor
      · intro j; rw [(hReady j).ready]; linarith [(hReady j).charge.2]
      · intro j q; rw [((hReady j).auxiliary q).1]; linarith [((hReady j).auxiliary q).2.2]
    · intro j q origin hraw
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      by_cases hq : q = p
      · subst q
        have ho : origin = H := Option.some.inj (hraw.symm.trans hRaw)
        rw [ho]
        change r.final.time < H + 1
        rw [r.date]
        linarith
      · rw [hOther q hq] at hraw; contradiction
    · intro d hd
      change r.final.time < d.due
      rw [r.date]
      exact hLater d hd
  exact ⟨{
    readyAt := r, final := final, final_state := by dsimp [final]; rw [r.date], arrival := arrival
    execution := execution, reconstruct := rfl, date := r.date
    ready := hReady, charge := r.charge, raw_active := hRaw, raw_other := hOther
    pending := rfl, gains := r.gains, recovery := r.recovery, emissions := hEm, deliveries := hDel
    physical := execution.physical_invariant hb hf, raw_valid := execution.raw_valid hv, complete := hComplete
  }⟩

end KernelR.Hybrid
