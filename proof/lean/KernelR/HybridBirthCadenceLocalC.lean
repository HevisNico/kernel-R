import KernelR.HybridBirthCadenceLocalCTail
import KernelR.HybridAutonomousCellProjection

/-! The full autonomous C trace starts at the actual639.9 network state.
Its prefix is extracted from the constructed global execution through660;
the actual C660 coordinates then start the constructed local tail. This
one-cell execution does not advance A or B beyond the global660 witness. -/
namespace KernelR.Hybrid

private theorem local_snapshot_ext {a b : Snapshot 1}
    (ht : a.time=b.time) (hx : a.x=b.x) (hm : a.main=b.main)
    (ha : a.aux=b.aux) (hr : a.raw=b.raw) (hp : a.pending=b.pending) : a=b := by
  cases a; cases b; simp_all only

private theorem double_succ_queue (Q : List (Delivery 1)) :
    cellQueue (2:Fin 3) ((Q.map Delivery.succ).map Delivery.succ)=Q := by
  induction Q with
  | nil => rfl
  | cons d Q ih =>
    rcases d with ⟨j,p,time⟩
    have hj : j=(0:Fin 1) := Subsingleton.elim _ _
    subst j
    simpa [cellQueue,Delivery.atCell,Delivery.succ] using congrArg (List.cons (⟨0,p,time⟩ : Delivery 1)) ih

private theorem view_double_prepend (c b a : Snapshot 1) :
    ((c.prependQuiet b).prependQuiet a).autonomousView (2:Fin 3)=c := by
  apply local_snapshot_ext
  · rfl
  · funext j coord
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    rfl
  · funext j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    rfl
  · funext j q
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    rfl
  · funext j q
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    rfl
  · exact double_succ_queue c.pending

private theorem cell_queue_source_train {n} (i : Fin n) (p : Port) (start gap : ℝ) (count : ℕ) :
    cellQueue i (sourceTrain i p start gap count)=sourceTrain 0 p start gap count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [sourceTrain_succ,sourceTrain_succ]
    simpa only [cellQueue,List.filterMap_cons,Delivery.atCell,ite_true] using
      congrArg (List.cons (⟨0,p,start⟩ : Delivery 1)) (ih (start+gap))

private noncomputable def local_finish_at {θ route s u v} (e : @Execution 1 θ route s u) (h : u=v) :
    Execution θ route s v := h ▸ e

private theorem local_finish_at_ledger {θ route s u v} (e : @Execution 1 θ route s u) (h : u=v) :
    (local_finish_at e h).ledger=e.ledger := by subst v; rfl

private theorem local_finish_at_deliveries {θ route s u v} (e : @Execution 1 θ route s u) (h : u=v) :
    (local_finish_at e h).deliveries=e.deliveries := by subst v; rfl

namespace ConstructedCadenceFirstMarkReturn
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

/-- The projected global C660 state is exactly its already-constructed local
source state, including all physical coordinates and all nineteen tokens. -/
theorem local_c_source_projection : c.final.autonomousView (2:Fin 3)=c.localCSource := by
  change c.mark.final.autonomousView (2:Fin 3)=c.mark.localSource.final
  rw [c.mark.final_state]
  exact view_double_prepend _ _ _

theorem local_c_prefix_calendar : c.execution.emissionTimes 2=[c.wave.cadence.wire.fire.final.time] := by
  rw [c.emission_times,c.wave.emission_times_c]

theorem local_c_prefix_deliveries : cellQueue (2:Fin 3) c.execution.deliveries=sourceTrain 0 0 640 4 6 := by
  simp only [c.reconstruct,Execution.deliveries_append,c.source.deliveries,c.mark.deliveries,
    c.wave.reconstruct,c.wave.cadence.reconstruct,c.wave.cadence.warmup.deliveries,
    c.wave.cadence.wire.deliveries,c.wave.relay.deliveries,c.wave.firstA.deliveries]
  norm_num [cellQueue,Delivery.atCell,sourceTrain,List.filterMap_cons,List.filterMap_nil]

end ConstructedCadenceFirstMarkReturn

structure ConstructedCadenceLocalC {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward) where
  projection : AutonomousCellProjection c.execution 2
  tail : LocalCadenceTail (fun _ : Fin 1 => freshC) c.localCSource
  prefixExecution : Execution (fun _ : Fin 1 => freshC) (fun _ _ => [])
    (c.wave.cadence.teaching.final.autonomousView 2) c.localCSource
  prefix_ledger : prefixExecution.ledger=projection.execution.ledger
  prefix_deliveries : prefixExecution.deliveries=sourceTrain 0 0 640 4 6
  prefix_calendar : prefixExecution.emissionTimes 0=[c.wave.cadence.wire.fire.final.time]
  execution : Execution (fun _ : Fin 1 => freshC) (fun _ _ => [])
    (c.wave.cadence.teaching.final.autonomousView 2) tail.final
  reconstruct : execution=prefixExecution.append tail.execution

/-- Extract C's actual global prefix, then use the exact C660 endpoint. No
reconstructed C640/652 response or reaching-execution premise is supplied. -/
theorem constructed_cadence_local_c_exists {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward ε}
    (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
      forward backward delay cascadeForward cascadeBackward)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    Nonempty (ConstructedCadenceLocalC c) := by
  have hNo : NoIncoming (cadenceRouter cascadeForward cascadeBackward) (2:Fin 3) := by
    intro j time d hd
    exact cadenceRouter.closed_to_c cascadeForward cascadeBackward j time d hd
  obtain ⟨projection⟩ := c.execution.autonomous_cell_exists 2 hNo
  obtain ⟨tail⟩ := c.local_c_tail_exists hb
  let prefixExecution : Execution (fun _ : Fin 1 => freshC) (fun _ _ => [])
      (c.wave.cadence.teaching.final.autonomousView 2) c.localCSource :=
    local_finish_at projection.execution c.local_c_source_projection
  have hledger : prefixExecution.ledger=projection.execution.ledger := local_finish_at_ledger _ _
  have hcalendar : prefixExecution.emissionTimes 0=[c.wave.cadence.wire.fire.final.time] := by
    change (prefixExecution.ledger.emissions.filter (fun ev => ev.1=0)).map Prod.snd=_
    rw [hledger]
    exact projection.emission_times.trans c.local_c_prefix_calendar
  have hdeliveries : prefixExecution.deliveries=sourceTrain 0 0 640 4 6 :=
    (local_finish_at_deliveries projection.execution c.local_c_source_projection).trans
      (projection.deliveries.trans c.local_c_prefix_deliveries)
  exact ⟨{
    projection:=projection,tail:=tail,prefixExecution:=prefixExecution,prefix_ledger:=hledger
    prefix_deliveries:=hdeliveries,prefix_calendar:=hcalendar
    execution:=prefixExecution.append tail.execution,reconstruct:=rfl
  }⟩

namespace ConstructedCadenceFirstMarkReturn
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  (c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward)

theorem local_c_full_exists {ε}
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε) :
    Nonempty (ConstructedCadenceLocalC c) := constructed_cadence_local_c_exists c hb

end ConstructedCadenceFirstMarkReturn

namespace ConstructedCadenceLocalC
variable {θ born freshB freshC newbornB newbornC forward backward delay cascadeForward cascadeBackward}
  {c : ConstructedCadenceFirstMarkReturn θ born freshB freshC newbornB newbornC
    forward backward delay cascadeForward cascadeBackward} (full : ConstructedCadenceLocalC c)

noncomputable abbrev final : Snapshot 1 := full.tail.final

theorem source_date : (c.wave.cadence.teaching.final.autonomousView 2).time=6399/10 :=
  c.wave.cadence.teaching.date

theorem source_pending : (c.wave.cadence.teaching.final.autonomousView 2).pending=sourceTrain 0 0 640 4 25 := by
  change cellQueue (2:Fin 3) c.wave.cadence.teaching.final.pending=_
  rw [c.wave.cadence.teaching.pending]
  exact cell_queue_source_train _ _ _ _ _

theorem calendar : full.execution.emissionTimes 0=
    [c.wave.cadence.wire.fire.final.time,full.tail.second.fire.final.time]++full.tail.high.execution.emissionTimes 0 := by
  rw [full.reconstruct,Execution.emissionTimes_append,full.prefix_calendar,full.tail.calendar]
  rfl

theorem emission_count : (full.execution.emissionTimes 0).length=20 := by
  rw [full.reconstruct,Execution.emissionTimes_append,List.length_append,full.prefix_calendar,full.tail.emission_count]
  rfl

theorem deliveries : full.execution.deliveries=sourceTrain 0 0 640 4 25 := by
  rw [full.reconstruct,Execution.deliveries_append,full.prefix_deliveries,full.tail.deliveries]
  norm_num [sourceTrain]

theorem date : full.final.time=7899/10 := full.tail.date

theorem ready (j : Fin 1) : ReadyCoordinates full.final j := full.tail.ready j

theorem charge : full.final.x 0 .q=1/10 := full.tail.charge

theorem raw_none (j : Fin 1) (p : Port) : full.final.raw j p=none := full.tail.raw_none j p

theorem pending : full.final.pending=[] := full.tail.pending

theorem c_gain_own : full.final.x 0 (.z 0)=newbornC.x (.z 0)+12/5 := full.tail.c_gain_own

theorem c_recovery_own : full.final.x 0 .b=newbornC.x .b+3/10 := full.tail.c_recovery_own

theorem physical : PhysicalInvariant (fun _ : Fin 1 => freshC) full.final := full.tail.physical

theorem raw_valid : RawValid full.final := full.tail.raw_valid

theorem complete : CompleteThrough full.execution (7899/10) := by
  simpa only [CompleteThrough] using full.tail.complete

/-- Terminal energy is the actual ODE endpoint of the attached local tail. -/
theorem energy_actual : full.final.x 0 .energy=full.tail.final.x 0 .energy := rfl

end ConstructedCadenceLocalC
end KernelR.Hybrid
