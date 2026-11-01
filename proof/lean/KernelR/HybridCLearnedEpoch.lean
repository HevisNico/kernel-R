import KernelR.HybridPortCoupledLearnedTrain
import KernelR.HybridCBirthActivePair

/-! Thirteen actual learned B/C responses from source504, followed by
physical quiet evolution to639.9. C's twenty-five own sources remain queued. -/
namespace KernelR.Hybrid

structure CLearnedEpoch (θB θC : Fin 1 → Parameters)
    (delay : ℝ → ℝ) (source : Snapshot 2) where
  source_date : source.time = 504
  train : PortCoupledLearnedTrain θB θC (cBirthPairRouter delay) source 2 1 delay 12
    (sourceTrain 1 0 640 4 25)
  train_date : train.final.time = 608
  final : Snapshot 2
  wait : Execution (extendParameters θB (θC 0)) (cBirthPairRouter delay) train.final final
  execution : Execution (extendParameters θB (θC 0)) (cBirthPairRouter delay) source final
  reconstruct : execution = train.execution.append wait
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  date : final.time = 6399 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  pending : final.pending = sourceTrain 1 0 640 4 25
  gains : ∀ i q, final.x i (.z q) = source.x i (.z q)
  recovery : ∀ i, final.x i .b = source.x i .b
  physical : PhysicalInvariant (extendParameters θB (θC 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (6399 / 10)

theorem c_learned_epoch_exists {θB θC ε}
    (hb : @PhysicalBox 2 (extendParameters θB (θC 0)) ε) (source : Snapshot 2)
    (hf : PhysicalInvariant (extendParameters θB (θC 0)) source) (hv : RawValid source)
    (ht : source.time = 504)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q = 1 / 10)
    (hGB : 9 / 5 ≤ Real.exp (source.x 0 (.z 2)) ∧ Real.exp (source.x 0 (.z 2)) ≤ 2)
    (hGC : 9 / 5 ≤ Real.exp (source.x 1 (.z 1)) ∧ Real.exp (source.x 1 (.z 1)) ≤ 11 / 5)
    (hr : source.raw 0 2 = some source.time)
    (ho : ∀ i q, i ≠ 0 ∨ q ≠ 2 → source.raw i q = none)
    (hqueue : source.pending = sourceTrain 0 2 512 8 12 ++ sourceTrain 1 0 640 4 25)
    (delay : ℝ → ℝ)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ delay time ∧ delay time ≤ 2 / 5) :
    Nonempty (CLearnedEpoch θB θC delay source) := by
  have htrainQueue : source.pending =
      sourceTrain 0 2 (source.time + 8) 8 12 ++ sourceTrain 1 0 640 4 25 := by
    rw [ht]
    norm_num
    exact hqueue
  have hroute : ∀ F, 480 ≤ F → F < 601 →
      cBirthPairRouter delay 0 F = [⟨1,1,F + delay F⟩] := by
    intro F hF hF'
    simp [cBirthPairRouter,cBirthPairContact,Contact.route,Contact.token,hF,
      show F < (630 : ℝ) by linarith]
  have hclosed : ∀ time, (480 : ℝ) ≤ time → time ≤ 608 → cBirthPairRouter delay 1 time = [] := by
    intro time _ _
    simp [cBirthPairRouter,cBirthPairContact,Contact.route]
  obtain ⟨tr⟩ := port_coupled_learned_train_exists hb source 12 (sourceTrain 1 0 640 4 25)
    hf hv (by rw [ht]; norm_num) hs hq hGB hGC hr ho htrainQueue
    (by
      intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      rw [ht]
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
    hdelay hroute hclosed
  have htrainDate : tr.final.time = (608 : ℝ) := by rw [tr.date,ht]; norm_num
  have hwait : tr.final.time < (6399 / 10 : ℝ) := by rw [htrainDate]; norm_num
  have hm : ∀ i, tr.final.main i = .ready := fun i => (tr.prepared i).ready
  have ha : ∀ i q, tr.final.aux i q = .ready := fun i q => ((tr.prepared i).auxiliary q).1
  have hqFinal : ∀ i, tr.final.x i .q < 1 := by intro i; rw [tr.charge]; norm_num
  have hx : ∀ i q, tr.final.x i (.m q) < 1 := by
    intro i q
    linarith [((tr.prepared i).auxiliary q).2.2]
  have hp : ∀ d ∈ tr.final.pending, (6399 / 10 : ℝ) < d.due := by
    intro d hd
    rw [tr.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let flow : Flow (extendParameters θB (θC 0)) tr.final (quietAt tr.final (6399 / 10)) :=
    quietFlow tr.final hwait hm ha tr.raw_none hqFinal hx (fun d hd => (hp d hd).le)
  let wait : Execution (extendParameters θB (θC 0)) (cBirthPairRouter delay)
      tr.final (quietAt tr.final (6399 / 10)) := .cons (.flow flow) (.nil _)
  let execution := tr.execution.append wait
  obtain ⟨_,hc⟩ := quiet_complete_exists (θ := extendParameters θB (θC 0))
    (route := cBirthPairRouter delay) tr.final hwait hm ha tr.raw_none hqFinal hx hp
  have hready : ∀ i, ReadyCoordinates (quietAt tr.final (6399 / 10)) i :=
    fun i => quietAt_ready_coordinates tr.final i (tr.ready i) hwait.le
  refine ⟨{
    source_date := ht, train := tr, train_date := htrainDate
    final := quietAt tr.final (6399 / 10), wait := wait, execution := execution, reconstruct := rfl
    wait_emissions := rfl, wait_deliveries := rfl, date := rfl
    prepared := fun i => ⟨(hready i).ready,(hready i).charge,(tr.prepared i).recovery,(hready i).auxiliary⟩
    charge := ?_, raw_none := tr.raw_none, pending := tr.pending
    gains := tr.gains, recovery := tr.recovery
    physical := wait.physical_invariant hb tr.physical
    raw_valid := wait.raw_valid tr.raw_valid, complete := hc
  }⟩
  intro i
  change relax (1 / 2) (1 / 10) (tr.final.x i .q) tr.final.time (6399 / 10) = _
  rw [tr.charge]
  simp [relax]

namespace CLearnedEpoch
variable {θB θC delay source} (e : CLearnedEpoch θB θC delay source)

theorem ready : ∀ i, ReadyCoordinates e.final i := fun i => (e.prepared i).ready_coordinates

theorem b_emission_count : (e.execution.emissionTimes 0).length = 13 := by
  have hw : e.wait.emissionTimes 0 = [] := by simp [Execution.emissionTimes,e.wait_emissions]
  rw [e.reconstruct,Execution.emissionTimes_append,hw,List.append_nil]
  exact e.train.a_emission_count

theorem c_emission_count : (e.execution.emissionTimes 1).length = 13 := by
  have hw : e.wait.emissionTimes 1 = [] := by simp [Execution.emissionTimes,e.wait_emissions]
  rw [e.reconstruct,Execution.emissionTimes_append,hw,List.append_nil]
  exact e.train.b_emission_count

theorem pending_length : e.final.pending.length = 25 := by
  rw [e.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem b_deliveries : e.execution.cellDeliveries 0 = sourceTrain 0 2 512 8 12 := by
  have hw : e.wait.cellDeliveries 0 = [] := by simp [Execution.cellDeliveries,e.wait_deliveries]
  rw [e.reconstruct,Execution.cellDeliveries_append,hw,List.append_nil,e.train.a_deliveries,e.source_date]
  norm_num

theorem c_deliveries : e.execution.cellDeliveries 1 =
    e.train.wireTimes.map (fun time => (⟨1,1,time⟩ : Delivery 2)) := by
  have hw : e.wait.cellDeliveries 1 = [] := by simp [Execution.cellDeliveries,e.wait_deliveries]
  rw [e.reconstruct,Execution.cellDeliveries_append,hw,List.append_nil]
  exact e.train.b_deliveries

theorem wire_count : e.train.wireTimes.length = 13 := e.train.wire_count

theorem wire_provenance (time : ℝ) (ht : time ∈ e.train.wireTimes) :
    ∃ F ∈ e.execution.emissionTimes 0, time = F + delay F := by
  obtain ⟨F,hF,hdate⟩ := e.train.wire_provenance time ht
  refine ⟨F,?_,hdate⟩
  rw [e.reconstruct,Execution.emissionTimes_append]
  exact List.mem_append_left _ hF

theorem error_zero (i : Fin 2) (q : Port) : e.execution.ledger.error i q = 0 := by
  have h := e.execution.gain_balance i q
  rw [e.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : e.execution.ledger.recovery i = 0 := by
  have h := e.execution.recovery_balance i
  rw [e.recovery] at h
  linarith

theorem wait_mark_zero (i : Fin 2) (q : Port) : e.wait.ledger.mark i q = 0 := by
  have hquiet := e.wait.aux_ready_without_input_band i q ((e.train.prepared i).auxiliary q).1
    ((e.train.prepared i).auxiliary q).2.2 (e.train.raw_none i q)
    (by simp [NoArrivalAt,e.wait_deliveries])
  exact e.wait.mark_zero_aux i q .ready (by decide)
    (e.wait.allStates_aux_flows i q .ready hquiet)

theorem mark_zero (i : Fin 2) (q : Port) : e.execution.ledger.mark i q = 0 := by
  rw [e.reconstruct,Execution.mark_append,e.train.mark_zero,e.wait_mark_zero,zero_add]

end CLearnedEpoch
end KernelR.Hybrid
