import KernelR.HybridReverseCoupledLearnedTrain

/-! The final nine real reciprocal learned cycles and the physical quiet
continuation to459.9. No reaching execution or emitted calendar is supplied. -/
namespace KernelR.Hybrid

structure ReverseLearnedEpoch (θA θB : Fin 1 → Parameters)
    (forward backward : ℝ → ℝ) (source : Snapshot 2) where
  source_date : source.time = 376
  train : ReverseCoupledLearnedTrain θA (θB 0) forward backward source 8 (sourceTrain 1 2 480 8 16)
  train_date : train.final.time = 448
  final : Snapshot 2
  wait : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) train.final final
  execution : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward) source final
  reconstruct : execution = train.execution.append wait
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  date : final.time = 4599 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i p, final.raw i p = none
  pending : final.pending = sourceTrain 1 2 480 8 16
  gains : ∀ i p, final.x i (.z p) = source.x i (.z p)
  recovery : ∀ i, final.x i .b = source.x i .b
  physical : PhysicalInvariant (extendParameters θA (θB 0)) final
  raw_valid : RawValid final
  complete : CompleteThrough execution (4599 / 10)

/-- Eight queued B occurrences plus the already active source376 produce
nine actual coupled responses. The separate sixteen-source train is retained. -/
theorem reverse_learned_epoch_exists {θA θB ε}
    (hb : @PhysicalBox 2 (extendParameters θA (θB 0)) ε) (source : Snapshot 2)
    (hf : PhysicalInvariant (extendParameters θA (θB 0)) source) (hv : RawValid source)
    (ht : source.time = 376)
    (hs : ∀ i, PreparedSection source i) (hq : ∀ i, source.x i .q = 1 / 10)
    (hGA : 9 / 5 ≤ Real.exp (source.x 0 (.z 2)) ∧ Real.exp (source.x 0 (.z 2)) ≤ 2)
    (hGB : 9 / 5 ≤ Real.exp (source.x 1 (.z 2)) ∧ Real.exp (source.x 1 (.z 2)) ≤ 2)
    (hr : source.raw 1 2 = some source.time)
    (ho : ∀ i p, i ≠ 1 ∨ p ≠ 2 → source.raw i p = none)
    (hqueue : source.pending = sourceTrain 1 2 384 8 8 ++ sourceTrain 1 2 480 8 16)
    (forward backward : ℝ → ℝ)
    (hback : ∀ t, (3 / 10 : ℝ) ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (ReverseLearnedEpoch θA θB forward backward source) := by
  have htrainQueue : source.pending =
      sourceTrain 1 2 (source.time + 8) 8 8 ++ sourceTrain 1 2 480 8 16 := by
    rw [ht]
    norm_num
    exact hqueue
  obtain ⟨tr⟩ := reverse_coupled_learned_train_exists hb source 8 (sourceTrain 1 2 480 8 16)
    hf hv (by rw [ht]; norm_num) hs hq hGA hGB hr ho htrainQueue
    (by
      intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      rw [ht]
      dsimp
      nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
    forward backward hback
  have htrainDate : tr.final.time = (448 : ℝ) := by rw [tr.date,ht]; norm_num
  have hwait : tr.final.time < (4599 / 10 : ℝ) := by rw [htrainDate]; norm_num
  have hm : ∀ i, tr.final.main i = .ready := fun i => (tr.prepared i).ready
  have ha : ∀ i p, tr.final.aux i p = .ready := fun i p => ((tr.prepared i).auxiliary p).1
  have hqFinal : ∀ i, tr.final.x i .q < 1 := by intro i; rw [tr.charge]; norm_num
  have hx : ∀ i p, tr.final.x i (.m p) < 1 := by
    intro i p
    linarith [((tr.prepared i).auxiliary p).2.2]
  have hp : ∀ d ∈ tr.final.pending, (4599 / 10 : ℝ) < d.due := by
    intro d hd
    rw [tr.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    dsimp
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  let flow : Flow (extendParameters θA (θB 0)) tr.final (quietAt tr.final (4599 / 10)) :=
    quietFlow tr.final hwait hm ha tr.raw_none hqFinal hx (fun d hd => (hp d hd).le)
  let wait : Execution (extendParameters θA (θB 0)) (reciprocalEntryRouter forward backward)
      tr.final (quietAt tr.final (4599 / 10)) := .cons (.flow flow) (.nil _)
  let e := tr.execution.append wait
  obtain ⟨_,hc⟩ := quiet_complete_exists (θ := extendParameters θA (θB 0))
    (route := reciprocalEntryRouter forward backward) tr.final hwait hm ha tr.raw_none hqFinal hx hp
  have hready : ∀ i, ReadyCoordinates (quietAt tr.final (4599 / 10)) i :=
    fun i => quietAt_ready_coordinates tr.final i (tr.ready i) hwait.le
  refine ⟨{
    source_date := ht, train := tr, train_date := htrainDate
    final := quietAt tr.final (4599 / 10), wait := wait, execution := e, reconstruct := rfl
    wait_emissions := rfl, wait_deliveries := rfl, date := rfl
    prepared := fun i => ⟨(hready i).ready,(hready i).charge,(tr.prepared i).recovery,(hready i).auxiliary⟩
    charge := ?_, raw_none := tr.raw_none, pending := tr.pending
    gains := tr.gains, recovery := tr.recovery
    physical := wait.physical_invariant hb tr.physical
    raw_valid := wait.raw_valid tr.raw_valid, complete := hc
  }⟩
  intro i
  change relax (1 / 2) (1 / 10) (tr.final.x i .q) tr.final.time (4599 / 10) = _
  rw [tr.charge]
  simp [relax]

namespace ReverseLearnedEpoch
variable {θA θB forward backward source} (e : ReverseLearnedEpoch θA θB forward backward source)

theorem ready : ∀ i, ReadyCoordinates e.final i := fun i => (e.prepared i).ready_coordinates

theorem a_emission_count : (e.execution.emissionTimes 0).length = 9 := by
  have hw : e.wait.emissionTimes 0 = [] := by simp [Execution.emissionTimes,e.wait_emissions]
  rw [e.reconstruct,Execution.emissionTimes_append,hw,List.append_nil]
  exact e.train.a_emission_count

theorem b_emission_count : (e.execution.emissionTimes 1).length = 9 := by
  have hw : e.wait.emissionTimes 1 = [] := by simp [Execution.emissionTimes,e.wait_emissions]
  rw [e.reconstruct,Execution.emissionTimes_append,hw,List.append_nil]
  exact e.train.b_emission_count

theorem pending_length : e.final.pending.length = 16 := by
  rw [e.pending]
  simp [sourceTrain]

theorem b_deliveries : e.execution.cellDeliveries 1 = sourceTrain 1 2 384 8 8 := by
  have hw : e.wait.cellDeliveries 1 = [] := by simp [Execution.cellDeliveries,e.wait_deliveries]
  rw [e.reconstruct,Execution.cellDeliveries_append,hw,List.append_nil,e.train.b_deliveries,e.source_date]
  norm_num

theorem a_deliveries : e.execution.cellDeliveries 0 =
    e.train.wireTimes.map (fun t => (⟨0,2,t⟩ : Delivery 2)) := by
  have hw : e.wait.cellDeliveries 0 = [] := by simp [Execution.cellDeliveries,e.wait_deliveries]
  rw [e.reconstruct,Execution.cellDeliveries_append,hw,List.append_nil]
  exact e.train.a_deliveries

theorem wire_count : e.train.wireTimes.length = 9 := e.train.wire_count

theorem wire_provenance (t : ℝ) (ht : t ∈ e.train.wireTimes) :
    ∃ F ∈ e.execution.emissionTimes 1, t = F + backward F := by
  obtain ⟨F,hF,hdate⟩ := e.train.wire_provenance t ht
  refine ⟨F,?_,hdate⟩
  rw [e.reconstruct,Execution.emissionTimes_append]
  exact List.mem_append_left _ hF

theorem error_zero (i : Fin 2) (p : Port) : e.execution.ledger.error i p = 0 := by
  have h := e.execution.gain_balance i p
  rw [e.gains] at h
  linarith

theorem recovery_zero (i : Fin 2) : e.execution.ledger.recovery i = 0 := by
  have h := e.execution.recovery_balance i
  rw [e.recovery] at h
  linarith

theorem wait_mark_zero (i : Fin 2) (p : Port) : e.wait.ledger.mark i p = 0 := by
  have hquiet := e.wait.aux_ready_without_input_band i p ((e.train.prepared i).auxiliary p).1
    ((e.train.prepared i).auxiliary p).2.2 (e.train.raw_none i p)
    (by simp [NoArrivalAt,e.wait_deliveries])
  exact e.wait.mark_zero_aux i p .ready (by decide)
    (e.wait.allStates_aux_flows i p .ready hquiet)

theorem mark_zero (i : Fin 2) (p : Port) : e.execution.ledger.mark i p = 0 := by
  rw [e.reconstruct,Execution.mark_append,e.train.mark_zero,e.wait_mark_zero,zero_add]

end ReverseLearnedEpoch
end KernelR.Hybrid
