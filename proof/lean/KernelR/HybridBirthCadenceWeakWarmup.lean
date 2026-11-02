import KernelR.HybridConstructedCadenceStart
import KernelR.HybridConstructedCadenceWeakWarmup
import KernelR.HybridQuietHeadNeutralProduct

/-! The real three-cell cadence prelude through source652. The original
quiet A/B paths and C's carried charge are retained under the open router. -/
namespace KernelR.Hybrid

structure ConstructedCadenceWarmup {θ born freshB freshC newbornB newbornC forward backward delay}
    (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay)
    (cascadeForward cascadeBackward : ℝ → ℝ) where
  start : ConstructedCadenceStart c cascadeForward cascadeBackward
  localWarmup : ConstructedCadenceWeakWarmup (fun _ : Fin 1 => freshC) (fun _ _ => []) start.sC
  final : Snapshot 3
  final_state : final = (localWarmup.final.prependQuiet
    (quietAt start.quietB localWarmup.final.time)).prependQuiet
    (quietAt start.quietA localWarmup.final.time)
  execution : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cadenceRouter cascadeForward cascadeBackward) c.final final
  date : final.time = 652
  c_coordinates : CadenceReadyCoordinates final 2 (3 / 10)
  c_charge_lower : 1 / 10 ≤ final.x 2 .q
  a_prepared : PreparedSection final 0
  b_prepared : PreparedSection final 1
  a_charge : final.x 0 .q = 1 / 10
  b_charge : final.x 1 .q = 1 / 10
  raw_active : final.raw 2 0 = some final.time
  raw_other : ∀ i q, i ≠ 2 ∨ q ≠ 0 → final.raw i q = none
  pending : final.pending = sourceTrain 2 0 656 4 21
  c_gain_target : final.x 2 (.z 0) = c.final.x 2 (.z 0) + 9 / 5
  gains_other : ∀ i q, i ≠ 2 ∨ q ≠ 0 → final.x i (.z q) = c.final.x i (.z q)
  recovery : ∀ i, final.x i .b = c.final.x i .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = [⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩,⟨2,0,652⟩]
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough execution 652

theorem constructed_cadence_warmup_exists {θ born freshB freshC newbornB newbornC forward backward delay ε}
    (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (cascadeForward cascadeBackward : ℝ → ℝ) :
    Nonempty (ConstructedCadenceWarmup c cascadeForward cascadeBackward) := by
  obtain ⟨start⟩ := constructed_cadence_start_exists c hb cascadeForward cascadeBackward
  obtain ⟨warm⟩ := constructed_cadence_weak_warmup_exists (route := fun _ _ => []) hb.extend_new
    start.sC start.c_physical start.c_raw_valid start.c_date (start.c_prepared 0) (start.c_charge 0)
    start.c_gain_low.2 start.c_raw_active start.c_raw_other start.c_pending
  obtain ⟨pair,hePair,hdPair⟩ := warm.execution.prepend_quiet_neutral warm.emissions
    (fun _ : Fin 1 => freshB) start.quietB (by rw [start.c_date,start.quiet_b_date])
    (fun i => (start.quiet_b_prepared i).ready_coordinates) start.quiet_b_raw_none start.quiet_b_pending
    (fun _ _ => [])
  obtain ⟨woven,heWoven,hdWoven⟩ := pair.prepend_quiet_neutral hePair θ start.quietA
    (by change start.sC.time = start.quietA.time; rw [start.c_date,start.quiet_a_date])
    (fun i => (start.quiet_a_prepared i).ready_coordinates) start.quiet_a_raw_none start.quiet_a_pending
    (cadenceRouter cascadeForward cascadeBackward)
  let final : Snapshot 3 := (warm.final.prependQuiet (quietAt start.quietB warm.final.time)).prependQuiet
    (quietAt start.quietA warm.final.time)
  let lifted : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter cascadeForward cascadeBackward) start.final final :=
    (woven.cast_source start.reconstruct.symm).cast_parameters
    (ConstructedCadenceStart.parameters_nested (θ := θ) (freshB := freshB) (freshC := freshC))
  let execution : Execution (extendParameters (extendParameters θ freshB) freshC)
      (cadenceRouter cascadeForward cascadeBackward) c.final final := start.execution.append lifted
  have hledger : lifted.ledger = woven.ledger :=
    ((woven.cast_source start.reconstruct.symm).cast_parameters_ledger
      (ConstructedCadenceStart.parameters_nested (θ := θ) (freshB := freshB) (freshC := freshC))).trans
      (woven.cast_source_ledger start.reconstruct.symm)
  have hdel : lifted.deliveries = woven.deliveries :=
    ((woven.cast_source start.reconstruct.symm).cast_parameters_deliveries
      (ConstructedCadenceStart.parameters_nested (θ := θ) (freshB := freshB) (freshC := freshC))).trans
      (woven.cast_source_deliveries start.reconstruct.symm)
  have hT : (640 : ℝ) ≤ warm.final.time := by rw [warm.final_eq,warm.date]; norm_num
  have hAready : ReadyCoordinates (quietAt start.quietA warm.final.time) 0 :=
    quietAt_ready_coordinates start.quietA 0
    (start.quiet_a_prepared 0).ready_coordinates (by rw [start.quiet_a_date]; exact hT)
  have hBready : ReadyCoordinates (quietAt start.quietB warm.final.time) 0 :=
    quietAt_ready_coordinates start.quietB 0
    (start.quiet_b_prepared 0).ready_coordinates (by rw [start.quiet_b_date]; exact hT)
  have hA : PreparedSection final 0 :=
    ⟨hAready.ready,hAready.charge,(start.quiet_a_prepared 0).recovery,hAready.auxiliary⟩
  have hB : PreparedSection final 1 :=
    ⟨hBready.ready,hBready.charge,(start.quiet_b_prepared 0).recovery,hBready.auxiliary⟩
  have hC : CadenceReadyCoordinates final 2 (3 / 10) :=
    ⟨warm.coordinates.ready,warm.coordinates.charge,warm.coordinates.auxiliary⟩
  have hRawOther : ∀ i q, i ≠ 2 ∨ q ≠ 0 → final.raw i q = none := by
    intro i q h
    fin_cases i
    · exact start.quiet_a_raw_none 0 q
    · exact start.quiet_b_raw_none 0 q
    · exact warm.raw_other q (by simpa using h)
  have hPending : final.pending = sourceTrain 2 0 656 4 21 := by
    change (warm.final.pending.map Delivery.succ).map Delivery.succ = _
    rw [warm.final_eq,warm.pending]
    simp [sourceTrain,Delivery.succ]
  have hDate : final.time = 652 := warm.date
  have hGains : ∀ i q, i ≠ 2 ∨ q ≠ 0 → final.x i (.z q) = c.final.x i (.z q) := by
    intro i q h
    fin_cases i
    · exact start.gains 0 q
    · exact start.gains 1 q
    · change warm.final.x 0 (.z q) = c.final.x 2 (.z q)
      rw [warm.final_eq,warm.gain_other q (by simpa using h)]
      exact start.c_gain_own q
  have hRecovery : ∀ i, final.x i .b = c.final.x i .b := by
    intro i
    fin_cases i
    · exact start.recovery 0
    · exact start.recovery 1
    · change warm.final.x 0 .b = c.final.x 2 .b
      rw [warm.final_eq,warm.recovery]
      exact start.recovery 2
  have hEm : execution.ledger.emissions = [] := by
    rw [Execution.emissions_append,start.emissions,hledger,heWoven]
    rfl
  have hDel : execution.deliveries = [⟨2,0,640⟩,⟨2,0,644⟩,⟨2,0,648⟩,⟨2,0,652⟩] := by
    rw [Execution.deliveries_append,start.deliveries,hdel,hdWoven,hdPair,warm.deliveries]
    rfl
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hd
    rw [hPending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hDate]
    change (652 : ℝ) < 656 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have hmodes : ∀ i : Fin 3, final.main i = .ready := by
    intro i
    fin_cases i
    · exact hA.ready
    · exact hB.ready
    · exact hC.ready
  have haux : ∀ (i : Fin 3) q, final.aux i q = .ready := by
    intro i q
    fin_cases i
    · exact (hA.auxiliary q).1
    · exact (hB.auxiliary q).1
    · exact (hC.auxiliary q).1
  have hqguard : ∀ i : Fin 3, final.x i .q < 1 := by
    intro i
    fin_cases i
    · exact lt_of_le_of_lt hA.charge.2 (by norm_num)
    · exact lt_of_le_of_lt hB.charge.2 (by norm_num)
    · exact lt_of_le_of_lt hC.charge.2 (by norm_num)
  have hmguard : ∀ (i : Fin 3) q, final.x i (.m q) < 1 := by
    intro i q
    fin_cases i
    · exact lt_of_le_of_lt (hA.auxiliary q).2.2 (by norm_num)
    · exact lt_of_le_of_lt (hB.auxiliary q).2.2 (by norm_num)
    · exact lt_of_le_of_lt (hC.auxiliary q).2.2 (by norm_num)
  have hguards : BeforeGuards final final.x := by
    constructor
    · intro i; rw [hmodes i]; exact hqguard i
    · intro i q; rw [haux i q]; exact hmguard i q
  have hRawStrict : ∀ (i : Fin 3) q origin, final.raw i q = some origin → final.time < origin + 1 := by
    intro i q origin hr
    by_cases h : i = 2 ∧ q = 0
    · rcases h with ⟨rfl,rfl⟩
      have ha : final.raw 2 0 = some final.time := warm.raw_active
      have heq : origin = final.time := Option.some.inj (hr.symm.trans ha)
      rw [heq]
      linarith
    · rw [hRawOther i q (by tauto)] at hr
      contradiction
  have hComplete : CompleteThrough execution 652 := by
    refine ⟨hDate,fun u => hguards.no_jump hRawStrict hFuture u,?_⟩
    intro d hd
    have h := hFuture d hd
    rw [hDate] at h
    exact h
  refine ⟨{
    start := start, localWarmup := warm, final := final, final_state := rfl
    execution := execution, date := hDate
    c_coordinates := hC, c_charge_lower := warm.charge_lower, a_prepared := hA, b_prepared := hB
    a_charge := ?_, b_charge := ?_, raw_active := warm.raw_active, raw_other := hRawOther
    pending := hPending, c_gain_target := ?_, gains_other := hGains, recovery := hRecovery
    emissions := hEm, deliveries := hDel
    physical := execution.physical_invariant hb c.physical
    raw_valid := execution.raw_valid c.raw_valid, complete := hComplete
  }⟩
  · change relax (1 / 2) (1 / 10) (start.quietA.x 0 .q) start.quietA.time warm.final.time = _
    have hq : start.quietA.x 0 .q = 1 / 10 := start.charge 0
    rw [hq]
    simp [relax]
  · change relax (1 / 2) (1 / 10) (start.quietB.x 0 .q) start.quietB.time warm.final.time = _
    have hq : start.quietB.x 0 .q = 1 / 10 := start.charge 1
    rw [hq]
    simp [relax]
  · change warm.final.x 0 (.z 0) = c.final.x 2 (.z 0) + 9 / 5
    rw [warm.final_eq,warm.gain_target,start.c_gain_own]

end KernelR.Hybrid
