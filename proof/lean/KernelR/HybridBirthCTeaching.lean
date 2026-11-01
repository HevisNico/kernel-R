import KernelR.HybridCTeachingPair

/-! The original one-cell birth, both real dimension-changing births, and
the constructed three-cell endpoint639.9. No reaching trace is a premise. -/
namespace KernelR.Hybrid

private theorem succ_emission_times (events : List (Fin 2 × ℝ)) (i : Fin 2) :
    (((events.map (fun ev => (ev.1.succ,ev.2))).filter (fun ev => ev.1 = i.succ)).map Prod.snd) =
      ((events.filter (fun ev => ev.1 = i)).map Prod.snd) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    rcases event with ⟨j,time⟩
    by_cases h : j = i
    · subst j; simp [ih]
    · have hn : j.succ ≠ i.succ := by simpa using h
      simp [h,hn,ih]

private theorem head_emission_times (events : List (Fin 2 × ℝ)) :
    (((events.map (fun ev => (ev.1.succ,ev.2))).filter (fun ev => ev.1 = 0)).map Prod.snd) = [] := by
  induction events with
  | nil => rfl
  | cons event events ih => simp [Fin.succ_ne_zero,ih]

structure ConstructedCTeaching (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (freshB freshC : Parameters) (newbornB newbornC : Newborn)
    (forward backward delay : ℝ → ℝ) where
  reverse : ConstructedReverseTeaching θ born freshB newbornB forward backward
  birth : ConstructedCBirth reverse freshC newbornC delay
  weak : CWeakEntry birth
  initial : CFirstLearnedBoundary weak
  preparedPair : CPreparedPair initial
  teaching : CTeachingPair preparedPair
  final : Snapshot 3
  lifted : Execution (extendParameters (extendParameters θ freshB) freshC)
    (cTeachingRouter delay) birth.final final
  final_state : final = teaching.final.prependQuiet (quietAt birth.quietA teaching.final.time)
  lifted_emissions : lifted.ledger.emissions =
    teaching.execution.ledger.emissions.map (fun ev => (ev.1.succ,ev.2))
  lifted_deliveries : lifted.deliveries = teaching.execution.deliveries.map Delivery.succ
  staged : StagedExecution (extendParameters θ freshB) freshC
    (reciprocalEntryRouter forward backward) (cTeachingRouter delay) reverse.final final
  staged_before : HEq staged.before birth.wait
  staged_birth : HEq staged.birth birth.birth
  staged_after : HEq staged.after (birth.staged.after.append lifted)
  date : final.time = 6399 / 10
  prepared : ∀ i, PreparedSection final i
  charge : ∀ i, final.x i .q = 1 / 10
  raw_none : ∀ i q, final.raw i q = none
  pending : final.pending = sourceTrain 2 0 640 4 25
  a_emission_count :
    (reverse.staged.before.emissionTimes 0 ++ reverse.staged.after.emissionTimes 0).length +
      (staged.before.emissionTimes 0).length + (staged.after.emissionTimes 0).length = 38
  b_emission_count : (reverse.staged.after.emissionTimes 1).length +
    (staged.before.emissionTimes 1).length + (staged.after.emissionTimes 1).length = 43
  c_emission_count : (staged.after.emissionTimes 2).length = 14
  a_gain_target : final.x 0 (.z 2) = born.x 0 (.z 2) + 9 / 5
  a_gain_first : final.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  a_gain_other : ∀ q, q ≠ 0 → q ≠ 2 → final.x 0 (.z q) = born.x 0 (.z q)
  b_gain_target : final.x 1 (.z 2) = newbornB.x (.z 2) + 9 / 5
  b_gain_first : final.x 1 (.z 1) = newbornB.x (.z 1) + 3 / 5
  b_gain_other : ∀ q, q ≠ 1 → q ≠ 2 → final.x 1 (.z q) = newbornB.x (.z q)
  c_gain_target : final.x 2 (.z 1) = newbornC.x (.z 1) + 3 / 5
  c_gain_other : ∀ q, q ≠ 1 → final.x 2 (.z q) = newbornC.x (.z q)
  a_recovery : final.x 0 .b = born.x 0 .b + 1 / 10
  b_recovery : final.x 1 .b = newbornB.x .b + 1 / 10
  c_recovery : final.x 2 .b = newbornC.x .b + 1 / 10
  physical : PhysicalInvariant (extendParameters (extendParameters θ freshB) freshC) final
  raw_valid : RawValid final
  complete : CompleteThrough staged.after (6399 / 10)

theorem birth_protocol_c_teaching_exists {θ born freshB freshC ε}
    (hborn : @BirthState 1 born)
    (hb : @PhysicalBox 3 (extendParameters (extendParameters θ freshB) freshC) ε)
    (ha : ∀ q, born.aux 0 q = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (newbornB newbornC : Newborn) (forward backward delay : ℝ → ℝ)
    (hforward : ∀ time, (3 / 10 : ℝ) ≤ forward time ∧ forward time ≤ 2 / 5)
    (hback : ∀ time, (3 / 10 : ℝ) ≤ backward time ∧ backward time ≤ 2 / 5)
    (hdelay : ∀ time, (3 / 10 : ℝ) ≤ delay time ∧ delay time ≤ 2 / 5) :
    Nonempty (ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay) := by
  obtain ⟨reverse⟩ := birth_protocol_reverse_teaching_exists hborn hb.extend_old ha hqueue
    newbornB forward backward hforward hback
  obtain ⟨birth⟩ := constructed_c_birth_exists reverse hb newbornC delay
  obtain ⟨weak⟩ := c_weak_entry_exists birth hb hdelay
  obtain ⟨initial⟩ := c_first_learned_boundary_exists weak hb hdelay
  obtain ⟨prepared⟩ := c_prepared_pair_exists initial hb hdelay
  obtain ⟨teaching⟩ := c_teaching_pair_exists prepared hb hdelay
  obtain ⟨woven,he,hd⟩ := teaching.execution.prepend_quiet θ birth.quietA rfl
    birth.quiet_a_ready birth.quiet_a_raw_none birth.quiet_a_pending
    (cTeachingRouter delay) (cBirthPairRouter_prepend delay)
  let lifted := (woven.cast_source birth.active_pair_reconstruct.symm).cast_parameters
    (cBirthPairParameters_prepend θ freshB freshC)
  let final := teaching.final.prependQuiet (quietAt birth.quietA teaching.final.time)
  have hledger : lifted.ledger = woven.ledger := by
    simp only [lifted,Execution.cast_parameters_ledger,Execution.cast_source_ledger]
  have hdel : lifted.deliveries = woven.deliveries := by
    simp only [lifted,Execution.cast_parameters_deliveries,Execution.cast_source_deliveries]
  have hEm : lifted.ledger.emissions =
      teaching.execution.ledger.emissions.map (fun ev => (ev.1.succ,ev.2)) := by rw [hledger,he]
  have hDel : lifted.deliveries = teaching.execution.deliveries.map Delivery.succ := by rw [hdel,hd]
  let staged : StagedExecution (extendParameters θ freshB) freshC
      (reciprocalEntryRouter forward backward) (cTeachingRouter delay) reverse.final final :=
    { birth.staged with after := birth.staged.after.append lifted }
  have hL0 : lifted.emissionTimes 0 = [] := by
    simp only [Execution.emissionTimes,hEm]
    exact head_emission_times _
  have hLS (i : Fin 2) : lifted.emissionTimes i.succ = teaching.execution.emissionTimes i := by
    simp only [Execution.emissionTimes,hEm]
    exact succ_emission_times _ i
  have hBefore (i : Fin 2) : staged.before.emissionTimes i = [] := birth.before_emission_times i
  have hAfter0 : staged.after.emissionTimes 0 = [] := by
    simp only [staged,Execution.emissionTimes_append,birth.after_emission_times,hL0,List.nil_append]
  have hAfterB : (staged.after.emissionTimes 1).length = 16 := by
    change ((birth.staged.after.append lifted).emissionTimes (0 : Fin 2).succ).length = _
    rw [Execution.emissionTimes_append,birth.after_emission_times,List.nil_append,hLS]
    exact teaching.b_emission_count
  have hAfterC : (staged.after.emissionTimes 2).length = 14 := by
    change ((birth.staged.after.append lifted).emissionTimes (1 : Fin 2).succ).length = _
    rw [Execution.emissionTimes_append,birth.after_emission_times,List.nil_append,hLS]
    exact teaching.c_emission_count
  have hquietTime : birth.quietA.time ≤ teaching.final.time := by
    rw [birth.quiet_a_date,teaching.date]
    norm_num
  have hquietReady := quietAt_ready_coordinates birth.quietA 0 (birth.quiet_a_ready 0) hquietTime
  have hPrepared : ∀ i, PreparedSection final i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hquietReady.ready,hquietReady.charge,(birth.quiet_a_prepared 0).recovery,
        hquietReady.auxiliary⟩
    · exact ⟨(teaching.prepared j).ready,(teaching.prepared j).charge,
        (teaching.prepared j).recovery,(teaching.prepared j).auxiliary⟩
  have hCharge : ∀ i, final.x i .q = 1 / 10 := by
    intro i
    refine Fin.cases ?_ (fun j => teaching.charge j) i
    change relax (1 / 2) (1 / 10) (birth.quietA.x 0 .q) birth.quietA.time teaching.final.time = _
    rw [birth.quiet_a_charge]
    simp [relax]
  have hRaw : ∀ i q, final.raw i q = none := by
    intro i q
    exact Fin.cases (birth.quiet_a_raw_none 0 q) (fun j => teaching.raw_none j q) i
  have hPending : final.pending = sourceTrain 2 0 640 4 25 := by
    change teaching.final.pending.map Delivery.succ = _
    rw [teaching.pending]
    simp [sourceTrain,Delivery.succ]
  have hDate : final.time = 6399 / 10 := teaching.date
  have hA (q : Port) : final.x 0 (.z q) = reverse.final.x 0 (.z q) := birth.old_gains 0 q
  have hB (q : Port) : final.x 1 (.z q) = reverse.final.x 1 (.z q) :=
    (teaching.sender_gains q).trans (birth.old_gains 1 q)
  have hRecA : final.x 0 .b = reverse.final.x 0 .b := birth.old_recovery 0
  have hRecB : final.x 1 .b = reverse.final.x 1 .b :=
    teaching.sender_recovery.trans (birth.old_recovery 1)
  have hFuture : ∀ d ∈ final.pending, final.time < d.due := by
    intro d hdue
    rw [hPending] at hdue
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hdue
    rw [hDate]
    change (6399 / 10 : ℝ) < 640 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  have hComplete : CompleteThrough staged.after (6399 / 10) := by
    refine ⟨hDate,?_,?_⟩
    · apply ready_no_jump final (fun i => (hPrepared i).ready)
        (fun i q => ((hPrepared i).auxiliary q).1) hRaw
      · intro i; rw [hCharge]; norm_num
      · intro i q; linarith [((hPrepared i).auxiliary q).2.2]
      · exact hFuture
    · intro d hdue
      have h := hFuture d hdue
      rw [hDate] at h
      exact h
  refine ⟨{
    reverse := reverse, birth := birth, weak := weak, initial := initial
    preparedPair := prepared, teaching := teaching, final := final, lifted := lifted
    final_state := rfl, lifted_emissions := hEm, lifted_deliveries := hDel
    staged := staged, staged_before := HEq.rfl, staged_birth := HEq.rfl, staged_after := HEq.rfl
    date := hDate, prepared := hPrepared, charge := hCharge, raw_none := hRaw, pending := hPending
    a_emission_count := ?_, b_emission_count := ?_, c_emission_count := hAfterC
    a_gain_target := (hA 2).trans reverse.a_gain_target
    a_gain_first := (hA 0).trans reverse.a_gain_first
    a_gain_other := fun q hq0 hq2 => (hA q).trans (reverse.a_gain_other q hq0 hq2)
    b_gain_target := (hB 2).trans reverse.b_gain_target
    b_gain_first := (hB 1).trans reverse.b_gain_first
    b_gain_other := fun q hq1 hq2 => (hB q).trans (reverse.b_gain_other q hq1 hq2)
    c_gain_target := teaching.c_gain_target, c_gain_other := teaching.c_gain_other
    a_recovery := hRecA.trans reverse.a_recovery, b_recovery := hRecB.trans reverse.b_recovery
    c_recovery := teaching.c_recovery
    physical := lifted.physical_invariant hb birth.physical
    raw_valid := lifted.raw_valid birth.raw_valid, complete := hComplete
  }⟩
  · rw [hBefore,hAfter0,reverse.a_emission_count]
    norm_num
  · rw [hBefore,hAfterB,reverse.b_emission_count]
    norm_num

namespace ConstructedCTeaching
variable {θ born freshB freshC newbornB newbornC forward backward delay}
  (c : ConstructedCTeaching θ born freshB freshC newbornB newbornC forward backward delay)

theorem pending_length : c.final.pending.length = 25 := by
  rw [c.pending]
  simp only [sourceTrain,List.length_ofFn]

theorem ready (i : Fin 3) : c.final.main i = .ready := (c.prepared i).ready

end ConstructedCTeaching
end KernelR.Hybrid
