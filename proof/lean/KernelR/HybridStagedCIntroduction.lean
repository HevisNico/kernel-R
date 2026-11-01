import KernelR.HybridCIntroductionBoundary
import KernelR.HybridCIntroductionBoundaryPhase
import KernelR.HybridBirthQueueBridge
import KernelR.HybridCIntroductionQueueClosure
/-! Actual C introduction at 480 and physical B-to-C teaching through 639.9. -/
namespace KernelR.Hybrid

structure StagedCIntroduction {θ fresh s u} (forward backward delay : ℝ → ℝ)
    (e : @StagedExecution 2 θ fresh (reciprocalEntryRouter forward backward) (cTeachingRouter delay) s u) where
  boundary : CIntroductionBoundary e.before
  phase : CIntroductionActivePhase e.after
  queues : CIntroductionQueueClosure e.after
  c_sources : (u.pending.filter (fun d => d.cell = 2)).Perm e.birth.sources
  a_emissions : (e.before.emissionTimes 0).length + (e.after.emissionTimes 0).length = 0
  b_emissions : (e.before.emissionTimes 1).length + (e.after.emissionTimes 1).length = 16
  c_emissions : (e.after.emissionTimes 2).length = 14
  gain_a : ∀ p, u.x 0 (.z p) = s.x 0 (.z p)
  gain_b : ∀ p, u.x 1 (.z p) = s.x 1 (.z p)
  recovery_a : u.x 0 .b = s.x 0 .b
  recovery_b : u.x 1 .b = s.x 1 .b
  gain_c_target : u.x 2 (.z 1) = e.birth.newborn.x (.z 1) + 3 / 5
  gain_c_other : ∀ p, p ≠ 1 → u.x 2 (.z p) = e.birth.newborn.x (.z p)
  recovery_c : u.x 2 .b = e.birth.newborn.x .b + 1 / 10
  a_raw : ∀ p, u.raw 0 p = none
  physical : PhysicalInvariant (extendParameters θ fresh) u
  raw_valid : RawValid u
  pending_future : PendingFuture u

/-- Starting from actual reciprocal-entry states at 459.9, the same old cells
reach C's birth at 480 and teach it through 639.9. Source 480 may be pending or
already active at birth; neither alternative resets coordinates or memories.
All executions and the birth event are supplied, not asserted to exist. -/
theorem StagedExecution.c_introduction {θ fresh ε s u} (forward backward delay : ℝ → ℝ)
    (e : @StagedExecution 2 θ fresh (reciprocalEntryRouter forward backward) (cTeachingRouter delay) s u)
    (hb : PhysicalBox (extendParameters θ fresh) ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hsA : PreparedSection s 0) (hqA : s.x 0 .q = 1 / 10) (hrA : ∀ p, s.raw 0 p = none)
    (hsB : PreparedSection s 1) (hqB : s.x 1 .q = 1 / 10) (hrB : ∀ p, s.raw 1 p = none)
    (hzB : 9 / 5 ≤ Real.exp (s.x 1 (.z 2)) ∧ Real.exp (s.x 1 (.z 2)) ≤ 12 / 5)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16))
    (ht : s.time = 4599 / 10) (hbirth : e.beforeBirth.time = 480) (hend : u.time = 6399 / 10)
    (hsources : ∀ d ∈ e.birth.sources, 640 ≤ d.due) (hpf : PendingFuture s)
    (hforward : ∀ t, 0 ≤ forward t) (hbackward : ∀ t, 0 ≤ backward t)
    (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5) :
    Nonempty (StagedCIntroduction forward backward delay e) := by
  obtain ⟨boundary⟩ := e.before.c_introduction_boundary forward backward hsA hqA hrA hsB hqB hrB
    hAempty hBqueue ht hbirth hpf hforward hbackward
  have hcastA : (0 : Fin 2).castSucc = (0 : Fin 3) := by decide
  have hcastB : (1 : Fin 2).castSucc = (1 : Fin 3) := by decide
  have hlast : Fin.last 2 = (2 : Fin 3) := by decide
  have birthA : e.afterBirth.x 0 = e.beforeBirth.x 0 := by
    simpa only [hcastA] using e.birth.old_coordinates (0 : Fin 2)
  have birthB : e.afterBirth.x 1 = e.beforeBirth.x 1 := by
    simpa only [hcastB] using e.birth.old_coordinates (1 : Fin 2)
  have birthC : e.afterBirth.x 2 = e.birth.newborn.x := by
    simpa only [hlast] using e.birth.new_coordinates
  have rawBirthA : e.afterBirth.raw 0 = e.beforeBirth.raw 0 := by
    simpa only [hcastA] using e.birth.old_raw (0 : Fin 2)
  have rawBirthB : e.afterBirth.raw 1 = e.beforeBirth.raw 1 := by
    simpa only [hcastB] using e.birth.old_raw (1 : Fin 2)
  have hiafter : PhysicalInvariant (extendParameters θ fresh) e.afterBirth :=
    e.birth.physical_invariant hb (e.before.physical_invariant hb.extend_old hf)
  have hvafter : RawValid e.afterBirth := e.birth.raw_valid (e.before.raw_valid hv)
  have hafterTime : e.afterBirth.time = 480 := e.birth.time_unchanged.trans hbirth
  have hafterA : PreparedSection e.afterBirth 0 := by
    simpa only [hcastA] using e.birth.old_prepared (0 : Fin 2) boundary.a_idle.prepared
  have hafterB : PreparedSection e.afterBirth 1 := by
    simpa only [hcastB] using e.birth.old_prepared (1 : Fin 2) boundary.b_idle.prepared
  have hqafterA : e.afterBirth.x 0 .q = 1 / 10 := by
    rw [birthA]
    exact boundary.a_idle.charge_rest
  have hqafterB : e.afterBirth.x 1 .q = 1 / 10 := by
    rw [birthB]
    exact boundary.b_idle.charge_rest
  have hrafterA : ∀ p, e.afterBirth.raw 0 p = none := by
    intro p
    rw [rawBirthA]
    exact boundary.a_raw p
  have hrafterBOther : ∀ p, p ≠ 2 → e.afterBirth.raw 1 p = none := by
    intro p hp
    rw [rawBirthB]
    exact boundary.b_raw_other p hp
  have hga : ∀ p, e.afterBirth.x 0 (.z p) = s.x 0 (.z p) := by
    intro p
    rw [birthA,boundary.a_idle.gain_preserved p]
  have hgb : ∀ p, e.afterBirth.x 1 (.z p) = s.x 1 (.z p) := by
    intro p
    rw [birthB,boundary.b_idle.gain_preserved p]
  have hzbafter : 9 / 5 ≤ Real.exp (e.afterBirth.x 1 (.z 2)) ∧
      Real.exp (e.afterBirth.x 1 (.z 2)) ≤ 12 / 5 := by rw [hgb 2]; exact hzB
  have hAqueue : e.afterBirth.pending.filter (fun d => d.cell = 0) = [] := by
    change e.afterBirth.pending.filter (fun d => d.cell = (0 : Fin 2).castSucc) = []
    rw [e.birth.old_cell_pending (0 : Fin 2),boundary.a_queue,List.map_nil]
  have lift_queue : ∀ (start : ℝ) (count : ℕ),
      (e.beforeBirth.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 start 8 count) →
      (e.afterBirth.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 start 8 count) := by
    intro start count hqueue
    change (e.afterBirth.pending.filter (fun d => d.cell = (1 : Fin 2).castSucc)).Perm
      (sourceTrain (1 : Fin 3) 2 start 8 count)
    rw [e.birth.old_cell_pending (1 : Fin 2)]
    have h := hqueue.map liftDelivery
    simpa only [sourceTrain,List.map_ofFn,Function.comp_def,liftDelivery,hcastB] using h
  have hboundary :
      (e.afterBirth.raw 1 2 = none ∧ (e.afterBirth.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 480 8 16)) ∨
      (e.afterBirth.raw 1 2 = some e.afterBirth.time ∧
        (e.afterBirth.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 488 8 15)) := by
    rcases boundary.b_boundary with ⟨hraw,hqueue⟩ | ⟨hraw,hqueue⟩
    · left
      refine ⟨?_,lift_queue 480 16 hqueue⟩
      rw [rawBirthB]
      exact hraw
    · right
      refine ⟨?_,lift_queue 488 15 hqueue⟩
      rw [rawBirthB,e.birth.time_unchanged]
      exact hraw
  have hsc : ReadyCoordinates e.afterBirth 2 := by simpa only [hlast] using e.birth.new_ready
  have hbc : 7999 / 100000 ≤ e.afterBirth.x 2 .b ∧ e.afterBirth.x 2 .b ≤ 8001 / 100000 := by
    simpa only [hlast] using e.birth.new_recovery
  have hzc : Real.log (6 / 5) - 1 / 1000 ≤ e.afterBirth.x 2 (.z 1) ∧
      e.afterBirth.x 2 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000 := by
    have h := e.birth.new_gain (1 : Port)
    simp [nominalGain,hlast] at h
    constructor <;> linarith [h.1,h.2]
  have hrc : ∀ p, e.afterBirth.raw 2 p = none := by simpa only [hlast] using e.birth.new_raw
  have hfuture : ∀ d ∈ e.afterBirth.pending, d.cell = 2 → 640 ≤ d.due := by
    intro d hd hc
    have hm : d ∈ e.afterBirth.pending.filter (fun d => d.cell = Fin.last 2) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,by simpa only [hlast] using hc⟩
    rw [e.birth.new_cell_pending] at hm
    exact hsources d hm
  have hafterCausal : CausalRouter (cTeachingRouter delay) :=
    cTeachingRouter.causal delay (fun t => by linarith [(hdelay t).1])
  have hterminal : PendingFuture u := e.pending_future
    (reciprocalEntryRouter.causal forward backward hforward hbackward) hafterCausal hpf
  obtain ⟨phase⟩ := e.after.c_introduction_boundary_phase delay hb hiafter hvafter
    hafterA hqafterA hrafterA hAqueue hafterB hqafterB hzbafter hboundary hrafterBOther
    hafterTime hend hterminal hsc hbc hzc hrc hfuture hdelay
  have hnoA : ∀ p, NoArrivalAt e.after 0 p := by
    apply e.after.no_arrival_before_due 0
    · intro d hd hc
      have hm : d ∈ e.afterBirth.pending.filter (fun d => d.cell = 0) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hd,hc⟩
      rw [hAqueue] at hm
      contradiction
    · intro event he d hd hc
      exact False.elim (cTeachingRouter.closed_to_a delay event.1 event.2 d hd hc)
  have rawA : ∀ p, u.raw 0 p = none :=
    fun p => (e.after.raw_absent_of_no_arrival 0 p (hrafterA p) (hnoA p)).1
  have hBpast : ∀ d ∈ e.afterBirth.pending, d.cell = 1 → d.due < u.time := by
    intro d hd hc
    have hm : d ∈ e.afterBirth.pending.filter (fun d => d.cell = 1) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,hc⟩
    rcases hboundary with ⟨_,hqueue⟩ | ⟨_,hqueue⟩
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (hqueue.mem_iff.mp hm)
      have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
      rw [hend]
      change 480 + 8 * (k.val : ℝ) < 6399 / 10
      linarith
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (hqueue.mem_iff.mp hm)
      have hk : (k.val : ℝ) ≤ 14 := by exact_mod_cast (show k.val ≤ 14 by omega)
      rw [hend]
      change 488 + 8 * (k.val : ℝ) < 6399 / 10
      linarith
  have hCfuture : ∀ d ∈ e.afterBirth.pending, d.cell = 2 → u.time < d.due := by
    intro d hd hc
    rw [hend]
    linarith [hfuture d hd hc]
  have queues := e.after.c_introduction_queue_closure delay hterminal hend hAqueue hBpast hCfuture
    (fun t => (hdelay t).2)
  have c_sources : (u.pending.filter (fun d => d.cell = 2)).Perm e.birth.sources := by
    have h := queues.c_sources
    change (u.pending.filter (fun d => d.cell = 2)).Perm
      (e.afterBirth.pending.filter (fun d => d.cell = Fin.last 2)) at h
    rw [e.birth.new_cell_pending] at h
    exact h
  refine ⟨⟨boundary,phase,queues,c_sources,?_,?_,phase.c_phase.emissions,?_,?_,?_,?_,?_,?_,?_,rawA,
    e.physical_invariant hb hf,e.raw_valid hv,hterminal⟩⟩
  · rw [boundary.a_idle.emissions,phase.a_idle.emissions]
    rfl
  · rw [boundary.b_idle.emissions,List.length_nil,zero_add]
    exact phase.b_train.emissions
  · intro p
    rw [phase.a_idle.gain_preserved p,hga p]
  · intro p
    rw [phase.b_train.gain_preserved p,hgb p]
  · rw [phase.a_idle.recovery_preserved,birthA,boundary.a_idle.recovery_preserved]
  · rw [phase.b_train.recovery_preserved,birthB,boundary.b_idle.recovery_preserved]
  · rw [phase.c_phase.gain_target,birthC]
  · intro p hp
    rw [phase.c_phase.gain_other p hp,birthC]
  · rw [phase.c_phase.recovery_gain,birthC]

end KernelR.Hybrid
