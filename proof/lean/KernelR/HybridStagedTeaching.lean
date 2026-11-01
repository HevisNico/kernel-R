import KernelR.HybridBirthQueueBridge
import KernelR.HybridTeachingBoundaryPhase
import KernelR.HybridEntryRouter
/-! The first two physical source epochs across the actual birth of B at 160. -/
namespace KernelR.Hybrid

structure StagedTeaching {θ fresh routeBefore routeAfter born u}
    (e : @StagedExecution 1 θ fresh routeBefore routeAfter born u) where
  preparation : StagedPreparation e 0 0
  teaching : TeachingActivePhase e.after
  a_emissions : (e.before.emissionTimes 0).length + (e.after.emissionTimes 0).length = 28
  b_emissions : (e.after.emissionTimes 1).length = 14
  gain_a_target : u.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5
  gain_a_other : ∀ p, p ≠ 0 → u.x 0 (.z p) = born.x 0 (.z p)
  gain_b_target : u.x 1 (.z 1) = e.birth.newborn.x (.z 1) + 3 / 5
  gain_b_other : ∀ p, p ≠ 1 → u.x 1 (.z p) = e.birth.newborn.x (.z p)
  recovery_a : u.x 0 .b = born.x 0 .b + 1 / 10
  recovery_b : u.x 1 .b = e.birth.newborn.x .b + 1 / 10
  error_a : e.before.ledger.error 0 0 + e.after.ledger.error 0 0 = 9 / 5
  mark_a : e.before.ledger.mark 0 0 + e.after.ledger.mark 0 0 = 1 / 10

/-- From the complete initial A source queue and a genuine fresh B birth,
derive both teaching counts and final prepared memories. No receiving calendar,
phase word, inherited B learning or event-priority premise is supplied. -/
theorem StagedExecution.teaching_epoch {θ fresh ε routeBefore routeAfter born u}
    (e : @StagedExecution 1 θ fresh routeBefore routeAfter born u)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hbirth : e.beforeBirth.time = 160) (hend : u.time = 3199 / 10)
    (hsources : ∀ d ∈ e.birth.sources, 320 ≤ d.due)
    (hcausal : CausalRouter routeAfter)
    (hclosed : ∀ event ∈ e.after.ledger.emissions, ∀ d ∈ routeAfter event.1 event.2, d.cell ≠ 0)
    (delay : ℝ → ℝ) (hdelay : ∀ t, 3 / 10 ≤ delay t ∧ delay t ≤ 2 / 5)
    (hwire : ∀ event ∈ e.after.ledger.emissions,
      (routeAfter event.1 event.2).filter (fun d => d.cell = 1) = (teachingContact delay).route event.1 event.2) :
    Nonempty (StagedTeaching e) := by
  obtain ⟨prep⟩ := e.preparation_at_birth hborn hb.extend_old 0 0 (by decide) ha hqueue hbefore hbirth
  have hcast : (0 : Fin 1).castSucc = (0 : Fin 2) := by decide
  have hlast : Fin.last 1 = (1 : Fin 2) := by decide
  have hagain : e.afterBirth.x 0 (.z 0) = born.x 0 (.z 0) + 9 / 5 := by
    simpa only [hcast] using prep.gain_target
  have haother : ∀ p, p ≠ 0 → e.afterBirth.x 0 (.z p) = born.x 0 (.z p) := by
    intro p hp
    simpa only [hcast] using prep.gain_other p hp
  have harecovery : e.afterBirth.x 0 .b = born.x 0 .b + 1 / 10 := by
    simpa only [hcast] using prep.recovery_gain
  have hnewx : e.afterBirth.x (1 : Fin 2) = e.birth.newborn.x := by
    simpa only [hlast] using e.birth.new_coordinates
  have hboundary := e.source_queue_at_birth hborn hb.extend_old 0 0 (by decide) ha hqueue hbefore hbirth
  have hinitial : PendingFuture born := by
    intro d hd
    rw [hqueue] at hd
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    all_goals obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; dsimp; positivity
  have hbeforeCausal : CausalRouter routeBefore := by simp [CausalRouter,hbefore]
  have hpf : PendingFuture u := e.pending_future hbeforeCausal hcausal hinitial
  have hfi := e.birth.physical_invariant hb (e.before.physical_invariant hb.extend_old (hborn.physical_invariant hb.extend_old))
  have hvalid := e.birth.raw_valid (e.before.raw_valid hborn.raw_valid)
  have hzbase : Real.log (3 / 10) - 1 / 100000 ≤ born.x 0 (.z 0) ∧
      born.x 0 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000 := by
    simpa [nominalGain] using ((hborn.2.2 0).2.2.2.2 0).1
  have hzband : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ e.afterBirth.x 0 (.z 0) ∧
      e.afterBirth.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [hagain]
    constructor <;> linarith [hzbase.1,hzbase.2]
  have hza : 9 / 5 ≤ Real.exp (e.afterBirth.x 0 (.z 0)) ∧
      Real.exp (e.afterBirth.x 0 (.z 0)) ≤ 12 / 5 := by
    have h := learned_gain_bounds hzband.1 hzband.2
    exact ⟨h.1,by linarith [h.2]⟩
  have hsb : ReadyCoordinates e.afterBirth 1 := e.birth.new_ready
  have hbb : 7999 / 100000 ≤ e.afterBirth.x 1 .b ∧ e.afterBirth.x 1 .b ≤ 8001 / 100000 := e.birth.new_recovery
  have hzb : Real.log (6 / 5) - 1 / 1000 ≤ e.afterBirth.x 1 (.z 1) ∧
      e.afterBirth.x 1 (.z 1) ≤ Real.log (6 / 5) + 1 / 1000 := by
    have h := e.birth.new_gain (1 : Port)
    simp [nominalGain,hlast] at h
    constructor <;> linarith [h.1,h.2]
  have hfuture : ∀ d ∈ e.afterBirth.pending, d.cell = 1 → 320 ≤ d.due := by
    intro d hd hc
    rw [e.birth.pending] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hd
      exact False.elim ((ne_of_lt old.cell.castSucc_lt_last) hc)
    · exact hsources d hd
  obtain ⟨phase⟩ := e.after.teaching_boundary_phase hb hfi hvalid prep.prepared prep.charge_rest hza
    hboundary prep.raw_other hclosed prep.date hend hpf hsb hbb hzb e.birth.new_raw hfuture delay hdelay hwire
  refine ⟨⟨prep,phase,?_,phase.b_phase.emissions,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [prep.first_phase.emissions,phase.a_train.emissions]
  · rw [phase.a_train.gain_preserved,hagain]
  · intro p hp
    rw [phase.a_train.gain_preserved,haother p hp]
  · rw [phase.b_phase.gain_target,hnewx]
  · intro p hp
    rw [phase.b_phase.gain_other p hp,hnewx]
  · rw [phase.a_train.recovery_preserved,harecovery]
  · rw [phase.b_phase.recovery_gain,hnewx]
  · rw [prep.first_phase.error_target,phase.a_train.error_zero]
    ring
  · rw [prep.first_phase.mark_target,phase.a_train.mark_zero]
    ring

/-- The declared [160,310) forward and [320,470) return contacts discharge all
teaching routing premises, using actual emission-time bounds. Existence of the
supplied phase executions remains a separate obligation. -/
theorem StagedExecution.reciprocal_teaching_epoch {θ fresh ε routeBefore born u}
    (forward backward : ℝ → ℝ)
    (e : @StagedExecution 1 θ fresh routeBefore (reciprocalEntryRouter forward backward) born u)
    (hborn : BirthState born) (hb : PhysicalBox (extendParameters θ fresh) ε)
    (ha : ∀ p, born.aux 0 p = .ready)
    (hqueue : born.pending = sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16)
    (hbefore : ∀ i t, routeBefore i t = [])
    (hbirth : e.beforeBirth.time = 160) (hend : u.time = 3199 / 10)
    (hsources : ∀ d ∈ e.birth.sources, 320 ≤ d.due)
    (hforward : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hbackward : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    Nonempty (StagedTeaching e) := by
  have htime : ∀ event ∈ e.after.ledger.emissions, event.2 < 320 := by
    intro event he
    have h := (e.after.emission_time_bounds event he).2
    rw [hend] at h
    linarith
  apply e.teaching_epoch hborn hb ha hqueue hbefore hbirth hend hsources
    (reciprocalEntryRouter.causal forward backward (fun t => by linarith [(hforward t).1])
      (fun t => by linarith [(hbackward t).1]))
    (fun event he => reciprocalEntryRouter.closed_to_a forward backward event.1 (htime event he))
    forward hforward
    (fun event he => reciprocalEntryRouter.to_b forward backward event.1 (htime event he))

end KernelR.Hybrid
